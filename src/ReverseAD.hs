{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

-- | Reverse-AD functions
--
-- Given the following term:
--   Γ |- t : τ
-- We produce this term:
--   Dr₁[Γ] |- Dr[t] : (Dr₁[τ] * (Dr₂[τ] -o Dr₂[Γ]))
module ReverseAD where

import           Operation          (LinearOperation (..), Operation (..))
import           SourceLanguage     as SL
import           TargetLanguage     as TL
import           Env
import           Types              (LT, LTU, Dr1, Dr2, LFun)

type family Dr1Env env where
  Dr1Env '[] = '[]
  Dr1Env (t ': env) = Dr1 t ': Dr1Env env

type family Dr2Env env where
  Dr2Env '[] = ()
  Dr2Env (t ': env) = (Dr2Env env, Dr2 t)

cvtDr1EnvIdx :: Idx env t -> Idx (Dr1Env env) (Dr1 t)
cvtDr1EnvIdx Z = Z
cvtDr1EnvIdx (S i) = S (cvtDr1EnvIdx i)

onehotEnv :: (LTenv lenv, LTU (Dr2Env env), LT (Dr2 t)) => Idx env t -> LinTTerm env' (Dr2 t ': lenv) (Dr2Env env)
onehotEnv Z = LinPair LinZero (LinVar Z)
onehotEnv (S i) = LinPair (onehotEnv i) LinZero

drOp :: Operation a b -> TTerm env (a -> LFun (Dr2 b) (Dr2 a))
drOp (Constant _) = Lambda Zero
drOp EAdd = Lambda $ LinFun $ LinPair (LinVar Z) (LinVar Z)
drOp EProd = Lambda $ LinFun $ LinPair (LinLOp LProd (Snd (Var Z)) (LinVar Z))
                                       (LinLOp LProd (Fst (Var Z)) (LinVar Z))
drOp EScalAdd = Lambda $ LinFun $ LinPair (LinVar Z) (LinVar Z)
drOp EScalSubt = Lambda $ LinFun $ LinPair (LinVar Z) (LinLOp LScalNeg Unit (LinVar Z))
drOp EScalProd = Lambda $ LinFun $ LinPair (LinLOp LScalProd (Snd (Var Z)) (LinVar Z))
                                           (LinLOp LScalProd (Fst (Var Z)) (LinVar Z))
drOp EScalSin = Lambda $ LinFun $ LinLOp LScalProd (Op EScalCos (Var Z)) (LinVar Z)
drOp EScalCos = Lambda $ LinFun $ LinLOp LScalProd (neg (Op EScalSin (Var Z))) (LinVar Z)
  where neg x = Op EScalSubt (Pair (Op (Constant 0.0) Unit) x)

dr :: LTU (Dr2Env env) => STerm env t -> TTerm (Dr1Env env) (Dr1 t, LFun (Dr2 t) (Dr2Env env))
dr = \case
  SVar idx ->
    Pair (Var (cvtDr1EnvIdx idx))
         (LinFun (onehotEnv idx))

  SLambda body ->
    Let (Lambda $ dr body) $
      Pair (Lambda $
              Let (Var (S Z) `App` Var Z) $
                Pair (Fst (Var Z))
                     (LinFun $ LinSnd (Snd (Var Z) `LinApp` LinVar Z)))
           (LinFun $
              LinCopowFold
                  (Lambda $ LinFun $
                     LinFst (Snd (Var (S Z) `App` Var Z) `LinApp` LinVar Z))
                  (LinVar Z))

  SLet rhs body ->
    Let (dr rhs) $
    Let (substTt (wSucc wId) (Fst (Var Z)) (dr body)) $
      Pair (Fst (Var Z))
           (LinFun $
              LinLet (Snd (Var Z) `LinApp` LinVar Z)
                     (LinPlus (LinFst (LinVar Z))
                              (Snd (Var (S Z)) `LinApp` LinSnd (LinVar Z))))

  SApp fun arg ->
    Let (dr arg) $
    Let (sinkTt1 (dr fun)) $
    Let (App (Fst (Var Z)) (Fst (Var (S Z)))) $
      Pair (Fst (Var Z))
           (LinFun $
              LinPlus (Snd (Var (S (S Z)))
                         `LinApp` (Snd (Var Z) `LinApp` LinVar Z))
                      (Snd (Var (S Z))
                         `LinApp` LinSingleton (Fst (Var (S (S Z)))) (LinVar Z)))

  SUnit -> Pair Unit Zero

  SPair e1 e2 ->
    Let (dr e1) $
    Let (sinkTt1 (dr e2)) $
      Pair (Pair (Fst (Var (S Z))) (Fst (Var Z)))
           (LinFun $
              LinPlus (Snd (Var (S Z)) `LinApp` LinFst (LinVar Z))
                      (Snd (Var Z    ) `LinApp` LinSnd (LinVar Z)))

  SFst e ->
    Let (dr e) $
      Pair (Fst (Fst (Var Z)))
           (LinFun $ Snd (Var Z) `LinApp` LinPair (LinVar Z) LinZero)

  SSnd e ->
    Let (dr e) $
      Pair (Snd (Fst (Var Z)))
           (LinFun $ Snd (Var Z) `LinApp` LinPair LinZero (LinVar Z))

  SOp op arg ->
    Let (dr arg) $
      Pair (Op op (Fst (Var Z)))
           (LinFun $
              let dop = drOp op `App` Fst (Var Z)
              in Snd (Var Z) `LinApp` (dop `LinApp` LinVar Z))

  SMap f e ->
    Let (dr f) $
    Let (sinkTt1 (dr e)) $
      Pair (Map (Lambda $ Fst (Fst (Var (S (S Z))) `App` Var Z)) (Fst (Var Z)))
           (LinFun $
              LinPlus (Snd (Var (S Z)) `LinApp` LinZip (Fst (Var Z)) (LinVar Z))
                      (Snd (Var Z) `LinApp`
                         LinZipWith (Lambda $ LinFun $
                                       Snd (Fst (Var (S (S Z))) `App` Var Z)
                                         `LinApp` LinVar Z)
                                    (Fst (Var Z)) (LinVar Z)))

  SReplicate e ->
    Let (dr e) $
      Pair (Replicate (Fst (Var Z)))
           (LinFun $ Snd (Var Z) `LinApp` LinSum (LinVar Z))

  SSum e ->
    Let (dr e) $
      Pair (Sum (Fst (Var Z)))
           (LinFun $ Snd (Var Z) `LinApp` LinReplicate (LinVar Z))
