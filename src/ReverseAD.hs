{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

-- | Reverse-AD functions
module ReverseAD where

import           Operation          (LinearOperation' (..), Operation (..))
import           SourceLanguage     as SL
import           TargetLanguage     as TL
import           Env
import           Types              (LT, Dr1, Dr2, LFun)

type family Dr1Env env where
  Dr1Env '[] = '[]
  Dr1Env (t ': env) = Dr1 t ': Dr1Env env

type family Dr2Env env where
  Dr2Env '[] = ()
  Dr2Env (t ': env) = (Dr2Env env, Dr2 t)

cvtDr1EnvIdx :: Idx env t -> Idx (Dr1Env env) (Dr1 t)
cvtDr1EnvIdx Z = Z
cvtDr1EnvIdx (S i) = S (cvtDr1EnvIdx i)

onehotEnv :: (LT (Dr2Env env), LT (Dr2 t)) => Idx env t -> LinTTerm env' (Dr2 t) (Dr2Env env)
onehotEnv Z = LinPair LinZero LinVar
onehotEnv (S i) = LinPair (onehotEnv i) LinZero

drOp :: a ~ Dr1 a => Operation a b -> TTerm env (a -> LFun (Dr2 b) (Dr2 a))
drOp (Constant _) = Lambda Zero
drOp EAdd = Lambda $ LinFun $ LinPair LinVar LinVar
drOp EProd = Lambda $ LinFun $ LinPair (LinLOp LProd (Snd (Var Z)) LinVar)
                                       (LinLOp LProd (Fst (Var Z)) LinVar)
drOp EScalAdd = Lambda $ LinFun $ LinPair LinVar LinVar
drOp EScalSubt = Lambda $ LinFun $ LinPair LinVar (LinLOp LScalNeg Unit LinVar)
drOp EScalProd = Lambda $ LinFun $ LinPair (LinLOp LScalProd (Snd (Var Z)) LinVar)
                                           (LinLOp LScalProd (Fst (Var Z)) LinVar)
drOp EScalSin = Lambda $ LinFun $ LinLOp LScalProd (Op EScalCos (Var Z)) LinVar
drOp EScalCos = Lambda $ LinFun $ LinLOp LScalProd (neg (Op EScalSin (Var Z))) LinVar
  where neg x = Op EScalSubt (Pair (Op (Constant 0.0) Unit) x)
drOp Sum = Lambda $ LinFun $ LinLOp LReplicate Unit LinVar

dr :: LT (Dr2Env env) => STerm env t -> TTerm (Dr1Env env) (Dr1 t, LFun (Dr2 t) (Dr2Env env))
dr = \case
  SVar idx ->
    Pair (Var (cvtDr1EnvIdx idx))
         (LinFun (onehotEnv idx))

  SLambda body ->
    Let (Lambda $ dr body) $
      Pair (Lambda $
              Let (Var (S Z) `App` Var Z) $
                Pair (Fst (Var Z))
                     (LinFun $
                        LinSnd (Snd (Var Z) `LinApp` LinVar)))
           (LinFun $
              LinCopowFold
                  (Lambda $ LinFun $
                     LinFst (Snd (Var (S Z) `App` Var Z)
                               `LinApp` LinVar))
                  LinVar)

  SLet rhs body ->
    Let (dr rhs) $
    Let (substTt (wSucc wId) (Fst (Var Z)) (dr body)) $
      Pair (Fst (Var Z))
           (LinFun $
              LinLet (Snd (Var Z) `LinApp` LinVar)
                     (LinPlus (LinFst LinVar)
                              (Snd (Var (S Z)) `LinApp` LinSnd LinVar)))

  SApp fun arg ->
    Let (dr arg) $
    Let (sinkTt (wSucc wId) (dr fun)) $
    Let (App (Fst (Var Z)) (Fst (Var (S Z)))) $
      Pair (Fst (Var Z))
           (LinFun $
              LinPlus (Snd (Var (S (S Z)))
                         `LinApp` (Snd (Var Z) `LinApp` LinVar))
                      (Snd (Var (S Z))
                         `LinApp` LinSingleton (Fst (Var (S (S Z)))) LinVar))

  SUnit -> Pair Unit Zero

  SPair e1 e2 ->
    Let (dr e1) $
    Let (sinkTt (wSucc wId) (dr e2)) $
      Pair (Pair (Fst (Var (S Z))) (Fst (Var Z)))
           (LinFun $
              LinPlus (Snd (Var (S Z)) `LinApp` LinFst LinVar)
                      (Snd (Var Z    ) `LinApp` LinSnd LinVar))

  SFst e ->
    Let (dr e) $
      Pair (Fst (Fst (Var Z)))
           (LinFun $
              Snd (Var Z)
                `LinApp` LinPair LinVar LinZero)

  SSnd e ->
    Let (dr e) $
      Pair (Snd (Fst (Var Z)))
           (LinFun $
              Snd (Var Z)
                `LinApp` LinPair LinZero LinVar)

  SOp op arg ->
    Let (dr arg) $
      Pair (Op op (Fst (Var Z)))
           (LinFun $
              let dop = drOp op `App` Fst (Var Z)
              in Snd (Var Z) `LinApp` (dop `LinApp` LinVar))

  _ -> undefined
