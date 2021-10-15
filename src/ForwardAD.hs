{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

-- | Forward-AD Functions
--
-- Given the following term:
--
-- > Γ |- t : τ
--
-- We produce this term:
--
-- > Df₁[Γ] |- Df[t] : (Df₁[τ] * (Df₂[Γ] -o Df₂[τ]))
module ForwardAD (
  df, dfOp,
  Df1Env, Df2Env,
) where

import           Operation          (LinearOperation (..), Operation (..))
import           SourceLanguage
import           TargetLanguage
import           Env
import           Types              (LT, LTU, UnLin, Df1, Df2, LFun)

type family Df1Env env where
  Df1Env '[] = '[]
  Df1Env (t ': env) = Df1 t ': Df1Env env

type family Df2Env env where
  Df2Env '[] = ()
  Df2Env (t ': env) = (Df2Env env, Df2 t)

cvtDf1EnvIdx :: Idx env t -> Idx (Df1Env env) (Df1 t)
cvtDf1EnvIdx Z = Z
cvtDf1EnvIdx (S i) = S (cvtDf1EnvIdx i)

linPrj :: (LTenv lenv, LT (Df2Env env))
       => Idx env t -> LinTTerm env' lenv (Df2Env env) -> LinTTerm env' lenv (Df2 t)
linPrj Z env = LinSnd env
linPrj (S i) env = linPrj i (LinFst env)

dfOp :: LT (UnLin (Df2 b)) => Operation a b -> TTerm env (a -> LFun (Df2 a) (Df2 b))
dfOp (Constant _) = Lambda (LinFun LinZero)
dfOp EAdd = Lambda $ LinFun $ LinPlus (LinFst (LinVar Z)) (LinSnd (LinVar Z))
dfOp EProd = Lambda $ LinFun $ LinPlus (LinLOp LProd (Fst (Var Z)) (LinSnd (LinVar Z)))
                                       (LinLOp LProd (Snd (Var Z)) (LinFst (LinVar Z)))
dfOp EScalAdd = Lambda $ LinFun $ LinPlus (LinFst (LinVar Z)) (LinSnd (LinVar Z))
dfOp EScalSubt = Lambda $ LinFun $ LinPlus (LinFst (LinVar Z)) (LinLOp LScalNeg Unit (LinSnd (LinVar Z)))
dfOp EScalProd = Lambda $ LinFun $ LinPlus (LinLOp LScalProd (Fst (Var Z)) (LinSnd (LinVar Z)))
                                           (LinLOp LScalProd (Snd (Var Z)) (LinFst (LinVar Z)))
dfOp EScalSin = Lambda $ LinFun $ LinLOp LScalProd (Op EScalCos (Var Z)) (LinVar Z)
dfOp EScalCos = Lambda $ LinFun $ LinLOp LScalProd (neg (Op EScalSin (Var Z))) (LinVar Z)
  where neg x = Op EScalSubt (Pair (Op (Constant 0.0) Unit) x)

df :: LTU (Df2Env env) => STerm env t -> TTerm (Df1Env env) (Df1 t, LFun (Df2Env env) (Df2 t))
df = \case
  SVar i ->
    Pair (Var (cvtDf1EnvIdx i))
         (LinFun (linPrj i (LinVar Z)))

  SLambda body ->
    Let (Lambda $ df body) $
      Pair (Lambda $
              Let (Var (S Z) `App` Var Z) $
                Pair (Fst (Var Z))
                     (LinFun $ Snd (Var Z) `LinApp` LinPair LinZero (LinVar Z)))
           (LinFun $ LinLam $
              Snd (Var (S Z) `App` Var Z) `LinApp` LinPair (LinVar Z) LinZero)

  SLet rhs body ->
    Let (df rhs) $
    Let (substTt (wSucc wId) (Fst (Var Z)) (df body)) $
      Pair (Fst (Var Z))
           (LinFun $
              Snd (Var Z) `LinApp` LinPair (LinVar Z)
                                           (Snd (Var (S Z)) `LinApp` LinVar Z))

  SApp fun arg ->
    Let (df arg) $
    Let (sinkTt1 (df fun)) $
    Let (Fst (Var Z) `App` Fst (Var (S Z))) $
      Pair (Fst (Var Z))
           (LinFun $
              LinPlus ((Snd (Var (S Z)) `LinApp` LinVar Z) `LinApp'` Fst (Var (S (S Z))))
                      (Snd (Var Z) `LinApp` (Snd (Var (S (S Z))) `LinApp` LinVar Z)))

  SUnit -> Pair Unit (LinFun LinZero)

  SPair e1 e2 ->
    Let (df e1) $
    Let (sinkTt1 (df e2)) $
      Pair (Pair (Fst (Var (S Z))) (Fst (Var Z)))
           (LinFun $
              LinPair (Snd (Var (S Z)) `LinApp` LinVar Z)
                      (Snd (Var Z    ) `LinApp` LinVar Z))

  SFst e ->
    Let (df e) $
      Pair (Fst (Fst (Var Z)))
           (LinFun $ LinFst (Snd (Var Z) `LinApp` LinVar Z))

  SSnd e ->
    Let (df e) $
      Pair (Snd (Fst (Var Z)))
           (LinFun $ LinSnd (Snd (Var Z) `LinApp` LinVar Z))

  SOp op arg ->
    Let (df arg) $
      Pair (Op op (Fst (Var Z)))
           (LinFun $
              (dfOp op `App` Fst (Var Z))
                `LinApp` (Snd (Var Z) `LinApp` LinVar Z))

  SMap f e ->
    Let (df f) $
    Let (sinkTt1 (df e)) $
      Pair (Map (Lambda $ Fst (Fst (Var (S (S Z))) `App` Var Z)) (Fst (Var Z)))
           (LinFun $
              LinPlus (LinZipWith (Lambda $ LinFun $
                                     Snd (Fst (Var (S (S Z))) `App` Var Z)
                                       `LinApp` LinVar Z)
                                  (Fst (Var Z))
                                  (Snd (Var Z) `LinApp` LinVar Z))
                      (LinMap (Snd (Var (S Z)) `LinApp` LinVar Z)
                              (Fst (Var Z))))

  SMap1 f e ->
    Let (Lambda (df f)) $
    Let (sinkTt1 (df e)) $
      Pair (Map (Lambda $ Fst (Var (S (S Z)) `App` Var Z)) (Fst (Var Z)))
           (LinFun $
              LinPlus (LinZipWith (Lambda $ LinFun $
                                     Snd (Var (S (S Z)) `App` Var Z)
                                       `LinApp` LinPair LinZero (LinVar Z))
                                  (Fst (Var Z))
                                  (Snd (Var Z) `LinApp` LinVar Z))
                      (LinMap (LinLam $
                                 Snd (Var (S (S Z)) `App` Var Z)
                                   `LinApp` LinPair (LinVar Z) LinZero)
                              (Fst (Var Z))))

  SReplicate e ->
    Let (df e) $
      Pair (Replicate (Fst (Var Z)))
           (LinFun $ LinReplicate (Snd (Var Z) `LinApp` LinVar Z))

  SSum e ->
    Let (df e) $
      Pair (Sum (Fst (Var Z)))
           (LinFun $ LinSum (Snd (Var Z) `LinApp` LinVar Z))
