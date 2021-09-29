{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}

-- | Reverse-AD functions
module ReverseAD where

import Data.GADT.Compare
import Data.Type.Equality

import           Operation          (LinearOperation' (..), Operation (..))
import           SourceLanguage     as SL
import           TargetLanguage     as TL
import           Env
import           Type
import           Types              (Dr1, Dr2, LFun)

type family Dr1Env env where
  Dr1Env '[] = '[]
  Dr1Env (t ': env) = Dr1 t ': Dr1Env env

type family Dr2Env env where
  Dr2Env '[] = ()
  Dr2Env (t ': env) = (Dr2Env env, Dr2 t)

dr1t :: Type t -> Type (Dr1 t)
dr1t TScal = TScal
dr1t TNil = TNil
dr1t (TPair a b) = TPair (dr1t a) (dr1t b)
dr1t (TFun a b) = TFun (dr1t a) (TPair (dr1t b) (TLFun (dr2t b) (dr2t a)))
dr1t TVect = TVect
dr1t TLFun{} = error "No Dr1 for linear functions"
dr1t TCopow{} = error "No Dr1 for copowers"

dr2t :: Type t -> Type (Dr2 t)
dr2t TScal = TScal
dr2t TNil = TNil
dr2t (TPair a b) = TPair (dr2t a) (dr2t b)
dr2t (TFun a b) = TCopow (dr1t a) (dr2t b)
dr2t TVect = TVect
dr2t TLFun{} = error "No Dr2 for linear functions"
dr2t TCopow{} = error "No Dr2 for copowers"

data EnvS env where
  ENil :: EnvS '[]
  EPush :: Type t -> EnvS ts -> EnvS (t ': ts)

dr2envt :: EnvS env -> Type (Dr2Env env)
dr2envt ENil = TNil
dr2envt (EPush t env) = TPair (dr2envt env) (dr2t t)


cvtDr1EnvIdx :: Idx env t -> Idx (Dr1Env env) (Dr1 t)
cvtDr1EnvIdx Z = Z
cvtDr1EnvIdx (S i) = S (cvtDr1EnvIdx i)

onehotEnv :: EnvS env -> Idx env t -> LinTTerm env' (Dr2 t) (Dr2Env env)
onehotEnv (EPush _ env) Z = LinPair (TL.LinZero (dr2envt env)) TL.LinVar
onehotEnv (EPush t env) (S i) = LinPair (onehotEnv env i) (TL.LinZero (dr2t t))

drt :: EnvS env -> Type t -> Type (Dr1 t, LFun (Dr2 t) (Dr2Env env))
drt env t = TPair (dr1t t) (TLFun (dr2t t) (dr2envt env))

drOp :: a ~ Dr1 a => Type a -> Type b -> Operation a b -> TTerm env (a -> LFun (Dr2 b) (Dr2 a))
drOp t t' (Constant _) = Lambda t $ TL.Zero (TLFun (dr2t t') TNil)
drOp t _ EAdd = Lambda t $ TL.LPair (TL.LId TVect) (TL.LId TVect)
drOp t _ EProd = Lambda t $ TL.LPair (TL.LOp LProd `TL.App` TL.Snd (TL.Var t Z))
                                       (LOp LProd `TL.App` TL.Fst (TL.Var t Z))
drOp t _ EScalAdd = Lambda t $ TL.LPair (TL.LId TScal) (TL.LId TScal)
drOp t _ EScalSubt = Lambda t $ TL.LPair (TL.LId TScal) (TL.LOp LScalNeg `TL.App` TL.Unit)
drOp t _ EScalProd = Lambda t $ TL.LPair (TL.LOp LScalProd `TL.App` TL.Snd (TL.Var t Z))
                                            (LOp LScalProd `TL.App` TL.Fst (TL.Var t Z))
drOp t _ EScalSin = Lambda t $ TL.LOp LScalProd `TL.App` TL.Op TScal EScalCos (TL.Var t Z)
drOp t _ EScalCos = Lambda t $ TL.LOp LScalProd `TL.App` neg (TL.Op TScal EScalSin (TL.Var t Z))
  where neg x = Op TScal EScalSubt (TL.Pair (TL.Op TScal (Constant 0.0) TL.Unit) x)
drOp t _ Sum = Lambda t $ TL.LOp LReplicate `TL.App` TL.Unit

dr :: EnvS env
   -> STerm env t
   -> TTerm (Dr1Env env) (Dr1 t, LFun (Dr2 t) (Dr2Env env))
dr env = \case
  SVar ty idx ->
    Pair (Var (dr1t ty) (cvtDr1EnvIdx idx))
         (makeLFunTerm (dr2t ty) (onehotEnv env idx))

  SLambda argty body ->
    let resty = typeofSt body
        bodydr2ty = drt (EPush argty env) resty
        bndty = TFun (dr1t argty) bodydr2ty
    in Let (Lambda (dr1t argty) $ dr (EPush argty env) body) $
         Pair (Lambda (dr1t argty) $
                 Let (Var bndty (S Z) `App` Var (dr1t argty) Z) $
                   Pair (Fst (Var bodydr2ty Z))
                        (makeLFunTerm (dr2t resty) $
                           LinSnd (Snd (Var bodydr2ty Z) `LinApp` LinVar)))
              (makeLFunTerm (TCopow (dr1t argty) (dr2t resty)) $
                 LinCopowFold
                     (Lambda (dr1t argty) $ makeLFunTerm (dr2t resty) $
                        LinFst (Snd (Var bndty (S Z) `App` Var (dr1t argty) Z)
                                  `LinApp` LinVar))
                     LinVar)

  SLet rhs body ->
    let rhsty = typeofSt rhs
        resty = typeofSt body
        bndty1 = drt env rhsty
        bndty2 = drt (EPush rhsty env) resty
    in Let (dr env rhs) $
       Let (substTt (wSucc wId) (Fst (Var (drt env rhsty) Z))
                    (dr (EPush rhsty env) body)) $
         Pair (Fst (Var bndty2 Z))
              (makeLFunTerm (dr2t resty) $
                 LinLet' (dr2envt (EPush rhsty env))
                         (Snd (Var bndty2 Z) `LinApp` LinVar)
                         (LinPlus (LinFst LinVar)
                                  (Snd (Var bndty1 (S Z)) `LinApp` LinSnd LinVar)))

  SApp fun arg ->
    let TFun argty resty = typeofSt fun
        argdr2ty = drt env (typeofSt arg)
        fundr2ty = drt env (typeofSt fun)
        fundiffty = TPair (dr1t resty) (TLFun (dr2t resty) (dr2t argty))
    in Let (dr env arg) $
       Let (sinkTt (wSucc wId) (dr env fun)) $
       Let (App (Fst (Var fundr2ty Z)) (Fst (Var argdr2ty (S Z)))) $
         Pair (Fst (Var fundiffty Z))
              (makeLFunTerm (dr2t resty) $
                 LinPlus (Snd (Var argdr2ty (S (S Z)))
                            `LinApp` (Snd (Var fundiffty Z) `LinApp` LinVar))
                         (Snd (Var fundr2ty (S Z))
                            `LinApp` LinSingleton (Fst (Var argdr2ty (S (S Z)))) LinVar))

  SUnit -> Pair Unit (Zero (TLFun TNil (dr2envt env)))

  SPair e1 e2 ->
    let e1dr2ty = drt env (typeofSt e1)
        e2dr2ty = drt env (typeofSt e2)
        adjty = TPair (dr2t (typeofSt e1)) (dr2t (typeofSt e2))
    in Let (dr env e1) $
       Let (sinkTt (wSucc wId) (dr env e2)) $
         Pair (Pair (Fst (Var e1dr2ty (S Z))) (Fst (Var e2dr2ty Z)))
              (makeLFunTerm adjty $
                 LinPlus (Snd (Var e1dr2ty (S Z)) `LinApp` LinFst LinVar)
                         (Snd (Var e2dr2ty Z    ) `LinApp` LinSnd LinVar))

  SFst e ->
    let TPair t1 t2 = typeofSt e
        dty = drt env (typeofSt e)
    in Let (dr env e) $
         Pair (Fst (Fst (Var dty Z)))
              (makeLFunTerm (dr2t t1) $
                 Snd (Var dty Z)
                   `LinApp` LinPair LinVar (LinZero (dr2t t2)))

  SSnd e ->
    let TPair t1 t2 = typeofSt e
        dty = drt env (typeofSt e)
    in Let (dr env e) $
         Pair (Snd (Fst (Var dty Z)))
              (makeLFunTerm (dr2t t2) $
                 Snd (Var dty Z)
                   `LinApp` LinPair (LinZero (dr2t t1)) LinVar)

  SOp resty op arg
    | let dty = drt env (typeofSt arg)
    , Just Refl <- geq (typeofSt arg) (dr1t (typeofSt arg))
    , Just Refl <- geq resty (dr1t resty)
    -> Let (dr env arg) $
         Pair (Op resty op (Fst (Var dty Z)))
              (makeLFunTerm (dr2t resty) $
                 let dop = drOp (typeofSt arg) resty op `App` Fst (Var dty Z)
                 in Snd (Var dty Z) `LinApp` (dop `LinApp` LinVar))

  _ -> undefined
