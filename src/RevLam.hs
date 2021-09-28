{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
module RevLam where

import Data.GADT.Compare
import Data.Type.Equality

import Lambda
import Operation (Operation(..), LinearOperation'(..))
import TargetLanguage.Env -- TODO don't put this module under TargetLanguage?
import Types


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

onehotEnv :: EnvS env -> Idx env t -> LinLambda env' (Dr2 t) (Dr2Env env)
onehotEnv (EPush _ env) Z = LinPair (LinZero (dr2envt env)) LinVar
onehotEnv (EPush t env) (S i) = LinPair (onehotEnv env i) (LinZero (dr2t t))

let_ :: Type a -> Lambda env a -> Lambda (a ': env) b -> Lambda env b
let_ ty rhs body = App (Lambda ty body) rhs

drt :: EnvS env -> Type t -> Type (Dr1 t, LFun (Dr2 t) (Dr2Env env))
drt env t = TPair (dr1t t) (TLFun (dr2t t) (dr2envt env))

drOp :: a ~ Dr1 a => Type a -> Type b -> Operation a b -> Lambda env (a -> LFun (Dr2 b) (Dr2 a))
drOp t t' (Constant _) = Lambda t $ Zero (TLFun (dr2t t') TNil)
drOp t _ EAdd = Lambda t $ LPair (LId TVect) (LId TVect)
drOp t _ EProd = Lambda t $ LPair (LOp LProd `App` Snd (Var t Z))
                                  (LOp LProd `App` Fst (Var t Z))
drOp t _ EScalAdd = Lambda t $ LPair (LId TScal) (LId TScal)
drOp t _ EScalSubt = Lambda t $ LPair (LId TScal) (LOp LScalNeg `App` Unit)
drOp t _ EScalProd = Lambda t $ LPair (LOp LScalProd `App` Snd (Var t Z))
                                      (LOp LScalProd `App` Fst (Var t Z))
drOp t _ Sum = Lambda t $ LOp LReplicate `App` Unit

dr :: EnvS env
   -> Lambda env t
   -> Lambda (Dr1Env env) (Dr1 t, LFun (Dr2 t) (Dr2Env env))
dr env = \case
  Var ty idx ->
    Pair (Var (dr1t ty) (cvtDr1EnvIdx idx))
         (makeLFunTerm (dr2t ty) (onehotEnv env idx))

  Lambda argty body ->
    let resty = typeof body
        bodydr2ty = drt (EPush argty env) (typeof body)
        bndty = TFun (dr1t argty) bodydr2ty
    in let_ bndty (Lambda (dr1t argty) $ dr (EPush argty env) body) $
         Pair (Lambda (dr1t argty) $
                 let_ bodydr2ty (Var bndty (S Z) `App` Var (dr1t argty) Z) $
                   Pair (Fst (Var bodydr2ty Z))
                        (makeLFunTerm (dr2t resty) $
                           LinSnd (Snd (Var bodydr2ty Z) `LinApp` LinVar)))
              (makeLFunTerm (TCopow (dr1t argty) (dr2t resty)) $
                 LinCopowFold
                     (Lambda (dr1t argty) $ makeLFunTerm (dr2t resty) $
                        LinFst (Snd (Var bndty (S Z) `App` Var (dr1t argty) Z)
                                  `LinApp` LinVar))
                     LinVar)

  Let rhs body ->
    let rhsty = typeof rhs
        resty = typeof body
        bndty1 = drt env rhsty
        bndty2 = drt (EPush rhsty env) resty
    in let_ bndty1 (dr env rhs) $
       let_ bndty2 (substLam (wSucc wId) (Fst (Var (drt env rhsty) Z))
                        (dr (EPush rhsty env) body)) $
         Pair (Fst (Var bndty2 Z))
              (makeLFunTerm (dr2t resty) $
                 LinLet' (dr2envt (EPush rhsty env))
                         (Snd (Var bndty2 Z) `LinApp` LinVar)
                         (LinPlus (LinFst LinVar)
                                  (Snd (Var bndty1 (S Z)) `LinApp` LinSnd LinVar)))

  App fun arg ->
    let TFun argty resty = typeof fun
        argdr2ty = drt env (typeof arg)
        fundr2ty = drt env (typeof fun)
        fundiffty = TPair (dr1t resty) (TLFun (dr2t resty) (dr2t argty))
    in let_ argdr2ty (dr env arg) $
       let_ fundr2ty (sinkLam (wSucc wId) (dr env fun)) $
       let_ fundiffty (App (Fst (Var fundr2ty Z)) (Fst (Var argdr2ty (S Z)))) $
         Pair (Fst (Var fundiffty Z))
              (makeLFunTerm (dr2t resty) $
                 LinPlus (Snd (Var argdr2ty (S (S Z)))
                            `LinApp` (Snd (Var fundiffty Z) `LinApp` LinVar))
                         (Snd (Var fundr2ty (S Z))
                            `LinApp` LinSingleton (Fst (Var argdr2ty (S (S Z)))) LinVar))

  Unit -> Pair Unit (Zero (TLFun TNil (dr2envt env)))

  Pair e1 e2 ->
    let e1dr2ty = drt env (typeof e1)
        e2dr2ty = drt env (typeof e2)
        adjty = TPair (dr2t (typeof e1)) (dr2t (typeof e2))
    in let_ e1dr2ty (dr env e1) $
       let_ e2dr2ty (sinkLam (wSucc wId) (dr env e2)) $
         Pair (Pair (Fst (Var e1dr2ty (S Z))) (Fst (Var e2dr2ty Z)))
              (makeLFunTerm adjty $
                 LinPlus (Snd (Var e1dr2ty (S Z)) `LinApp` LinFst LinVar)
                         (Snd (Var e2dr2ty Z    ) `LinApp` LinSnd LinVar))

  Fst e ->
    let TPair t1 t2 = typeof e
        dty = drt env (typeof e)
    in let_ dty (dr env e) $
         Pair (Fst (Fst (Var dty Z)))
              (makeLFunTerm (dr2t t1) $
                 Snd (Var dty Z)
                   `LinApp` LinPair LinVar (LinZero (dr2t t2)))

  Snd e ->
    let TPair t1 t2 = typeof e
        dty = drt env (typeof e)
    in let_ dty (dr env e) $
         Pair (Snd (Fst (Var dty Z)))
              (makeLFunTerm (dr2t t2) $
                 Snd (Var dty Z)
                   `LinApp` LinPair (LinZero (dr2t t1)) LinVar)

  Op resty op arg
    | let dty = drt env (typeof arg)
    , Just Refl <- geq (typeof arg) (dr1t (typeof arg))
    , Just Refl <- geq resty (dr1t resty)
    -> let_ dty (dr env arg) $
         Pair (Op resty op (Fst (Var dty Z)))
              (makeLFunTerm (dr2t resty) $
                 let dop = drOp (typeof arg) resty op `App` Fst (Var dty Z)
                 in Snd (Var dty Z) `LinApp` (dop `LinApp` LinVar))

  _ -> undefined
