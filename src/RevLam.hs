{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module RevLam where

import Lambda
import Operation (Operation(..))
import TargetLanguage.Env -- TODO don't put this module under TargetLanguage?
import Types


type family Dr1' a = r | r -> a where
  Dr1' Scal = Scal
  -- Dr1' (Vect n) = Vect n
  Dr1' (a, b) = (Dr1' a, Dr1' b)
  Dr1' () = ()
  Dr1' (Either a b) = Either (Dr1' a) (Dr1' b)
  Dr1' (a -> b) = Dr1' a -> (Dr1' b, Dr2' b -> Dr2' a)

type family Dr2' a where
  Dr2' Scal = Scal
  -- Dr2' (Vect n) = Vect n
  Dr2' (a, b) = (Dr2' a, Dr2' b)
  Dr2' () = ()
  Dr2' (Either a b) = Either (Dr2' a) (Dr2' b)
  Dr2' (a -> b) = Copower (Dr1' a) (Dr2' b)

type family Dr1Env env where
  Dr1Env '[] = '[]
  Dr1Env (t ': env) = Dr1' t ': Dr1Env env

type family Dr2Env env where
  Dr2Env '[] = ()
  Dr2Env (t ': env) = (Dr2' t, Dr2Env env)

dr1t :: Type t -> Type (Dr1' t)
dr1t TScal = TScal
dr1t TNil = TNil
dr1t (TPair a b) = TPair (dr1t a) (dr1t b)
dr1t (TFun a b) = TFun (dr1t a) (TPair (dr1t b) (TFun (dr2t b) (dr2t a)))
dr1t t = error ("dr1 unimplemented for type " ++ show t)

dr2t :: Type t -> Type (Dr2' t)
dr2t TScal = TScal
dr2t TNil = TNil
dr2t (TPair a b) = TPair (dr2t a) (dr2t b)
dr2t (TFun a b) = TCopow (dr1t a) (dr2t b)
dr2t t = error ("dr2 unimplemented for type " ++ show t)

data EnvS env where
  ENil :: EnvS '[]
  EPush :: Type t -> EnvS ts -> EnvS (t ': ts)

dr2envt :: EnvS env -> Type (Dr2Env env)
dr2envt ENil = TNil
dr2envt (EPush t env) = TPair (dr2t t) (dr2envt env)

data Dict c t where
  Dict :: c t => Dict c t

dr2hasLT :: Type t -> Dict LT (Dr2' t)
dr2hasLT TScal = Dict
dr2hasLT TNil = Dict
dr2hasLT (TPair a b)
  | Dict <- dr2hasLT a
  , Dict <- dr2hasLT b
  = Dict
dr2hasLT (TFun a b)
  | Dict <- dr2hasLT a
  , Dict <- dr2hasLT b
  = Dict
dr2hasLT t = error ("dr2 unimplemented for type " ++ show t)

dr2envHasLT :: EnvS env -> Dict LT (Dr2Env env)
dr2envHasLT ENil = Dict
dr2envHasLT (EPush t env)
  | Dict <- dr2hasLT t
  , Dict <- dr2envHasLT env
  = Dict


cvtDr1EnvIdx :: Idx env t -> Idx (Dr1Env env) (Dr1' t)
cvtDr1EnvIdx Z = Z
cvtDr1EnvIdx (S i) = S (cvtDr1EnvIdx i)

-- | Given primal must be a duplicable expression.
zeroR :: Type t -> Lambda env (Dr1' t) -> Lambda env (Dr2' t)
zeroR TScal _ = Op (Constant 0) Unit
zeroR TNil _ = Unit
zeroR (TPair t1 t2) e = Pair (zeroR t1 (Fst e)) (zeroR t2 (Snd e))
zeroR (TEither t1 t2) e =
    Case e (Lambda (dr1t t1) (Inl (dr2t t2) (zeroR t1 (Var (dr1t t1) Z))))
           (Lambda (dr1t t2) (Inr (dr2t t1) (zeroR t2 (Var (dr1t t2) Z))))
zeroR (TFun t1 t2) _
  | Dict <- dr2hasLT t2  -- TODO: THIS IS UGLY, REMOVE THIS AND FIX
  = EmptyCopow (dr1t t1) (dr2t t2)
zeroR TCopow{} _ = error "zeroR: copower in primal program"
zeroR TVect _ = undefined

zeroEnv :: Dr1Env env :> env' -> EnvS env -> Lambda env' (Dr2Env env)
zeroEnv _ ENil = Unit
zeroEnv w (EPush t env) = Pair (zeroR t (Var (dr1t t) (w >:> Z)))
                               (zeroEnv (wRaise w) env)

onehotEnv :: Dr1Env env :> env' -> Lambda env' (Dr2' t) -> Idx env t -> EnvS env -> Lambda env' (Dr2Env env)
onehotEnv w adj Z (EPush _ env) = Pair adj (zeroEnv (w .> wSucc wId) env)
onehotEnv w adj (S i) (EPush ty env) = Pair (zeroR ty (Var (dr1t ty) (w >:> Z)))
                                            (onehotEnv (wRaise w) adj i env)

let_ :: Type a -> Lambda env a -> Lambda (a ': env) b -> Lambda env b
let_ ty rhs body = App (Lambda ty body) rhs

drt :: EnvS env -> Type t -> Type (Dr1' t, Dr2' t -> Dr2Env env)
drt env t = TPair (dr1t t) (TFun (dr2t t) (dr2envt env))

dr :: EnvS env
   -> Lambda env t
   -> Lambda (Dr1Env env) (Dr1' t, Dr2' t -> Dr2Env env)
dr env = \case
  Var ty idx ->
    Pair (Var (dr1t ty) (cvtDr1EnvIdx idx))
         (Lambda (dr2t ty) $ onehotEnv (wSucc wId) (Var (dr2t ty) Z) idx env)

  Lambda argty body
    | let resty = typeof body
    , Dict <- dr2hasLT resty
    , Dict <- dr2envHasLT env
    , let bodydr2ty = drt (EPush argty env) (typeof body)
    -> let_ (TFun (dr1t argty) bodydr2ty)
            (Lambda (dr1t argty) $ dr (EPush argty env) body) $
         Pair (Lambda (dr1t argty) $
                 let_ bodydr2ty (Var (TFun (dr1t argty) bodydr2ty) (S Z) `App` Var (dr1t argty) Z) $
                   Pair (Fst (Var bodydr2ty Z))
                        (Lambda (dr2t resty) $
                           Fst (Snd (Var bodydr2ty (S Z)) `App` Var (dr2t resty) Z)))
              (Lambda (TCopow (dr1t argty) (dr2t resty)) $
                 CopowFold (Lambda (dr1t argty) $ Lambda (dr2t resty) $
                              Snd (Snd (Var (TFun (dr1t argty) bodydr2ty) (S (S (S Z))) `App` Var (dr1t argty) (S Z))
                                     `App` Var (dr2t resty) Z))
                           (Var (TCopow (dr1t argty) (dr2t resty)) Z))

  App fun arg
    | let TFun argty resty = typeof fun
    , Dict <- dr2envHasLT env
    , Dict <- dr2hasLT resty
    , let argdr2ty = drt env (typeof arg)
          fundr2ty = drt env (typeof fun)
          fundiffty = TPair (dr1t resty) (TFun (dr2t resty) (dr2t argty))
    -> let_ argdr2ty (dr env arg) $
       let_ fundr2ty (sinkLam (wSucc wId) (dr env fun)) $
       let_ fundiffty (App (Fst (Var fundr2ty Z)) (Fst (Var argdr2ty (S Z)))) $
         Pair (Fst (Var fundiffty Z))
              (Lambda (dr2t resty) $
                 AdjPlus (Snd (Var argdr2ty (S (S (S Z))))
                            `App` (Snd (Var fundiffty (S Z)) `App` Var (dr2t resty) Z))
                         (Snd (Var fundr2ty (S (S Z)))
                            `App` Singleton (Fst (Var argdr2ty (S (S (S Z))))) (Var (dr2t resty) Z)))

  Unit -> Pair Unit (Lambda TNil $ zeroEnv (wSucc wId) env)

  Pair e1 e2
    | Dict <- dr2envHasLT env
    , let e1dr2ty = drt env (typeof e1)
          e2dr2ty = drt env (typeof e2)
          adjty = TPair (dr2t (typeof e1)) (dr2t (typeof e2))
    -> let_ e1dr2ty (dr env e1) $
       let_ e2dr2ty (sinkLam (wSucc wId) (dr env e2)) $
         Pair (Pair (Fst (Var e1dr2ty (S Z))) (Fst (Var e2dr2ty Z)))
              (Lambda adjty $
                 AdjPlus (Snd (Var e1dr2ty (S (S Z))) `App` Fst (Var adjty Z))
                         (Snd (Var e2dr2ty (S Z)    ) `App` Snd (Var adjty Z)))

  Fst e ->
    let TPair t1 t2 = typeof e
        dty = drt env (typeof e)
    in let_ dty (dr env e) $
         Pair (Fst (Fst (Var dty Z)))
              (Lambda (dr2t t1) $
                 Snd (Var dty (S Z))
                   `App` Pair (Var (dr2t t1) Z)
                              (zeroR t2 (Snd (Fst (Var dty (S Z))))))

  Snd e ->
    let TPair t1 t2 = typeof e
        dty = drt env (typeof e)
    in let_ dty (dr env e) $
         Pair (Snd (Fst (Var dty Z)))
              (Lambda (dr2t t2) $
                 Snd (Var dty (S Z))
                   `App` Pair (zeroR t1 (Fst (Fst (Var dty (S Z)))))
                              (Var (dr2t t2) Z))

  _ -> undefined
