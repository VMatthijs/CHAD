{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module RevLam where

import Lambda
import TargetLanguage.Env -- TODO don't put this module under TargetLanguage?
import Types


type family Dr1' a = r | r -> a where
  Dr1' Scal = Scal
  -- Dr1' (Vect n) = Vect n
  Dr1' (a, b) = (Dr1' a, Dr1' b)
  Dr1' () = ()
  -- Dr1' (Either a b) = Either (Dr1' a) (Dr1' b)
  Dr1' (a -> b) = Dr1' a -> (Dr1' b, Dr2' b -> Dr2' a)

type family Dr2' a where
  Dr2' Scal = Scal
  -- Dr2' (Vect n) = Vect n
  Dr2' (a, b) = (Dr2' a, Dr2' b)
  Dr2' () = ()
  -- Dr2' (Either a b) = LEither (Dr2' a) (Dr2' b)
  Dr2' (a -> b) = Copower (Dr1' a) (Dr2' b)

dr1t :: Type t -> Type (Dr1' t)
dr1t = undefined

dr2t :: Type t -> Type (Dr2' t)
dr2t = undefined


type family EnvType env where
  EnvType '[] = ()
  EnvType (t ': ts) = (t, EnvType ts)

data EnvS env where
  ENil :: EnvS '[]
  EPush :: Type t -> EnvS ts -> EnvS (t ': ts)

captureEnv :: EnvS env -> Lambda env (EnvType env)
captureEnv ENil = Unit
captureEnv (EPush t env) = Pair (Var t Z) (sinkLam (wSucc wId) (captureEnv env))

envType :: EnvS env -> Type (EnvType env)
envType ENil = TNil
envType (EPush ty env) = TPair ty (envType env)

cvtEnvIdx :: Idx env t -> Lambda env' (EnvType env) -> Lambda env' t
cvtEnvIdx Z e = Fst e
cvtEnvIdx (S i) e = cvtEnvIdx i (Snd e)

cvtDr1EnvIdx :: Idx env t -> Lambda env' (Dr1' (EnvType env)) -> Lambda env' (Dr1' t)
cvtDr1EnvIdx Z e = Fst e
cvtDr1EnvIdx (S i) e = cvtDr1EnvIdx i (Snd e)

zeroR :: Type t -> Lambda env (Dr1' t) -> Lambda env (Dr2' t)
zeroR = undefined

-- Two expression arguments must be duplicable
onehotEnv :: Type (EnvType env) -> Idx env t -> Lambda env' (Dr1' (EnvType env)) -> Lambda env' (Dr2' t) -> Lambda env' (Dr2' (EnvType env))
onehotEnv (TPair _ ty) Z e adj = Pair adj (zeroR ty (Snd e))
onehotEnv (TPair t1 t2) (S i) e adj =
  Pair (zeroR t1 (Fst e)) (onehotEnv t2 i (Snd e) adj)

let_ :: Type a -> Lambda env a -> Lambda (a ': env) b -> Lambda env b
let_ ty rhs body = App (Lambda ty body) rhs

dr :: EnvS env
   -> Lambda env t
   -> Lambda env' (Dr1' (EnvType env) -> (Dr1' t, Dr2' t -> Dr2' (EnvType env)))
dr env = \case
  Var ty idx ->
    Lambda primty $
      Pair (cvtDr1EnvIdx idx (Var primty Z))
           (Lambda (dr2t ty) $ zeroR (envType env) (Var primty (S Z)))

  Lambda argty body ->
    let resty = typeof body
        bodydr2ty = TPair (dr1t resty) (TFun (dr2t resty) (TPair (dr2t argty) (dr2t (envType env))))
    in
    -- Lambda body :: Term env (a -> b)
    -- body :: Term (a : env) b
    -- dr (Lambda body) :: Term env' (Dr1 (EnvType env)
    --                                -> (Dr1 a -> (Dr1 b, Dr2 b -> Dr2 a)
    --                                   ,Copow (Dr1 a) (Dr2 b) -> Dr2 (EnvType env)))
    -- dr body :: Term env' ((Dr1 a, Dr1 (EnvType env))
    --                       -> (Dr1 b, Dr2 b -> (Dr2 a, Dr2 (EnvType env))))
    -- \penv ->
    --   (\px -> let (py, dfun) = dr body (px, penv)
    --           in (py, fst . dfun)
    --   ,copowfold (\px -> let (_, dfun) = dr body (px, penv)
    --                      in snd . dfun))
    Lambda primty $
      Pair (Lambda (dr1t argty) $
              let_ bodydr2ty
                   (dr (EPush argty env) body
                      `App` Pair (Var (dr1t argty) Z) (Var primty (S Z))) $
                Pair (Fst (Var bodydr2ty Z))
                     (Lambda (dr2t resty) $
                        Fst (Snd (Var bodydr2ty (S Z)) `App` Var (dr2t resty) Z)))
           (Lambda (TCopow (dr1t argty) (dr2t resty)) $
             CopowFold (Lambda (dr1t argty) $ Lambda (dr2t resty) $
                          Snd (Snd (dr (EPush argty env) body
                                      `App` Pair (Var (dr1t argty) (S Z))
                                                 (Var primty (S (S (S Z)))))
                                 `App` Var (dr2t resty) Z))
                       (Var (TCopow (dr1t argty) (dr2t resty)) Z))

  App fun arg ->
    let TFun argty resty = typeof fun
        argdr2ty = TPair (dr1t argty) (TFun (dr2t argty) (dr2t (envType env)))
        fundr2ty = TPair (dr1t (typeof fun)) (TFun (dr2t (typeof fun)) (dr2t (envType env)))
    in
    -- fun :: Term env (a -> b)
    -- arg :: Term env a
    -- App fun arg :: Term env b
    -- dr (App fun arg) :: Term env' (Dr1 (EnvType env) -> (Dr1 b, Dr2 b -> Dr2 (EnvType env)))
    -- dr fun :: Term env' (Dr1 (EnvType env)
    --                      -> (Dr1 a -> (Dr1 b, Dr2 b -> Dr2 a)
    --                         ,Copower (Dr1 a) (Dr2 b) -> Dr2 (EnvType env)))
    -- dr arg :: Term env' (Dr1 (EnvType env) -> (Dr1 a, Dr2 a -> Dr2 (EnvType env)))
    -- \penv ->
    --   (fst (fst (dr fun penv) (fst (dr arg penv)))
    --   ,\dy -> let (px, darg) = dr arg penv
    --           in let (dfun1, dfun2) = dr fun penv
    --           in dfun2 (singleton px dy) + darg (snd (dfun1 px) dy))
    Lambda primty $
      Pair (Fst (Fst (dr env fun `App` Var primty Z) `App` Fst (dr env arg `App` Var primty Z)))
           (Lambda (dr2t resty) $
              let_ argdr2ty
                   (dr env arg `App` Var primty (S Z)) $
              let_ fundr2ty
                   (dr env fun `App` Var primty (S (S Z))) $
                AdjPlus (Snd (Var fundr2ty Z)
                           `App` Singleton (Fst (Var argdr2ty (S Z)))
                                           (Var (dr2t resty) (S (S Z))))
                        (Snd (Var argdr2ty (S Z))
                           `App` (Snd (Fst (Var fundr2ty Z) `App` Fst (Var argdr2ty (S Z)))
                                    `App` Var (dr2t resty) (S (S Z)))))

  Unit ->
    Lambda primty $
      Pair Unit (Lambda TNil $ zeroR (envType env) (Var primty (S Z)))

  Pair e1 e2 ->
    let e1dr2ty = TPair (dr1t (typeof e1)) (TFun (dr2t (typeof e1)) (dr2t (envType env)))
        e2dr2ty = TPair (dr1t (typeof e2)) (TFun (dr2t (typeof e2)) (dr2t (envType env)))
        adjty = TPair (dr2t (typeof e1)) (dr2t (typeof e2))
    in
    -- \penv ->
    --   let (p1, d1) = dr e1 penv
    --   in let (p2, d2) = dr e2 penv
    --   in ((p1, p2)
    --      ,\dy -> d1 (fst dy) + d2 (snd dy))
    Lambda primty $
      let_ e1dr2ty (dr env e1 `App` Var primty Z) $
      let_ e2dr2ty (dr env e2 `App` Var primty (S Z)) $
      Pair (Pair (Fst (Var e1dr2ty (S Z))) (Fst (Var e2dr2ty Z)))
           (Lambda adjty $
              AdjPlus (Snd (Var e1dr2ty (S (S Z))) `App` Fst (Var adjty Z))
                      (Snd (Var e2dr2ty (S Z)) `App` Snd (Var adjty Z)))

  _ -> undefined
  where
    primty = dr1t (envType env)
