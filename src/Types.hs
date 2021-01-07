{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Types where

import Data.Type.Equality ((:~:)(Refl), (:~:))
import GHC.TypeNats (sameNat, Nat, KnownNat)
import Data.Vector (Vector)

type RealN = Vector Double

type Tens a b = [(a, b)]
-- | Linear function
type LFun a b = a -> b



data Type a where
    TRealN  :: Type RealN
    TArrow  :: Type a -> Type b -> Type (a -> b)
    TPair   :: Type a -> Type b -> Type (a, b)
    TUnit   :: Type ()

    TLinFun :: Type a -> Type b -> Type (LFun a b)
    TTens   :: Type a -> Type b -> Type (Tens a b)


eqTy :: Type u -> Type v -> Maybe (u :~: v)
eqTy TRealN  TRealN = Just Refl
eqTy TUnit   TUnit  = Just Refl
eqTy (TArrow  u1 u2) (TArrow  v1 v2) =
    do Refl <- eqTy u1 v1
       Refl <- eqTy u2 v2
       return Refl
eqTy (TPair   u1 u2) (TPair   v1 v2) =
    do Refl <- eqTy u1 v1
       Refl <- eqTy u2 v2
       return Refl
eqTy (TLinFun u1 u2) (TLinFun v1 v2) =
    do Refl <- eqTy u1 v1
       Refl <- eqTy u2 v2
       return Refl
eqTy (TTens u1 u2) (TTens v1 v2) =
    do Refl <- eqTy u1 v1
       Refl <- eqTy u2 v2
       return Refl
eqTy _ _ = Nothing
