{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Types where

import Data.Type.Equality ((:~:)(Refl), (:~:))
import Data.Vector (Vector)

type RealN = Vector Double

type Tens a b = [(a, b)]
-- | Linear function
type LFun a b = a -> b

-- Forward mode AD type families

type family Df1 a = r | r -> a where
    Df1 RealN    = RealN
    Df1 (a -> b) = Df1 a -> (Df1 b, LFun (Df2 a) (Df2 b))
    Df1 (a, b)   = (Df1 a, Df1 b)
    Df1 ()       = ()

type family Df2 a = r | r -> a where
    Df2 RealN    = RealN
    Df2 (a -> b) = Df1 a -> Df2 b
    Df2 (a, b)   = (Df2 a, Df2 b)
    Df2 ()       = ()

-- Reverse mode AD type families

type family Dr1 a = r | r -> a where
    Dr1 RealN    = RealN
    Dr1 (a -> b) = Dr1 a -> (Dr1 b, LFun (Dr2 b) (Dr2 a))
    Dr1 (a, b)   = (Dr1 a, Dr1 b)
    Dr1 ()       = ()

type family Dr2 a = r | r -> a where
    Dr2 RealN    = RealN
    Dr2 (a -> b) = Tens (Dr1 a) (Dr2 b)
    Dr2 (a, b)   = (Dr2 a, Dr2 b)
    Dr2 ()       = ()

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

