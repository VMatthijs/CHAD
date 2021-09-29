{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Type where

import Data.GADT.Compare
import Data.Proxy
import Data.Type.Equality
import GHC.TypeNats

import Types


data Type t where
  TScal :: Type Scal
  TNil :: Type ()
  TPair :: Type a -> Type b -> Type (a, b)
  TFun :: Type a -> Type b -> Type (a -> b)
  TLFun :: Type a -> Type b -> Type (LFun a b)
  TCopow :: Type a -> Type b -> Type (Copower a b)
  TVect :: KnownNat n => Type (Vect n)

deriving instance Show (Type t)

instance GEq Type where
  geq TScal TScal = Just Refl
  geq TScal _ = Nothing
  geq TNil TNil = Just Refl
  geq TNil _ = Nothing
  geq (TPair a b) (TPair a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq TPair{} _ = Nothing
  geq (TFun a b) (TFun a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq TFun{} _ = Nothing
  geq (TLFun a b) (TLFun a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq TLFun{} _ = Nothing
  geq (TCopow a b) (TCopow a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq TCopow{} _ = Nothing
  geq a@TVect b@TVect
    | Just Refl <- check a b
    = Just Refl
    where -- TODO: Why don't pattern signatures work here?
          check :: forall n m. (KnownNat n, KnownNat m)
                => Type (Vect n) -> Type (Vect m) -> Maybe (n :~: m)
          check _ _ | Just Refl <- sameNat (Proxy @n) (Proxy @m) = Just Refl
                    | otherwise = Nothing
  geq TVect _ = Nothing
