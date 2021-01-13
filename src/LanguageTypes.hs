{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module LanguageTypes where

import Prelude hiding (zipWith, replicate)
import Data.Proxy (Proxy(Proxy))
import Data.Vector.Sized (replicate, zipWith)
import GHC.TypeNats (KnownNat)

import Types (Type(..), Tens, RealN)


-- | Operators defined over multiple language types
class LT a where
    zero      :: a
    plus      :: a -> a -> a
    inferType :: Type a

instance LT () where
    zero      = ()
    plus _ _  = ()
    inferType = TUnit

instance (LT a, LT b) => LT (a, b) where
    zero      = (zero, zero)
    plus a b  = (fst a `plus` fst b, snd a `plus` snd b)
    inferType = TPair inferType inferType

instance KnownNat n => LT (RealN n) where
    zero      = replicate 0
    plus      = zipWith (+)
    inferType = TRealN (Proxy @n)

instance (LT a, LT b) => LT (a -> b) where
    zero      = const zero
    plus f g  = \x -> plus (f x) (g x)
    inferType = TArrow inferType inferType

instance (LT a, LT b) => LT (Tens a b) where
    zero      = []
    plus      = (++)
    inferType = TTens inferType inferType
