{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module LanguageTypes where

import Prelude hiding (zipWith, replicate)
import Data.Proxy (Proxy(Proxy))
import Data.Vector.Unboxed.Sized (replicate, zipWith)
import GHC.TypeNats (KnownNat)

import Types as T (LT(..), Type(..), Tens, LFun, RealN, empty, (++), lConst, lPlus)

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
    zero      = empty
    plus      = (T.++)
    inferType = TTens inferType inferType

instance (LT a, LT b) => LT (LFun a b) where
    zero      = lConst zero
    plus      = lPlus
    inferType = TLinFun inferType inferType
