{-# LANGUAGE FlexibleInstances #-}
module LanguageTypes where

import Prelude hiding (zipWith)
import Data.Vector (singleton, zipWith)
import Types (Type(..), Tens, RealN)


-- | Operators defined over multiple language types
class LT a where
    zero :: a
    plus :: a -> a -> a
    inferType :: Type a

instance LT () where
    zero      = ()
    plus _ _  = ()
    inferType = TUnit

instance (LT a, LT b) => LT (a, b) where
    zero      = (zero, zero)
    plus a b  = (fst a `plus` fst b, snd a `plus` snd b)
    inferType = TPair inferType inferType

instance LT RealN where
    zero      = singleton 0 -- TODO: Correct zero type?
    plus      = zipWith (+)
    inferType = TRealN

instance (LT a, LT b) => LT (a -> b) where
    zero      = const zero
    plus f g  = \x -> plus (f x) (g x)
    inferType = TArrow inferType inferType

instance (LT a, LT b) => LT (Tens a b) where
    zero      = []
    plus      = (++)
    inferType = TTens inferType inferType
