{-# LANGUAGE FlexibleInstances #-}
module LanguageTypes where

import Prelude hiding (zipWith)
import Data.Vector (Vector, singleton, zipWith)

type RealN = Vector Double

type Tens a b = [(a, b)]
-- | Linear function
type LFun a b = a -> b


-- | Operators defined over multiple language types
class LT a where
    zero :: a
    plus :: a -> a -> a

instance LT RealN where
    zero = singleton 0 -- TODO: Correct zero type?
    plus = zipWith (+)

instance (LT a, LT b) => LT (a -> b) where
    zero     = const zero
    plus f g = \x -> plus (f x) (g x)

instance (LT a, LT b) => LT (Tens a b) where
    zero = []
    plus = (++)
