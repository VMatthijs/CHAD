{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
module SourceLanguage where

import Data.Vector.Sized as V (map, singleton, index)

import Lib ((&&&))
import Types
import Operation (Operation, evalOp)
import LanguageTypes
import GHC.TypeNats (KnownNat)


-- | Terms of the source language
data STerm a b where
    -- | Identity function
    Id    :: (LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a))
          => STerm a a
    -- | Composition
    --   Read as: f; g
    Comp  :: ( LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)
             , LT b, LT (Dr1 b), LT (Dr2 b), LT (Df1 b), LT (Df2 b)
             )
          => STerm a b -> STerm b c -> STerm a c
    -- Product tuples
    Unit  :: (LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a))
          => STerm a ()
    Pair  :: ( LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)
             , LT b, LT (Dr1 b), LT (Dr2 b), LT (Df1 b), LT (Df2 b)
             , LT c, LT (Dr1 c), LT (Dr2 c), LT (Df1 c), LT (Df2 c)
             )
          => STerm a b -> STerm a c -> STerm a (b, c)
    Fst   :: ( LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)
             , LT b, LT (Dr1 b), LT (Dr2 b), LT (Df1 b), LT (Df2 b)
             )
          => STerm (a, b) a
    Snd   :: ( LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)
             , LT b, LT (Dr1 b), LT (Dr2 b), LT (Df1 b), LT (Df2 b)
             )
          => STerm (a, b) b
    -- | Evaluation
    Ev    :: ( LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)
             , LT b, LT (Dr1 b), LT (Dr2 b), LT (Df1 b), LT (Df2 b)
             )
          => STerm (a -> b, a) b
    -- | Curry
    Curry :: ( LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)
             , LT b, LT (Dr1 b), LT (Dr2 b), LT (Df1 b), LT (Df2 b)
             , LT c, LT (Dr1 c), LT (Dr2 c), LT (Df1 c), LT (Df2 c)
             )
          => STerm (a, b) c -> STerm a (b -> c)
    -- | Operators
    Op    :: ( LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)
             , LT b, LT (Dr1 b), LT (Dr2 b), LT (Df1 b), LT (Df2 b)
             , a ~ Dr1 a, b ~ Dr1 b
             , a ~ Df1 a, b ~ Df1 b
             )
          => Operation a b -> STerm a b
    -- | Map
    Map   :: KnownNat n
          => STerm (RealN 1 -> RealN 1, RealN n) (RealN n)

-- | Evaluate the source language
evalSt :: STerm a b -> a -> b
evalSt  Id        = id
evalSt (Comp f g) = evalSt g . evalSt f
evalSt  Unit      = const ()
evalSt (Pair a b) = evalSt a &&& evalSt b
evalSt  Fst       = fst
evalSt  Snd       = snd
evalSt  Ev        = uncurry ($)
evalSt (Curry a)  = curry $ evalSt a
evalSt (Op op)    = evalOp op
evalSt  Map       = \(f, v) -> V.map (flip index 0 . f . singleton) v
