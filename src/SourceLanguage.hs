{-# LANGUAGE GADTs #-}
module SourceLanguage where

import Lib ((&&&))
import LanguageTypes (RealN)
import Operation (Operation, evalOp)


-- | Terms of the source language
data STerm a b where
    -- | Identity function
    Id    :: STerm a a
    -- | Composition
    --   Read as: f; g
    Comp  :: STerm a b -> STerm b c -> STerm a c
    -- Product tuples
    Unit  :: STerm a ()
    Pair  :: STerm a b -> STerm a c -> STerm a (b, c)
    Fst   :: STerm (a, b) a
    Snd   :: STerm (a, b) b
    -- | Evaluation
    Ev    :: STerm (a -> b, a) b
    -- | Curry
    Curry :: STerm (a, b) c -> STerm a (b -> c)
    -- | Operators
    Op    :: Operation a -> STerm a RealN

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
