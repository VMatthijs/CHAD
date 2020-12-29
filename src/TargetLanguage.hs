{-# LANGUAGE GADTs #-}
module TargetLanguage where

import Lib ((&&&))
import LanguageTypes (LFun, Tens, RealN, LT(..))
import Operation (Operation, LinearOperation, evalOp)


-- | Terms of the target language
data TTerm a b where
    -- Terms from source language

    -- | Identity function
    Id    :: TTerm a a
    -- | Composition
    --   Read as: f; g
    Comp  :: TTerm a b -> TTerm b c -> TTerm a c
    -- Product tuples
    Unit  :: TTerm a ()
    Pair  :: TTerm a b -> TTerm a c -> TTerm a (b, c)
    Fst   :: TTerm (a, b) a
    Snd   :: TTerm (a, b) b
    -- | Evaluation
    Ev    :: TTerm (a -> b, a) b
    -- | Curry
    Curry :: TTerm (a, b) c -> TTerm a (b -> c)
    -- | Operators
    Op    :: Operation a -> TTerm a RealN

    -- Target language extension

    -- | Linear operation
    LOp       :: LinearOperation a -> TTerm a RealN
    --   Linear functions
    LId       :: TTerm a (LFun b b) -- Correct? Why?
    LComp     :: TTerm a b -> TTerm b c -> TTerm a c
    LApp      :: TTerm a b -> TTerm () a -> TTerm () b
    LEval     :: TTerm () a -> TTerm (a -> b) b
    -- Tuples
    LFst      :: TTerm (a, b) a
    LSnd      :: TTerm (a, b) b
    LPair     :: TTerm a b -> TTerm a c -> TTerm a (b, c)
    -- LPair     :: TTerm i1 (LFun a b) -> TTerm i2 (LFun a c) -> TTerm i3 (LFun a (b, c))
    -- | Singleton
    Singleton :: TTerm () a -> TTerm b (Tens a b)
    -- Zero
    Zero      :: LT b => TTerm a b
    -- Plus
    Plus      :: LT b => TTerm a b -> TTerm a b -> TTerm a b
    -- Swap
    LSwap     :: TTerm a (LFun b c) -> TTerm b (a -> c)
    -- | Tensor-elimination
    LCur      :: (LT a, LT b, LT c) => TTerm a (LFun b c) -> TTerm (Tens a b) c

-- | Evaluate the target language
evalTt :: TTerm a b -> a -> b
-- Source language terms
evalTt  Id           = id
evalTt (Comp f g)    = evalTt g . evalTt f
evalTt  Unit         = const ()
evalTt (Pair a b)    = evalTt a &&& evalTt b
evalTt  Fst          = fst
evalTt  Snd          = snd
evalTt  Ev           = uncurry ($)
evalTt (Curry a)     = curry $ evalTt a
evalTt (Op op)       = evalOp op
-- Target language extension
evalTt (LOp lop)     = undefined -- TODO
evalTt  LId          = const id
evalTt (LComp f g)   = evalTt g . evalTt f
evalTt (LApp f a)    = \() -> evalTt f (evalTt a ())
evalTt  LFst         = fst
evalTt  LSnd         = snd
evalTt (LPair a b)   = evalTt a &&& evalTt b
evalTt (Singleton t) = \x -> [(evalTt t (), x)]
evalTt  Zero         = const zero
evalTt (Plus a b)    = \x -> plus (evalTt a x) (evalTt b x)
evalTt (LSwap t)     = flip $ evalTt t
evalTt (LCur t)      = foldr f zero
    where f x acc = plus (uncurry (evalTt t) x) acc

