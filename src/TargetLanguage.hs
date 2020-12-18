{-# LANGUAGE GADTs #-}
module TargetLanguage where

import Lib ((&&&))
import LanguageTypes (LFun, Tens, RealN, LT(..))
import SourceLanguage (STerm, evalSt)
import Operation (LinearOperation)


-- | Terms of the target language
data TTerm t where
    -- | Term of the source language
    ST        :: STerm a -> TTerm a
    -- | Linear operation
    LOp       :: LinearOperation a -> TTerm (LFun a RealN)
    --   Linear functions
    LId       :: TTerm (LFun a a)
    LComp     :: TTerm (LFun a b) -> TTerm (LFun b c) -> TTerm (LFun a c)
    LApp      :: TTerm (LFun a b) -> TTerm a -> TTerm b
    LEval     :: TTerm a -> TTerm (LFun (a -> b) b)
    -- Tuples
    LFst      :: TTerm ((a, b) -> a)
    LSnd      :: TTerm ((a, b) -> b)
    LPair     :: TTerm (LFun a b) -> TTerm (LFun a c) -> TTerm (LFun a (b, c))
    -- | Singleton
    Singleton :: TTerm a -> TTerm (LFun b (Tens a b))
    -- Zero
    Zero      :: LT a => TTerm a
    -- Plus
    Plus      :: LT a => TTerm a -> TTerm a -> TTerm a
    -- Swap
    LSwap     :: TTerm (a -> LFun b c) -> TTerm (LFun b (a -> c))
    -- | Tensor-elimination
    LCur      :: (LT a, LT b, LT c) => TTerm (a -> LFun b c) -> TTerm (LFun (Tens a b) c)

-- | Evaluate the target language
evalTt :: TTerm t -> t
evalTt (ST st)       = evalSt st
evalTt (LOp lop)     = undefined -- TODO
evalTt  LId          = id
evalTt (LComp f g)   = evalTt g . evalTt f
evalTt (LApp f a)    = evalTt f (evalTt a)
evalTt  LFst         = fst
evalTt  LSnd         = snd
evalTt (LPair a b)   = evalTt a &&& evalTt b
evalTt (Singleton t) = \x -> [(evalTt t, x)]
evalTt  Zero         = zero
evalTt (Plus a b)    = plus (evalTt a) (evalTt b)
evalTt (LSwap t)     = flip $ evalTt t
evalTt (LCur t)      = foldr f zero
    where f x acc = plus (uncurry (evalTt t) x) acc

