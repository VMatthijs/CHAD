{-# LANGUAGE GADTs #-}
module Operation where

import Prelude hiding (sum, map, zipWith)
import LanguageTypes (RealN)
import Data.Vector (sum, singleton, map, zipWith)


-- | Possible operators in the source language
data Operation i where
    Constant :: RealN -> Operation ()
    EAdd     :: Operation (RealN, RealN)
    EProd    :: Operation (RealN, RealN)
    MProd    :: Operation (RealN, RealN)
    Sum      :: Operation  RealN
    Sigmoid  :: Operation  RealN
    -- Map      :: Operation (Double -> Double, RealN)

evalOp :: Operation i -> i -> RealN
evalOp (Constant c) = const c
evalOp  EAdd        = uncurry $ zipWith (+)
evalOp  EProd       = uncurry $ zipWith (*)
evalOp  MProd       = undefined
evalOp  Sum         = singleton . sum
evalOp  Sigmoid     = map sigmoid


sigmoid :: Double -> Double
sigmoid x = 1.0 / (1.0 + exp (negate x))

-- | D op and D op^t of the Operators in the source language?
data LinearOperation i where

