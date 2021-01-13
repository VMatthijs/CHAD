{-# LANGUAGE GADTs #-}
module Operation where

import Prelude hiding (sum, map, zipWith, length, replicate)
import Types (LFun, RealN)
import Data.Vector


-- | Possible operators in the source language
data Operation i where
    Constant :: RealN -> Operation ()
    EAdd     :: Operation (RealN, RealN)
    EProd    :: Operation (RealN, RealN)
    MProd    :: Operation (RealN, RealN)
    Sum      :: Operation  RealN
    Sigmoid  :: Operation  RealN
    DSigmoid :: Operation  RealN
    -- Map      :: Operation (Double -> Double, RealN)

showOp :: Operation i -> String
showOp (Constant c) = "const"
showOp  EAdd        = "EAdd"
showOp  EProd       = "EProd"
showOp  MProd       = "MProd"
showOp  Sum         = "Sum"
showOp  Sigmoid     = "Sigmoid"
showOp  DSigmoid    = "DSigmoid"

evalOp :: Operation i -> i -> RealN
evalOp (Constant c) = const c
evalOp  EAdd        = uncurry $ zipWith (+)
evalOp  EProd       = uncurry $ zipWith (*)
evalOp  MProd       = undefined
evalOp  Sum         = singleton . sum
evalOp  Sigmoid     = map sigmoid
evalOp  DSigmoid    = map dsigmoid


sigmoid :: Double -> Double
sigmoid x = 1.0 / (1.0 + exp (negate x))

dsigmoid :: Double -> Double
dsigmoid x = (sigmoid x) * (1 - sigmoid x)

-- | D op and D op^t of the Operators in the source language
data LinearOperation a b c where
    DEAdd   :: LinearOperation (RealN, RealN) (RealN, RealN)  RealN
    DEAddT  :: LinearOperation (RealN, RealN)  RealN         (RealN, RealN)
    DEProd  :: LinearOperation (RealN, RealN) (RealN, RealN)  RealN
    DEProdT :: LinearOperation (RealN, RealN)  RealN         (RealN, RealN)


showLOp :: LinearOperation a b c -> String
showLOp DEAdd   = "DEadd"
showLOp DEAddT  = "DEaddT"
showLOp DEProd  = "DEProd"
showLOp DEProdT = "DEProdT"


evalLOp :: LinearOperation a b c -> a -> LFun b c
evalLOp DEAdd   (_x, _y) (a, b) = zipWith (+) a b
evalLOp DEAddT  (_x, _y)  r     = (r, r)
evalLOp DEProd  ( x,  y) (a, b) = zipWith (+) xDeriv yDeriv
    where xDeriv = zipWith (*) y a
          yDeriv = zipWith (*) x b
evalLOp DEProdT ( x,  y)  r     = (xDeriv, yDeriv)
    where xDeriv = zipWith (*) y r
          yDeriv = zipWith (*) x r
