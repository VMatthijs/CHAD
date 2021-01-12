{-# LANGUAGE GADTs #-}
module Operation where

import Prelude hiding (sum, map, zipWith, length, replicate)
import Types (RealN)
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

-- | D op and D op^t of the Operators in the source language?
data LinearOperation a b where
    DEAdd  :: LinearOperation (RealN, RealN) RealN
    DEAddT :: LinearOperation RealN (RealN, RealN)

{-
[1 2 3 4 5] [5 4 3 2 1] = [30] = [15, 15]
++ =
[6 6 6 6 6]

|1|   |2x  |    |x|    |x^2 |    |x + x^2 |    | 1 + 2x |
|0| + |3x^2|  = |2|' + |x^3 |' = |2 + x^3 |' = | 3x^2   |
|0|   |4x  |    |1|    |2x^2|    |1 + 2x^2|    | 4x     |

-}

showLOp :: LinearOperation a b -> String
showLOp DEAdd = "DEadd"
showLOp DEAddT = "DEaddT"

evalLOp :: LinearOperation a b -> a -> b
evalLOp DEAdd  = \(a, b) -> fromList [sum a, sum b]
evalLOp DEAddT = \r      -> (singleton (sum r), singleton (sum r))
