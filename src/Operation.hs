{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Operation where

import Prelude hiding (sum, map, zipWith, length, replicate)
import Data.Vector.Unboxed.Sized (map, replicate, singleton, sum, zipWith, index)
import GHC.TypeNats as TN


import Types (LFun(..), RealN)


-- | Possible operators in the source language
data Operation a b where
    Constant :: KnownNat n => RealN n -> Operation () (RealN n)
    EAdd     :: Operation (RealN n, RealN n) (RealN n)
    EProd    :: Operation (RealN n, RealN n) (RealN n)
    MProd    :: (KnownNat n, KnownNat m)
             => Operation (RealN (n TN.* m), RealN m) (RealN n)
    Sum      :: KnownNat n => Operation (RealN n) (RealN 1)
    Sigmoid  :: Operation (RealN 1) (RealN 1)


showOp :: Operation a b -> String
showOp (Constant c) = "const(" ++ show c ++ ")"
showOp  EAdd        = "EAdd"
showOp  EProd       = "EProd"
showOp  MProd       = "MProd"
showOp  Sum         = "Sum"
showOp  Sigmoid     = "Sigmoid"

evalOp :: Operation a b -> a -> b
evalOp (Constant c) = const c
evalOp  EAdd        = uncurry $ zipWith (+)
evalOp  EProd       = uncurry $ zipWith (*)
evalOp  MProd       = undefined
evalOp  Sum         = singleton . sum
evalOp  Sigmoid     = map sigmoid


sigmoid :: Double -> Double
sigmoid x = 1.0 / (1.0 + exp (negate x))

dsigmoid :: Double -> Double
dsigmoid x = (sigmoid x) * (1 - sigmoid x)

-- | D op and D op^t of the Operators in the source language
data LinearOperation a b c where
    DConstant  :: KnownNat n
               => LinearOperation ()                 ()                  (RealN n)
    DConstantT :: LinearOperation ()                 (RealN n)           ()
    DEAdd      :: LinearOperation (RealN n, RealN n) (RealN n, RealN n)  (RealN n)
    DEAddT     :: LinearOperation (RealN n, RealN n) (RealN n)           (RealN n, RealN n)
    DEProd     :: LinearOperation (RealN n, RealN n) (RealN n, RealN n)  (RealN n)
    DEProdT    :: LinearOperation (RealN n, RealN n) (RealN n)           (RealN n, RealN n)
    DSum       :: LinearOperation (RealN n)          (RealN n)           (RealN 1)
    DSumT      :: KnownNat n
               => LinearOperation (RealN n)          (RealN 1)           (RealN n)


showLOp :: LinearOperation a b c -> String
showLOp DConstant   = "DConstant"
showLOp DConstantT  = "DConstantT"
showLOp DEAdd       = "DEadd"
showLOp DEAddT      = "DEaddT"
showLOp DEProd      = "DEProd"
showLOp DEProdT     = "DEProdT"


evalLOp :: LinearOperation a b c -> a -> LFun b c
evalLOp DConstant  ()       = LFun $ \() -> replicate 0
evalLOp DConstantT ()       = LFun $ const ()
evalLOp DEAdd      (_x, _y) = LFun $ uncurry $ zipWith (+)
evalLOp DEAddT     (_x, _y) = LFun $ \r -> (r, r)
evalLOp DEProd     ( x,  y) = LFun $ \(a, b) -> zipWith (+) (xDeriv a) (yDeriv b)
    where xDeriv a = zipWith (*) y a
          yDeriv b = zipWith (*) x b
evalLOp DEProdT    ( x,  y) = LFun $ \r -> (xDeriv r, yDeriv r)
    where xDeriv r = zipWith (*) y r
          yDeriv r = zipWith (*) x r
-- Jacobian: 1xn [1, 1, 1, ...]
evalLOp DSum        _x      = LFun $ singleton . sum
evalLOp DSumT       _x      = LFun $ \r -> replicate $ index r 0
