{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
-- | Definition of the different supported operators
module Operation where

import Prelude hiding (sum, zipWith, replicate)
import Data.Vector.Unboxed.Sized (replicate, singleton, sum, zipWith)
import GHC.TypeNats (KnownNat)


import Types ( LFun, RealN, lComp, lConst, lDup, lZipWith, lAdd, lUncurry
             , lProd, lMapTuple, lPair, lSum, lExpand
             )


-- | Possible operators in the source language
data Operation a b where
    Constant :: KnownNat n => RealN n -> Operation () (RealN n)
    EAdd     :: Operation (RealN n, RealN n) (RealN n)
    EProd    :: Operation (RealN n, RealN n) (RealN n)
    Sum      :: KnownNat n => Operation (RealN n) (RealN 1)


showOp :: Operation a b -> String
showOp (Constant c) = "const(" ++ show c ++ ")"
showOp  EAdd        = "EAdd"
showOp  EProd       = "EProd"
showOp  Sum         = "Sum"

-- | Evaluate an operator
evalOp :: Operation a b -> a -> b
evalOp (Constant c) = const c
evalOp  EAdd        = uncurry $ zipWith (+)
evalOp  EProd       = uncurry $ zipWith (*)
evalOp  Sum         = singleton . sum


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
showLOp DEAdd       = "DEAdd"
showLOp DEAddT      = "DEAddT"
showLOp DEProd      = "DEProd"
showLOp DEProdT     = "DEProdT"

-- | Evaluate the linear operators
evalLOp :: LinearOperation a b c -> a -> LFun b c
evalLOp DConstant  ()       = lConst $ replicate 0
evalLOp DConstantT ()       = lConst ()
evalLOp DEAdd      (_x, _y) = lUncurry $ lZipWith lAdd
evalLOp DEAddT     (_x, _y) = lDup
evalLOp DEProd     ( x,  y) = lComp (lMapTuple xDeriv yDeriv) (lUncurry (lZipWith lAdd))
    where xDeriv = lZipWith lProd y
          yDeriv = lZipWith lProd x
evalLOp DEProdT    ( x,  y) = lPair xDeriv yDeriv
    where xDeriv = lZipWith lProd y
          yDeriv = lZipWith lProd x
-- Jacobian: 1xn [1, 1, 1, ...]
evalLOp DSum        _x      = lSum
evalLOp DSumT       _x      = lExpand
