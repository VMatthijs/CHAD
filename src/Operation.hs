{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
-- | Definition of the different supported operators
module Operation where

import Prelude hiding (sum, zipWith, replicate)
import Data.Vector.Unboxed.Sized (replicate, sum, zipWith)
import GHC.TypeNats (KnownNat)


import Types ( LFun, Vect, Scal, lComp, lConst, lDup, lZipWith, lAdd, lUncurry
             , lProd, lMapTuple, lPair, lSum, lExpand
             )


-- | Possible operators in the source language
data Operation a b where
    Constant :: KnownNat n => Vect n -> Operation () (Vect n)
    EAdd     :: KnownNat n => Operation (Vect n, Vect n) (Vect n)
    EProd    :: KnownNat n => Operation (Vect n, Vect n) (Vect n)
    EScalAdd :: Operation (Scal, Scal) Scal
    EScalProd :: Operation (Scal, Scal) Scal
    Sum      :: KnownNat n => Operation (Vect n) Scal


showOp :: Operation a b -> String
showOp (Constant c) = "const(" ++ show c ++ ")"
showOp  EAdd        = "EAdd"
showOp  EProd       = "EProd"
showOp  EScalAdd    = "EAScaldd"
showOp  EScalProd   = "EScalProd"
showOp  Sum         = "Sum"

-- | Evaluate an operator
evalOp :: Operation a b -> a -> b
evalOp (Constant c) = const c
evalOp  EAdd        = uncurry $ zipWith (+)
evalOp  EProd       = uncurry $ zipWith (*)
evalOp  EScalAdd    = uncurry (+)
evalOp  EScalProd   = uncurry (*)
evalOp  Sum         = sum


-- | D op and D op^t of the Operators in the source language
data LinearOperation a b c where
    DConstant  :: KnownNat n
               => LinearOperation ()                 ()                  (Vect n)
    DConstantT :: LinearOperation ()                 (Vect n)           ()
    DEAdd      :: KnownNat n => LinearOperation (Vect n, Vect n) (Vect n, Vect n)  (Vect n)
    DEAddT     :: KnownNat n => LinearOperation (Vect n, Vect n) (Vect n)           (Vect n, Vect n)
    DEProd     :: KnownNat n => LinearOperation (Vect n, Vect n) (Vect n, Vect n)  (Vect n)
    DEProdT    :: KnownNat n => LinearOperation (Vect n, Vect n) (Vect n)           (Vect n, Vect n)
    DEScalAdd  :: LinearOperation (Scal, Scal) (Scal, Scal) Scal 
    DEScalAddT :: LinearOperation (Scal, Scal) Scal (Scal, Scal) 
    DEScalProd :: LinearOperation (Scal, Scal) (Scal, Scal) Scal 
    DEScalProdT :: LinearOperation (Scal, Scal) Scal (Scal, Scal)
    DSum       :: KnownNat n => LinearOperation (Vect n)          (Vect n)           Scal
    DSumT      :: KnownNat n
               => LinearOperation (Vect n)          Scal           (Vect n)


showLOp :: LinearOperation a b c -> String
showLOp DConstant   = "DConstant"
showLOp DConstantT  = "DConstantT"
showLOp DEAdd       = "DEAdd"
showLOp DEAddT      = "DEAddT"
showLOp DEProd      = "DEProd"
showLOp DEProdT     = "DEProdT"
showLOp DEScalAdd   = "DEScalAdd"
showLOp DEScalAddT  = "DEScalAddT"
showLOp DEScalProd  = "DEScalProd"
showLOp DEScalProdT = "DEScalProdT"
showLOp DSum        = "DSum"
showLOp DSumT       = "DSumT"

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
evalLOp DEScalAdd (_, _)    = lUncurry lAdd
evalLOp DEScalAddT (_, _)   = lDup
evalLOp DEScalProd (x, y)   = lComp (lMapTuple xDeriv yDeriv) (lUncurry lAdd)
    where xDeriv = lProd y
          yDeriv = lProd x
evalLOp DEScalProdT ( x,  y) = lPair xDeriv yDeriv
    where xDeriv = lProd y
          yDeriv = lProd x
-- Jacobian: 1xn [1, 1, 1, ...]
evalLOp DSum        _x      = lSum
evalLOp DSumT       _x      = lExpand
