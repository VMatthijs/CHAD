{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Definition of the different supported operators
module Operation where

import           Data.Vector.Unboxed.Sized (zipWith)
import           GHC.TypeNats              (KnownNat)
import           Prelude                   hiding (sum, zipWith)

import           Types                     (LFun, LT, LT2, Scal, Vect,
                                            lExpand, lProd, lNeg)

-- | Possible operators in the source language
data Operation a b where
  Constant :: (Show b, LT b, LT2 b) => b -> Operation () b
  EAdd :: KnownNat n => Operation (Vect n, Vect n) (Vect n)
  EProd :: KnownNat n => Operation (Vect n, Vect n) (Vect n)
  EScalAdd :: Operation (Scal, Scal) Scal
  EScalSubt :: Operation (Scal, Scal) Scal
  EScalProd :: Operation (Scal, Scal) Scal
  EScalSin :: Operation Scal Scal
  EScalCos :: Operation Scal Scal

deriving instance Show (Operation a b)

showOp :: Operation a b -> String
showOp (Constant c) = "const(" ++ show c ++ ")"
showOp EAdd         = "EAdd"
showOp EProd        = "EProd"
showOp EScalAdd     = "EScalAdd"
showOp EScalSubt    = "EScalSubt"
showOp EScalProd    = "EScalProd"
showOp EScalSin     = "EScalSin"
showOp EScalCos     = "EScalCos"

-- | Evaluate an operator
evalOp :: Operation a b -> a -> b
evalOp (Constant c) = const c
evalOp EAdd         = uncurry $ zipWith (+)
evalOp EProd        = uncurry $ zipWith (*)
evalOp EScalAdd     = uncurry (+)
evalOp EScalSubt    = uncurry (-)
evalOp EScalProd    = uncurry (*)
evalOp EScalSin     = sin
evalOp EScalCos     = cos

-- | @a -> LFun b c@
data LinearOperation a b c where
  LProd :: KnownNat n => LinearOperation (Vect n) (Vect n) (Vect n)
  LReplicate :: KnownNat n => LinearOperation () Scal (Vect n)
  LScalNeg :: LinearOperation () Scal Scal
  LScalProd :: LinearOperation Scal Scal Scal

deriving instance Show (LinearOperation a b c)

showLOp :: LinearOperation a b c -> String
showLOp LProd = "lprod"
showLOp LReplicate = "lreplicate"
showLOp LScalNeg = "lscalneg"
showLOp LScalProd = "lscalprod"

-- | Evaluate the linear operators
evalLOp :: LinearOperation a b c -> a -> LFun b c
evalLOp LProd = lProd
evalLOp LReplicate = const lExpand
evalLOp LScalNeg = const lNeg
evalLOp LScalProd = lProd
