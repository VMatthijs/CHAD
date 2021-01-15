{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
module Main where

import Prelude hiding (replicate)
import Control.Monad.State.Lazy
import Data.Maybe (fromMaybe)
import Data.Vector.Unboxed.Sized (Unbox, Vector, replicate, fromList)

import qualified SourceLanguage as SL
import qualified TargetLanguage as TL
import qualified ReverseAD as R
import qualified ForwardAD as F
import LanguageTypes
import Operation
import Types
import GHC.TypeNats


main :: IO ()
main = undefined


fromList' :: (KnownNat n, Unbox a) => [a] -> Vector n a
fromList' = fromMaybe (error "Incorrect vector size") . fromList

-- Constant
constVec :: (KnownNat n, LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a))
         => Double -> SL.STerm a (RealN n)
constVec x = SL.Comp SL.Unit (SL.Op (Constant (replicate x)))

-- c * x
cX :: Double -> SL.STerm (RealN 1) (RealN 1)
cX c = SL.Comp (SL.Pair cons SL.Id) (SL.Op EProd)
    where cons = constVec c

-- x^2
xSquared :: SL.STerm (RealN 1) (RealN 1)
xSquared = SL.Comp (SL.Pair SL.Id SL.Id) (SL.Op EProd)

-- c * x + x^2
quadratic :: Double -> SL.STerm (RealN 1) (RealN 1)
quadratic c = SL.Comp (SL.Pair (cX c) xSquared) (SL.Op EAdd)


mapQuadratic :: Double -> SL.STerm (RealN 3) (RealN 3)
mapQuadratic c = SL.Comp pair SL.Map
    where mapOp = SL.Curry $ SL.Comp SL.Snd (quadratic c)
          pair  = SL.Pair mapOp SL.Id

