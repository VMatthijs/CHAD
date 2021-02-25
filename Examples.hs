{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

module Examples where

import           Data.Maybe                (fromMaybe)
import qualified Data.Vector.Unboxed.Sized as V (Unbox, Vector, fromList, map,
                                                 replicate)
import           Prelude                   hiding (replicate)

import qualified ForwardAD                 as F
import           GHC.TypeNats              (KnownNat)
import           Helper
import           Operation                 (Operation (..))
import qualified ReverseAD                 as R
import           Simplify                  (simplifyTTerm)
import qualified SourceLanguage            as SL
import qualified TargetLanguage            as TL
import           Types

-- | Helper function to evaluate a derivative
evalDerivative :: (LT b, LT c) => TL.TTerm (a -> LFun b c) -> a -> b -> c
evalDerivative f a = lApp (TL.evalTt f a)

-- | Helper function to create a vector from a list
fromList' :: (KnownNat n, V.Unbox a) => [a] -> V.Vector n a
fromList' = fromMaybe (error "Incorrect vector size") . V.fromList

-- Constant
constant ::
     ( LT a
     , LT (Dr1 a)
     , LT (Df1 a)
     , LT (Dr2 a)
     , LT (Df2 a)
     , LT b
     , LT (Dr1 b)
     , LT (Df1 b)
     , LT (Dr2 b)
     , LT (Df2 b)
     , Show b
     , b ~ Df1 b
     , b ~ Dr1 b
     )
  => b
  -> SL.STerm a b
constant c = SL.Comp SL.Unit (SL.Op (Constant c))

-- c * x
cX :: Double -> SL.STerm Scal Scal
cX c = SL.Comp (SL.Pair cons SL.Id) (SL.Op EScalProd)
  where
    cons = constant c

-- x^2
xSquared :: SL.STerm Scal Scal
xSquared = SL.Comp (SL.Pair SL.Id SL.Id) (SL.Op EScalProd)

-- x^3
xCubed :: SL.STerm Scal Scal
xCubed = SL.Comp (SL.Pair xSquared SL.Id) (SL.Op EScalProd)

-- c * x + x^2
quadratic :: Double -> SL.STerm Scal Scal
quadratic c = SL.Comp (SL.Pair (cX c) xSquared) (SL.Op EScalAdd)

-- Map the quadratic function over an input vector
mapQuadratic :: Double -> SL.STerm (Vect 3) (Vect 3)
mapQuadratic c = SL.Comp pair SL.Map
  where
    mapOp = SL.Curry $ SL.Comp SL.Snd (quadratic c)
    pair = SL.Pair mapOp SL.Id

evalFwdDerivative ::
     ( LT a
     , LT (Dr1 a)
     , LT (Df1 a)
     , LT (Dr2 a)
     , LT (Df2 a)
     , LT b
     , LT (Dr1 b)
     , LT (Df1 b)
     , LT (Dr2 b)
     , LT (Df2 b)
     )
  => SL.STerm a b
  -> Df1 a
  -> Df2 a
  -> Df2 b
evalFwdDerivative f = evalDerivative (runAD F.d2 f)

evalRevDerivative ::
     ( LT a
     , LT (Dr1 a)
     , LT (Df1 a)
     , LT (Dr2 a)
     , LT (Df2 a)
     , LT b
     , LT (Dr1 b)
     , LT (Df1 b)
     , LT (Dr2 b)
     , LT (Df2 b)
     )
  => SL.STerm a b
  -> Dr1 a
  -> Dr2 b
  -> Dr2 a
evalRevDerivative f = evalDerivative (runAD R.d2 f)

evalFwdFinDiff :: (LT a, LT b) => SL.STerm a b -> a -> a -> b
evalFwdFinDiff f x y =
  (SL.evalSt f (x `plus` (delta `scalProd` y)) `minus` SL.evalSt f x) `scalDiv`
  delta
  where
    delta = 0.0000001

evalRevFinDiff :: (LT a, LT b) => SL.STerm a b -> Dr1 a -> Dr2 b -> Dr2 a
evalRevFinDiff f = undefined

evalFwd ::
     ( LT a
     , LT (Dr1 a)
     , LT (Df1 a)
     , LT (Dr2 a)
     , LT (Df2 a)
     , LT b
     , LT (Dr1 b)
     , LT (Df1 b)
     , LT (Dr2 b)
     , LT (Df2 b)
     )
  => SL.STerm a b
  -> Df1 a
  -> Df1 b
evalFwd f = TL.evalTt (runAD F.d1 f)

evalRev ::
     ( LT a
     , LT (Dr1 a)
     , LT (Df1 a)
     , LT (Dr2 a)
     , LT (Df2 a)
     , LT b
     , LT (Dr1 b)
     , LT (Df1 b)
     , LT (Dr2 b)
     , LT (Df2 b)
     )
  => SL.STerm a b
  -> Dr1 a
  -> Dr1 b
evalRev f = TL.evalTt (runAD R.d1 f)

fwdDerMapQuadratic :: Vect 3 -> Vect 3 -> Vect 3
fwdDerMapQuadratic = evalFwdDerivative (mapQuadratic 42) --OK

revDerMapQuadratic :: Vect 3 -> Vect 3 -> Vect 3
revDerMapQuadratic = evalRevDerivative (mapQuadratic 42) --OK

fwdDerQuadratic :: Scal -> Scal -> Scal
fwdDerQuadratic = evalFwdDerivative (quadratic 42) -- OK

revDerQuadratic :: Scal -> Scal -> Scal
revDerQuadratic = evalRevDerivative (quadratic 42) -- OK

slid :: SL.STerm Scal Scal -- OK
slid = SL.Id

fwdDerId :: Scal -> Scal -> Scal -- OK
fwdDerId = evalFwdDerivative slid

revDerId :: Scal -> Scal -> Scal -- OK
revDerId = evalRevDerivative slid

pair :: SL.STerm Scal (Scal, Scal) -- OK
pair = SL.Pair SL.Id SL.Id

fwdDerPair :: Scal -> Scal -> (Scal, Scal) -- OK
fwdDerPair = evalFwdDerivative pair

revDerPair :: Scal -> (Scal, Scal) -> Scal -- OK
revDerPair = evalRevDerivative pair

add :: SL.STerm (Scal, Scal) Scal -- OK
add = SL.Op EScalAdd

fwdDerAdd :: (Scal, Scal) -> (Scal, Scal) -> Scal -- OK
fwdDerAdd = evalFwdDerivative add

revDerAdd :: (Scal, Scal) -> Scal -> (Scal, Scal) -- OK
revDerAdd = evalRevDerivative add

prod :: SL.STerm (Scal, Scal) Scal -- OK
prod = SL.Op EScalProd

fwdDerProd :: (Scal, Scal) -> (Scal, Scal) -> Scal -- OK
fwdDerProd = evalFwdDerivative prod

revDerProd :: (Scal, Scal) -> Scal -> (Scal, Scal) -- OK
revDerProd = evalRevDerivative prod

addCopy :: SL.STerm (Scal, Scal) (Scal, Scal) -- OK
addCopy = SL.Comp add pair

fwdDerAddCopy :: (Scal, Scal) -> (Scal, Scal) -> (Scal, Scal) -- OK
fwdDerAddCopy = evalFwdDerivative addCopy

revDerAddCopy :: (Scal, Scal) -> (Scal, Scal) -> (Scal, Scal) -- OK
revDerAddCopy = evalRevDerivative addCopy

fwdAddCopy :: (Scal, Scal) -> (Scal, Scal) -- OK
fwdAddCopy = evalFwd addCopy

revAddCopy :: (Scal, Scal) -> (Scal, Scal) -- OK
revAddCopy = evalRev addCopy

foldProd :: KnownNat n => SL.STerm (Vect n) Scal -- OK
foldProd =
  SL.Comp
    (SL.Pair
       (SL.Pair (SL.Curry (SL.Comp SL.Snd (SL.Op EScalProd))) (constant 1))
       SL.Id)
    SL.Foldr

foldProd' :: (Vect 3) -> Scal -- OK
foldProd' = SL.evalSt foldProd

fwdFoldProd :: (Vect 3) -> Scal -- OK
fwdFoldProd = evalFwd foldProd

revFoldProd :: (Vect 3) -> Scal -- OK
revFoldProd = evalFwd foldProd

fwdDerFoldProd :: (Vect 3) -> Vect 3 -> Scal -- OK
fwdDerFoldProd = evalFwdDerivative foldProd

revDerFoldProd :: (Vect 3) -> Scal -> Vect 3 -- OK
revDerFoldProd = evalRevDerivative foldProd

finFwdDiffFoldProd :: (Vect 3) -> Vect 3 -> Scal -- OK
finFwdDiffFoldProd = evalFwdFinDiff foldProd

finRevDiffFoldProd :: (Vect 3) -> Scal -> Vect 3 -- OK
finRevDiffFoldProd x y =
  V.map
    partial
    (fromList' [fromList' [1, 0, 0], fromList' [0, 1, 0], fromList' [0, 0, 1]])
  where
    delta = 0.000001
    partial z =
      y * (fwdFoldProd (x + V.map (* delta) z) - fwdFoldProd x) / delta
