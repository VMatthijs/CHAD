{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

module Examples where

import           Data.Maybe                (fromMaybe)
import qualified Data.Vector.Unboxed.Sized as V (Unbox, Vector, fromList, map,
                                                 replicate)
import           Prelude                   hiding (replicate)

import           Control.Monad.State.Lazy  (State, modify, runState)
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
revFoldProd = evalRev foldProd

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

foldProd2 :: SL.STerm Scal Scal
foldProd2 =
  SL.Comp
    (SL.Pair
       (SL.Pair (SL.Curry (SL.Comp SL.Snd (SL.Op EScalProd))) SL.Id)
       (constant v))
    SL.Foldr
  where
    v :: Vect 3
    v = (fromList' [1, 2, 3])

fwdFinDiffFoldProd2 :: Scal -> Scal -> Scal -- OK
fwdFinDiffFoldProd2 = evalFwdFinDiff foldProd2

fwdDerFoldProd2 :: Scal -> Scal -> Scal -- OK
fwdDerFoldProd2 = evalFwdDerivative foldProd2

revDerFoldProd2 :: Scal -> Scal -> Scal -- OK
revDerFoldProd2 = evalRevDerivative foldProd2

realCase ::
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
  => SL.STerm a (Either () ())
  -> SL.STerm a b
  -> SL.STerm a b
  -> SL.STerm a b
realCase c l r =
  SL.Comp
    (SL.Pair
       (SL.Comp
          c
          (SL.CoPair (SL.Curry (SL.Comp SL.Snd l)) (SL.Curry (SL.Comp SL.Snd r))))
       SL.Id)
    SL.Ev

fact :: SL.STerm Scal Scal
fact =
  SL.Comp
    (SL.Pair SL.Unit (SL.Pair SL.Id (constant 1)))
    (SL.It
       (realCase
          (SL.Comp (SL.Comp SL.Snd SL.Fst) SL.Sign)
          (SL.Comp (SL.Comp SL.Snd SL.Snd) SL.Inl)
          (SL.Comp
             (SL.Pair
                (SL.Comp
                   (SL.Pair (SL.Comp SL.Snd SL.Fst) (constant 1))
                   (SL.Op EScalSubt))
                (SL.Comp
                   (SL.Pair (SL.Comp SL.Snd SL.Fst) (SL.Comp SL.Snd SL.Snd))
                   (SL.Op EScalProd)))
             SL.Inr)))

fact' :: Scal -> Scal -- OK!
fact' = SL.evalSt fact

fwdFinDiffFact :: Scal -> Scal -> Scal
fwdFinDiffFact = evalFwdFinDiff fact

fwdDerFact :: Scal -> Scal -> Scal -- OK!
fwdDerFact = evalFwdDerivative fact

revDerFact :: Scal -> Scal -> Scal -- OK!
revDerFact = evalRevDerivative fact

factExtra :: SL.STerm (Scal, Scal) Scal -- to test derivative of parameterized iteration w.r.t. parameter
factExtra =
  SL.Comp
    (SL.Pair SL.Unit SL.Id)
    (SL.It
       (realCase
          (SL.Comp (SL.Comp SL.Snd SL.Fst) SL.Sign)
          (SL.Comp (SL.Comp SL.Snd SL.Snd) SL.Inl)
          (SL.Comp
             (SL.Pair
                (SL.Comp
                   (SL.Pair (SL.Comp SL.Snd SL.Fst) (constant 1))
                   (SL.Op EScalSubt))
                (SL.Comp
                   (SL.Pair (SL.Comp SL.Snd SL.Fst) (SL.Comp SL.Snd SL.Snd))
                   (SL.Op EScalProd)))
             SL.Inr)))

factExtra' :: (Scal, Scal) -> Scal
factExtra' = SL.evalSt factExtra

fwdFinDiffFactExtra :: (Scal, Scal) -> (Scal, Scal) -> Scal
fwdFinDiffFactExtra = evalFwdFinDiff factExtra

fwdDerFactExtra :: (Scal, Scal) -> (Scal, Scal) -> Scal -- OK
fwdDerFactExtra = evalFwdDerivative factExtra

revDerFactExtra :: (Scal, Scal) -> Scal -> (Scal, Scal) -- OK
revDerFactExtra = evalRevDerivative factExtra

revFinDiffFactExtra :: (Scal, Scal) -> Scal -> (Scal, Scal)
revFinDiffFactExtra (x, x') y =
  ( (factExtra' (x + y * delta, x') - factExtra' (x, x')) / delta
  , (factExtra' (x, x' + y * delta) - factExtra' (x, x')) / delta)
  where
    delta = 0.000001

fact2 :: SL.STerm Scal Scal
fact2 =
  SL.Pair
    ((constant 1) `SL.Comp`
     (SL.Rec
        (SL.Curry
           (realCase
              (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt `SL.Comp`
               SL.Sign)
              (SL.Fst `SL.Comp` SL.Fst)
              (SL.Pair
                 SL.Snd
                 (SL.Pair
                    (SL.Fst `SL.Comp` SL.Snd)
                    (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt) `SL.Comp`
                  SL.Ev) `SL.Comp`
               (SL.Op EScalProd))))))
    SL.Id `SL.Comp`
  SL.Ev

fact2' :: Scal -> Scal -- OK
fact2' = SL.evalSt fact2

fwdFinDiffFact2 :: Scal -> Scal -> Scal
fwdFinDiffFact2 = evalFwdFinDiff fact2

fwdDerFact2 :: Scal -> Scal -> Scal -- OK!
fwdDerFact2 = evalFwdDerivative fact2

revDerFact2 :: Scal -> Scal -> Scal -- OK!
revDerFact2 = evalRevDerivative fact2

fact2Extra :: SL.STerm (Scal, Scal) Scal -- to test derivative of parameterized recursion w.r.t. parameter
fact2Extra =
  SL.Pair
    (SL.Snd `SL.Comp`
     SL.Rec
       (SL.Curry
          (realCase
             (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt `SL.Comp`
              SL.Sign)
             (SL.Fst `SL.Comp` SL.Fst)
             (SL.Pair
                SL.Snd
                (SL.Pair
                   (SL.Fst `SL.Comp` SL.Snd)
                   (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt) `SL.Comp`
                 SL.Ev) `SL.Comp`
              (SL.Op EScalProd)))))
    SL.Fst `SL.Comp`
  SL.Ev

fact2Extra' :: (Scal, Scal) -> Scal -- OK
fact2Extra' = SL.evalSt fact2Extra

fwdFinDiffFact2Extra :: (Scal, Scal) -> (Scal, Scal) -> Scal
fwdFinDiffFact2Extra = evalFwdFinDiff fact2Extra

fwdDerFact2Extra :: (Scal, Scal) -> (Scal, Scal) -> Scal -- OK!
fwdDerFact2Extra = evalFwdDerivative fact2Extra

revDerFact2Extra :: (Scal, Scal) -> Scal -> (Scal, Scal) -- OK!
revDerFact2Extra = evalRevDerivative fact2Extra

revFinDiffFact2Extra :: (Scal, Scal) -> Scal -> (Scal, Scal)
revFinDiffFact2Extra (x, x') y =
  ( (fact2Extra' (x + y * delta, x') - fact2Extra' (x, x')) / delta
  , (fact2Extra' (x, x' + y * delta) - fact2Extra' (x, x')) / delta)
  where
    delta = 0.000001

recurse :: ((a, c) -> c) -> (a -> c)
recurse f a = f (a, recurse f a)

branch2 :: Scal -> Scal
branch2 =
  recurse
    (\(r, g) ->
       \n ->
         if n > 1
           then n * g (n - 1) * g (n * 0.5)
           else r)
    1

branch :: SL.STerm Scal Scal
branch =
  SL.Pair
    ((constant 1) `SL.Comp`
     (SL.Rec
        (SL.Curry
           (realCase
              (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt `SL.Comp`
               SL.Sign)
              (SL.Fst `SL.Comp` SL.Fst)
              (SL.Pair
                 (SL.Pair
                    SL.Snd
                    (SL.Pair
                       (SL.Fst `SL.Comp` SL.Snd)
                       (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt) `SL.Comp`
                     SL.Ev) `SL.Comp`
                  (SL.Op EScalProd))
                 (SL.Pair
                    (SL.Fst `SL.Comp` SL.Snd)
                    (SL.Pair SL.Snd (constant 0.5) `SL.Comp` SL.Op EScalProd) `SL.Comp`
                  SL.Ev) `SL.Comp`
               (SL.Op EScalProd))))))
    SL.Id `SL.Comp`
  SL.Ev

branch' :: Scal -> Scal -- OK
branch' = SL.evalSt branch

fwdFinDiffBranch :: Scal -> Scal -> Scal
fwdFinDiffBranch = evalFwdFinDiff branch

fwdDerBranch :: Scal -> Scal -> Scal -- OK!
fwdDerBranch = evalFwdDerivative branch

revDerBranch :: Scal -> Scal -> Scal -- OK!
revDerBranch = evalRevDerivative branch

branch2extra :: (Scal, Scal) -> Scal
branch2extra (r', n') =
  recurse
    (\(r, g) ->
       \n ->
         if n > 1
           then n * g (n - 1) * g (n * 0.5)
           else r)
    n'
    r'

branchExtra :: SL.STerm (Scal, Scal) Scal
branchExtra =
  SL.Pair
    (SL.Snd `SL.Comp`
     (SL.Rec
        (SL.Curry
           (realCase
              (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt `SL.Comp`
               SL.Sign)
              (SL.Fst `SL.Comp` SL.Fst)
              (SL.Pair
                 (SL.Pair
                    SL.Snd
                    (SL.Pair
                       (SL.Fst `SL.Comp` SL.Snd)
                       (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt) `SL.Comp`
                     SL.Ev) `SL.Comp`
                  (SL.Op EScalProd))
                 (SL.Pair
                    (SL.Fst `SL.Comp` SL.Snd)
                    (SL.Pair SL.Snd (constant 0.5) `SL.Comp` SL.Op EScalProd) `SL.Comp`
                  SL.Ev) `SL.Comp`
               (SL.Op EScalProd))))))
    SL.Fst `SL.Comp`
  SL.Ev

branchExtra' :: (Scal, Scal) -> Scal -- OK
branchExtra' = SL.evalSt branchExtra

fwdFinDiffBranchExtra :: (Scal, Scal) -> (Scal, Scal) -> Scal
fwdFinDiffBranchExtra = evalFwdFinDiff branchExtra

fwdDerBranchExtra :: (Scal, Scal) -> (Scal, Scal) -> Scal -- OK!
fwdDerBranchExtra = evalFwdDerivative branchExtra

revDerBranchExtra :: (Scal, Scal) -> Scal -> (Scal, Scal) -- OK!
revDerBranchExtra = evalRevDerivative branchExtra

revFinDiffBranchExtra :: (Scal, Scal) -> Scal -> (Scal, Scal)
revFinDiffBranchExtra (x, x') y =
  ( (branchExtra' (x + y * delta, x') - branchExtra' (x, x')) / delta
  , (branchExtra' (x, x' + y * delta) - branchExtra' (x, x')) / delta)
  where
    delta = 0.000001
