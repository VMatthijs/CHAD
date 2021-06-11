{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableSuperClasses   #-}
{-# OPTIONS -Wno-orphans #-} -- for Arbitrary

module Test where

import           Data.List                 (mapAccumL)
import           Data.Maybe
import           Data.Tuple                (swap)
import qualified Data.Vector.Unboxed.Sized as V
import           GHC.TypeLits              (KnownNat, SomeNat (..), someNatVal)
import           Test.Tasty
import           Test.Tasty.QuickCheck

import qualified Examples                  as E
import qualified ForwardAD                 as F
import qualified ReverseAD                 as R
import qualified SourceLanguage            as SL
import qualified TargetLanguage            as TL
import           Types

class LT a =>
      FinDiff a
  where
  type Element a
  -- Takes primal value
  oneHotVecs :: a -> [a]
  -- Input should have same length as oneHotVecs
  rebuild :: a -> [Element a] -> a
  rebuild primal l =
    case rebuild' primal l of
      (res, []) -> res
      _         -> error "rebuild: Invalid length"
  rebuild' :: a -> [Element a] -> (a, [Element a]) -- returns excess
  dotprod :: a -> a -> Element a
  genWithPrimal :: a -> Gen a
  -- Helper methods for finite differencing on numeric-like types
  scalProd :: Scal -> a -> a
  scalDiv :: a -> Scal -> a
  minus :: a -> a -> a

instance FinDiff Scal where
  type Element Scal = Scal
  oneHotVecs _ = [1]
  rebuild' _ (x:xs) = (x, xs)
  rebuild' _ []     = error "rebuild: Invalid length"
  dotprod = (*)
  genWithPrimal _ = arbitrary
  scalProd = (*)
  scalDiv = (/)
  minus = (-)

instance KnownNat n => FinDiff (Vect n) where
  type Element (Vect n) = Scal
  oneHotVecs primal =
    [ V.generate
      (\k ->
         if k == i
           then itemvec
           else zero)
    | i <- [minBound .. maxBound]
    , itemvec <- oneHotVecs (primal `V.index` i)
    ]
  rebuild' primal l =
    let result =
          mapAccumL (\l' prim -> swap (rebuild' prim l')) l (V.toList primal)
     in swap (fromJust . V.fromList <$> result)
  dotprod u v = V.sum (V.zipWith dotprod u v)
  genWithPrimal _ = genVect
  scalProd r = V.map (* r)
  scalDiv v r = V.map (/ r) v
  minus = V.zipWith (-)

instance (FinDiff a, FinDiff b, Element a ~ Element b, Element a ~ Scal) =>
         FinDiff (a, b) where
  type Element (a, b) = Element a
  oneHotVecs (x, y) = map (, zero) (oneHotVecs x) ++ map (zero, ) (oneHotVecs y)
  rebuild' (x, y) l =
    let (a, l') = rebuild' x l
        (b, l'') = rebuild' y l'
     in ((a, b), l'')
  dotprod (a, b) (c, d) = dotprod a c + dotprod b d
  genWithPrimal (x, y) = (,) <$> genWithPrimal x <*> genWithPrimal y
  scalProd r a = (scalProd r (fst a), scalProd r (snd a))
  scalDiv a r = (scalDiv (fst a) r, scalDiv (snd a) r)
  minus a b = (fst a `minus` fst b, snd a `minus` snd b)

instance FinDiff () where
  type Element () = ()
  oneHotVecs _ = [()]
  rebuild' _ l = ((), l)
  dotprod _ _ = ()
  genWithPrimal _ = return ()
  scalProd _ _ = ()
  scalDiv _ _ = ()
  minus _ _ = ()

instance KnownNat n => Arbitrary (Vect n) where
  arbitrary = genVect

genVect :: KnownNat n => Gen (Vect n)
genVect = V.generateM (const arbitrary)

data SomeVect =
  forall n. SomeVect (Vect n)

genSomeVect :: Int -> Gen SomeVect
genSomeVect len =
  case someNatVal (fromIntegral len) of
    Just (SomeNat n) -> SomeVect <$> V.replicateM' n arbitrary
    _                -> error "Negative length in genSomeVect"

-- Minimum of the relative difference and the absolute difference
relAbsDiff :: Scal -> Scal -> Scal
relAbsDiff x y = abs (x - y) / max 1 (max (abs x) (abs y))

class Show a =>
      Approx a
  where
  isApprox' :: a -> a -> (Bool, String)
  isApprox :: a -> a -> Bool
  x `isApprox` y = fst (x `isApprox'` y)
  isApproxQC :: a -> a -> Property
  x `isApproxQC` y =
    let (ok, errs) = x `isApprox'` y
     in counterexample
          (unlines
             ["Control: " ++ show x, "AD:      " ++ show y, "Errors:  " ++ errs])
          ok

instance Approx Scal where
  x `isApprox'` y =
    let err = relAbsDiff x y
     in (err < 0.001, show err)

instance Approx (Vect n) where
  x `isApprox'` y =
    let results = zipWith isApprox' (V.toList x) (V.toList y)
     in (and (map fst results), show (map snd results))

instance (Approx a, Approx b) => Approx (a, b) where
  (a, b) `isApprox'` (x, y) =
    let (ok1, errs1) = a `isApprox'` x
        (ok2, errs2) = b `isApprox'` y
     in (ok1 && ok2, "(" ++ errs1 ++ ", " ++ errs2 ++ ")")

evalFwdFinDiff :: (FinDiff a, FinDiff b) => SL.STerm a b -> a -> a -> b
evalFwdFinDiff f x y =
  (SL.evalSt f (x `plus` (delta `scalProd` y)) `minus` SL.evalSt f x) `scalDiv`
  delta
  where
    delta = 0.0000001

propAll ::
     ( Arbitrary a
     , Arbitrary b
     , Show a
     , LT a
     , LT b
     , Approx a
     , Approx b
     , FinDiff a
     , FinDiff b
     , Element a ~ Element b
     , Element a ~ Scal
     , a ~ Df1 a
     , a ~ Df2 a
     , b ~ Df1 b
     , b ~ Df2 b
     , a ~ Dr1 a
     , a ~ Dr2 a
     , b ~ Dr1 b
     , b ~ Dr2 b
     )
  => SL.STerm a b
  -> Property
propAll = propAll' arbitrary genWithPrimal genWithPrimal (const id)

-- The @a -> Property -> Property@ argument can be used to e.g. 'label'
-- generated arguments in QuickCheck.
propAll' ::
     ( Arbitrary a
     , Arbitrary b
     , Show a
     , LT a
     , LT b
     , Approx a
     , Approx b
     , FinDiff a
     , FinDiff b
     , Element a ~ Element b
     , Element a ~ Scal
     , a ~ Df1 a
     , a ~ Df2 a
     , b ~ Df1 b
     , b ~ Df2 b
     , a ~ Dr1 a
     , a ~ Dr2 a
     , b ~ Dr1 b
     , b ~ Dr2 b
     )
  => Gen a
  -> (a -> Gen a)
  -> (b -> Gen b)
  -> (a -> Property -> Property)
  -> SL.STerm a b
  -> Property
propAll' arggen dirgen adjgen propfun sterm =
  conjoin
    [ counterexample
        "testing: fwd1"
        (forAll arggen $ \arg -> propfun arg $ propFwd1 sterm arg)
    , counterexample
        "testing: fwd2"
        (forAll arggen $ \arg ->
           propfun arg $ forAll (dirgen arg) $ propFwd2 sterm arg)
    , counterexample
        "testing: rev1"
        (forAll arggen $ \arg -> propfun arg $ propRev1 sterm arg)
    , counterexample
        "testing: rev2"
        (forAll arggen $ \arg -> propfun arg $ propRev2 sterm arg adjgen)
    ]

propFwd1 ::
     (Show a, Approx b, a ~ Df1 a, b ~ Df1 b) => SL.STerm a b -> a -> Property
propFwd1 sterm arg =
  let resEval = SL.evalSt sterm arg
      resAD = TL.evalTt (F.d1 sterm) arg
   in resEval `isApproxQC` resAD

propFwd2 ::
     (Approx b, FinDiff a, FinDiff b, a ~ Df1 a, a ~ Df2 a, b ~ Df2 b)
  => SL.STerm a b
  -> a
  -> a
  -> Property
propFwd2 sterm arg dir =
  let resFD = evalFwdFinDiff sterm arg dir
      resAD = lApp (TL.evalTt (F.d2 sterm) arg) dir
   in resFD `isApproxQC` resAD

propRev1 :: (Approx b, a ~ Dr1 a, b ~ Dr1 b) => SL.STerm a b -> a -> Property
propRev1 sterm arg =
  let resEval = SL.evalSt sterm arg
      resAD = TL.evalTt (R.d1 sterm) arg
   in resEval `isApproxQC` resAD

-- Finite differencing approach: Function to approximate is (arg :: a) -> (adjoint :: b) -> a
-- 1. Enumerate the basis vectors of the type 'a'; let L :: [a] be that list, with as length the number of values in 'a'
-- 2. Call finite differencing with 'arg' and 'v' for each 'v' in 'L'; the result is a list M :: [b] with as length the number of values in 'a'
-- 3. Compute the dot product of each element in 'M' with 'adjoint', producing a list N :: [Scal] ('fdvals' below) with as length the number of values in 'a'
-- 4. Return the 'a' value produced by initialising it with the values in 'N'.
propRev2 ::
     ( FinDiff a
     , FinDiff b
     , Element a ~ Element b
     , Approx a
     , Show b
     , a ~ Dr1 a
     , a ~ Dr2 a
     , b ~ Dr2 b
     )
  => SL.STerm a b
  -> a
  -> (b -> Gen b)
  -> Property
propRev2 sterm arg adjgen =
  forAll (adjgen (SL.evalSt sterm arg)) $ \adjoint ->
    let fdvals =
          [dotprod adjoint (evalFwdFinDiff sterm arg v) | v <- oneHotVecs arg]
        resFD = rebuild arg fdvals
        resAD = lApp (TL.evalTt (R.d2 sterm) arg) adjoint
     in resFD `isApproxQC` resAD

propFwdVsRev ::
     ( Arbitrary a
     , Arbitrary b
     , Show b
     , FinDiff a
     , FinDiff b
     , Element a ~ Element b
     , Approx a
     , a ~ Df1 a
     , a ~ Df2 a
     , a ~ Dr1 a
     , a ~ Dr2 a
     , b ~ Df2 b
     , b ~ Dr2 b
     )
  => SL.STerm a b
  -> Property
propFwdVsRev = propFwdVsRev' arbitrary arbitrary

propFwdVsRev' ::
     ( Arbitrary a
     , Arbitrary b
     , Show b
     , FinDiff a
     , FinDiff b
     , Element a ~ Element b
     , Approx a
     , a ~ Df1 a
     , a ~ Df2 a
     , a ~ Dr1 a
     , a ~ Dr2 a
     , b ~ Df2 b
     , b ~ Dr2 b
     )
  => Gen a
  -> Gen b
  -> SL.STerm a b
  -> Property
propFwdVsRev' arggen adjgen sterm =
  forAll arggen $ \arg ->
    forAll adjgen $ \adjoint ->
      let fdvals =
            [ dotprod adjoint (lApp (TL.evalTt (F.d2 sterm) arg) v)
            | v <- oneHotVecs arg
            ]
          resFD = rebuild arg fdvals
          resAD = lApp (TL.evalTt (R.d2 sterm) arg) adjoint
       in resFD `isApproxQC` resAD

floorf :: RealFrac a => a -> a
floorf x = fromIntegral (floor x :: Integer)

main :: IO ()
main =
  defaultMain $
  testGroup
    "AD"
    [ localOption (QuickCheckTests 10000) fastTests
    , localOption (QuickCheckTests 1000) slowTests
    , localOption (QuickCheckTests 100) superSlowTests
    ]

fastTests :: TestTree
fastTests =
  testGroup
    "Fast"
    [ testProperty "id" (propAll E.slid)
    , testProperty "pair" (propAll E.pair)
    , testProperty "add" (propAll E.add)
    , testProperty "prod" (propAll E.prod)
    , testProperty "addCopy" (propAll E.addCopy)
    , testProperty "cX" (\c -> propAll (E.cX c))
    , testProperty "xSquared" (propAll E.xSquared)
    , testProperty "xCubed" (propAll E.xCubed)
    , testProperty "quadratic" (\c -> propAll (E.quadratic c))
    , testProperty "mapQuadratic" (\c -> propAll (E.mapQuadratic c))
    -- foldProd: For small inputs, finite differencing is still accurate enough
    , testProperty
        "foldProd-small"
        (propAll'
           (genVect :: Gen (Vect 4))
           (resize 1 . genWithPrimal)
           (const arbitrarySizedFractional)
           (const id)
           E.foldProd)
    -- foldProd: For larger inputs, we only compare forward AD versus reverse AD
    , testProperty
        "foldProd-noFD"
        (propFwdVsRev'
           (genVect :: Gen (Vect 8))
           arbitrarySizedFractional
           E.foldProd)
    , testProperty "foldProd2" (propAll E.foldProd2)
    -- foldrSum: For small inputs, finite differencing is still accurate enough
    , testProperty
        "foldrSum-small"
        (propAll'
           (genVect :: Gen (Vect 4))
           (resize 1 . genWithPrimal)
           (const arbitrarySizedFractional)
           (const id)
           E.foldrSum)
    -- foldrSum: For larger inputs, we only compare forward AD versus reverse AD
    , testProperty
        "foldrSum-noFD"
        (propFwdVsRev'
           (genVect :: Gen (Vect 8))
           arbitrarySizedFractional
           E.foldrSum)
    ]

slowTests :: TestTree
slowTests =
  testGroup
    "Slow"
    [ testProperty
        "fact"
        (propAll'
           (choose (-2, 20) `suchThat`
            (\x -> x - fromIntegral (floor x :: Int) > 0.1))
           (\_ -> choose (0.1, 0.5))
           (\_ -> choose (0.1, 0.5))
           (const id)
           E.fact)
    , testProperty
        "factExtra"
        (propAll'
           ((,) <$> (choose (-2, 20) `suchThat` (\x -> x /= floorf x)) <*>
            arbitrarySizedFractional)
           (\_ -> (,) <$> choose (0.1, 0.5) <*> arbitrarySizedFractional)
           (\_ -> choose (0.1, 0.5))
           (const id)
           E.factExtra)
    , testProperty
        "fact2"
        (propAll'
           (choose (-2, 5) `suchThat` (\x -> x /= floorf x))
           (\_ -> choose (0.1, 0.5))
           (\_ -> choose (0.1, 0.5))
           (const id)
           E.fact2)
    , testProperty
        "fact2Extra"
        (propAll'
           ((,) <$> (choose (-2, 5) `suchThat` (\x -> x /= floorf x)) <*>
            arbitrarySizedFractional)
           (\_ -> (,) <$> choose (0.1, 0.5) <*> arbitrarySizedFractional)
           (\_ -> choose (0.1, 0.5))
           (const id)
           E.fact2Extra)
    ]

superSlowTests :: TestTree
superSlowTests =
  testGroup
    "Super slow"
    [ testProperty
        "tree"
        (propAll'
           (choose (-2, 10) `suchThat` (\x -> x /= floorf x))
           (\_ -> choose (0.1, 0.5))
           (\_ -> choose (0.1, 0.5))
           (const id)
           E.tree)
    , testProperty
        "treeExtra"
        (propAll'
           ((,) <$> (choose (-2, 10) `suchThat` (\x -> x /= floorf x)) <*>
            arbitrarySizedFractional)
           (\_ -> (,) <$> choose (0.1, 0.5) <*> arbitrarySizedFractional)
           (\_ -> choose (0.1, 0.5))
           (const id)
           E.treeExtra)
    ]
