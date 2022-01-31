{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableSuperClasses   #-}
{-# OPTIONS -Wno-orphans #-} -- for Arbitrary

-- | Test suite for the AD code.
--
-- The specified tests verify (using QuickCheck) that CHAD forward AD, CHAD
-- reverse AD and finite differencing all agree on the examples programs in the
-- "Examples" module.
--
-- Tests for all example programs:
--
-- * 'testEvalT': @evalSt ~= evalTt . stConvert@
-- * 'testEvalST': @evalSt ~= evalTt . simplifyTTerm . stConvert@
-- * 'testEvalCT': @evalSt ~= evalCt . toConcrete . stConvert@
-- * 'testEvalSCT': @evalSt ~= evalCt . simplifyCTerm . toConcrete . stConvert@
-- * 'testEvalSCST': @evalSt ~= evalCt . simplifyCTerm . toConcrete . simplifyTTerm . stConvert@
-- * 'testPrimalF': @forward_primal ~= evalSt@
-- * 'testPrimalR': @reverse_primal ~= evalSt@
-- * 'testJacFR': @forward_jacobian ~= reverse_jacobian@
-- * 'testJacFD': @forward_jacobian ~= fd_jacobian@
-- * 'testJacRD': @reverse_jacobian ~= fd_jacobian@
--
-- where @~=@ denotes elementwise approximate equality.
--
-- The four paper examples are additionally tested against their @_ref@
-- reference implementations in Haskell.
module Test where

import Control.Monad (replicateM)
import Data.Proxy
import Data.Maybe (fromJust)
import qualified Data.Vector.Unboxed.Sized as V
import GHC.TypeNats
import Test.Tasty
import Test.Tasty.QuickCheck

import Concrete
import Concrete.Simplify
import Env
import ForwardAD
import FinDiff
import Examples
import ReverseAD
import SourceLanguage
import STConvert
import TargetLanguage
import TargetLanguage.Simplify
import ToConcrete
import Types


instance KnownNat n => Arbitrary (Vect n) where
  arbitrary = fromJust . V.fromList <$> replicateM (fromIntegral (natVal (Proxy @n))) arbitrary


-- Minimum of the relative difference and the absolute difference
relAbsDiff :: Scal -> Scal -> Scal
relAbsDiff x y = abs (x - y) / max 1 (max (abs x) (abs y))

class Show a => Approx a where
  -- | Return whether the values are close together, as well as a description
  -- of the error between them.
  isApprox' :: a -> a -> (Bool, String)

  -- | Return whether the values are close together (using 'isApprox'').
  isApprox :: a -> a -> Bool
  x `isApprox` y = fst (x `isApprox'` y)

  -- | Given names of what the two inputs represent, produce a QuickCheck
  -- property that puts the error description string in the 'counterexample'. (Uses 'isApprox''.)
  isApproxQC :: (String, a) -> (String, a) -> Property
  (xdesc, x) `isApproxQC` (ydesc, y) =
    let (ok, errs) = x `isApprox'` y
        xprefix = xdesc ++ ": "
        yprefix = ydesc ++ ": "
        errprefix = "Errors: "
        len = maximum (map length [xprefix, yprefix, errprefix])
        xprefix' = xprefix ++ replicate (max 0 (len - length xprefix)) ' '
        yprefix' = yprefix ++ replicate (max 0 (len - length yprefix)) ' '
        errprefix' = errprefix ++ replicate (max 0 (len - length errprefix)) ' '
     in counterexample
          (unlines [xprefix' ++ show x, yprefix' ++ show y, errprefix' ++ errs])
          ok

instance Approx Scal where
  x `isApprox'` y =
    let err = relAbsDiff x y
    in (err < 0.001, show err)

instance Approx (Vect n) where
  x `isApprox'` y =
    let (oks, errs) = unzip $ zipWith isApprox' (V.toList x) (V.toList y)
    in (and oks, show errs)

instance (Approx a, Approx b) => Approx (a, b) where
  (a, b) `isApprox'` (x, y) =
    let (ok1, errs1) = a `isApprox'` x
        (ok2, errs2) = b `isApprox'` y
    in (ok1 && ok2, "(" ++ errs1 ++ ", " ++ errs2 ++ ")")

instance Approx a => Approx [a] where
  x `isApprox'` y
    | length x == length y =
        let (oks, errs) = unzip $ zipWith isApprox' x y
        in (and oks, show errs)
    | otherwise =
        error "Unequal list lengths in Approx on lists"


data ShowVal env where
  SVZ :: ShowVal '[]
  SVS :: Show t => t -> ShowVal env -> ShowVal (t ': env)
deriving instance Show (ShowVal env)

makeVal :: ShowVal env -> Val env
makeVal SVZ = VZ
makeVal (SVS x env) = VS x (makeVal env)

instance Arbitrary (ShowVal '[]) where
  arbitrary = pure SVZ

instance (Show t, Arbitrary t, Arbitrary (ShowVal ts))
      => Arbitrary (ShowVal (t ': ts)) where
  arbitrary = SVS <$> arbitrary <*> arbitrary

type family EnvType env where
  EnvType '[] = ()
  EnvType (t ': ts) = (EnvType ts, t)

class TypeEnvironment env where
  envToTup :: ShowVal env -> EnvType env
  tupToEnv :: EnvType env -> ShowVal env

instance TypeEnvironment '[] where
  envToTup SVZ = ()
  tupToEnv () = SVZ

instance (Show t, TypeEnvironment ts) => TypeEnvironment (t ': ts) where
  envToTup (SVS x env) = (envToTup env, x)
  tupToEnv (xs, x) = SVS x (tupToEnv xs)

data Program env t = Program
  { progProgram :: STerm env t
  , progInpGen :: Gen (ShowVal env)
  , -- | Special input generator when comparing with finite differencing.
    -- Because of the limited precision of FD, this usually needs to be a
    -- smaller range of values where the derivative isn't too large yet.
    progInpGenFD :: Gen (ShowVal env)
  }

instance Show (Program env t) where
  showsPrec p (Program prog _ _) = showParen (p > 10) $
    showString "Program " . showsPrec 11 prog . showString " _ _"

testEvalStVersus :: Approx t
                 => (Val env -> STerm env t -> t) -> Program env t -> Property
testEvalStVersus transform prog = forAll (progInpGen prog) $ \inp ->
  isApproxQC ("evalSt", evalSt (makeVal inp) (progProgram prog))
             ("evalTt", transform (makeVal inp) (progProgram prog))

testEvalT :: Approx t => Program env t -> Property
testEvalT = testEvalStVersus (\val -> evalTt' val . stConvert)

testEvalST :: Approx t => Program env t -> Property
testEvalST = testEvalStVersus (\val -> evalTt' val . simplifyTTerm . stConvert)

testEvalCT :: (Approx t, t ~ UnLin t, env ~ UnLinEnv env) => Program env t -> Property
testEvalCT = testEvalStVersus (\val -> evalCt' val . toConcrete . stConvert)

testEvalSCT :: (Approx t, t ~ UnLin t, env ~ UnLinEnv env) => Program env t -> Property
testEvalSCT = testEvalStVersus (\val ->
  evalCt' val . simplifyCTerm allSettings . toConcrete . stConvert)

testEvalSCST :: (Approx t, t ~ UnLin t, env ~ UnLinEnv env) => Program env t -> Property
testEvalSCST = testEvalStVersus (\val ->
  evalCt' val . simplifyCTerm allSettings . toConcrete . simplifyTTerm . stConvert)

testPrimalF :: (Approx t
               ,t ~ UnLin (Df1 t)
               ,env ~ UnLinEnv (Df1Env env)
               ,LT (Df2Env env), LT (UnLin (Df2Env env)))
            => Program env t -> Property
testPrimalF prog = forAll (progInpGen prog) $ \inp ->
  isApproxQC ("evalSt", evalSt (makeVal inp) (progProgram prog))
             ("fwdprim", fst (evalCt' (makeVal inp) cterm))
  where cterm = simplifyCTerm allSettings (toConcrete (df (progProgram prog)))

testPrimalR :: (Approx t
               ,t ~ UnLin (Dr1 t)
               ,env ~ UnLinEnv (Dr1Env env)
               ,LT (Dr2Env env), LT (UnLin (Dr2Env env)))
            => Program env t -> Property
testPrimalR prog = forAll (progInpGen prog) $ \inp ->
  isApproxQC ("evalSt", evalSt (makeVal inp) (progProgram prog))
             ("revprim", fst (evalCt' (makeVal inp) cterm))
  where cterm = simplifyCTerm allSettings (toConcrete (dr (progProgram prog)))

computeJacF :: (env ~ UnLinEnv (Df1Env env)
               ,FinDiff (UnLin (Df2Env env))
               ,FinDiff (UnLin (Df2 t)), Element (UnLin (Df2 t)) ~ Scal
               ,LT (Df2Env env))
            => Program env t -> ShowVal env -> [[Scal]]
computeJacF prog = jacobianByCols (\x dx -> snd (evalCt' (makeVal x) fwdterm) dx)
  where fwdterm = simplifyCTerm allSettings (toConcrete (df (progProgram prog)))

computeJacR :: (env ~ UnLinEnv (Dr1Env env)
               ,FinDiff (UnLin (Dr2 t))
               ,FinDiff (UnLin (Dr2Env env)), Element (UnLin (Dr2Env env)) ~ Scal
               ,LT (Dr2Env env))
            => Program env t -> ShowVal env -> [[Scal]]
computeJacR prog = jacobianByRows (\x dy -> snd (evalCt' (makeVal x) revterm) dy)
  where revterm = simplifyCTerm allSettings (toConcrete (dr (progProgram prog)))

computeJacD :: (TypeEnvironment env
               ,FinDiff t, Element t ~ Scal
               ,FinDiff (EnvType env), Element (EnvType env) ~ Scal)
            => Program env t -> ShowVal env -> [[Scal]]
computeJacD prog sval =
  let fun tupinp = evalSt (makeVal (tupToEnv tupinp)) (progProgram prog)
  in jacobianByElts (finiteDifference fun) (envToTup sval)

testJacFR :: (env ~ UnLinEnv (Df1Env env)
             ,env ~ UnLinEnv (Dr1Env env)
             ,FinDiff (UnLin (Df2Env env))
             ,FinDiff (UnLin (Df2 t)), Element (UnLin (Df2 t)) ~ Scal
             ,FinDiff (UnLin (Dr2 t))
             ,FinDiff (UnLin (Dr2Env env)), Element (UnLin (Dr2Env env)) ~ Scal
             ,LT (Df2Env env), LT (Dr2Env env))
          => Program env t -> Property
testJacFR prog = forAll (progInpGen prog) $ \inp ->
  isApproxQC ("fwdad", computeJacF prog inp)
             ("revad", computeJacR prog inp)

testJacFD :: (TypeEnvironment env
             ,env ~ UnLinEnv (Df1Env env)
             ,FinDiff (UnLin (Df2Env env))
             ,FinDiff (UnLin (Df2 t)), Element (UnLin (Df2 t)) ~ Scal
             ,FinDiff t, Element t ~ Scal
             ,FinDiff (EnvType env), Element (EnvType env) ~ Scal
             ,LT (Df2Env env))
          => Program env t -> Property
testJacFD prog = forAll (progInpGenFD prog) $ \inp ->
  isApproxQC ("fwdad", computeJacF prog inp)
             ("findiff", computeJacD prog inp)

testJacRD :: (TypeEnvironment env
             ,env ~ UnLinEnv (Dr1Env env)
             ,FinDiff (UnLin (Dr2 t))
             ,FinDiff (UnLin (Dr2Env env)), Element (UnLin (Dr2Env env)) ~ Scal
             ,FinDiff t, Element t ~ Scal
             ,FinDiff (EnvType env), Element (EnvType env) ~ Scal
             ,LT (Dr2Env env))
          => Program env t -> Property
testJacRD prog = forAll (progInpGenFD prog) $ \inp ->
  isApproxQC ("revad", computeJacR prog inp)
             ("findiff", computeJacD prog inp)


testAll :: (TypeEnvironment env
           ,Approx t
           -- Forward AD
           ,FinDiff (UnLin (Df2Env env))
           ,FinDiff (UnLin (Df2 t)), Element (UnLin (Df2 t)) ~ Scal
           ,LT (Df2Env env)
           ,UnLinEnv (Df1Env env) ~ env
           ,UnLin (Df1 t) ~ t
           -- Reverse AD
           ,FinDiff (UnLin (Dr2 t))
           ,FinDiff (UnLin (Dr2Env env)), Element (UnLin (Dr2Env env)) ~ Scal
           ,LT (Dr2Env env)
           ,UnLinEnv (Dr1Env env) ~ env
           ,UnLin (Dr1 t) ~ t
           -- Finite differencing
           ,FinDiff t, Element t ~ Scal
           ,FinDiff (EnvType env), Element (EnvType env) ~ Scal
           ,UnLinEnv env ~ env
           ,UnLin t ~ t)
        => TestName -> Gen (Program env t) -> TestTree
testAll name prog = testGroup name
  [testProperty "evalSt = evalTt" $ forAll prog testEvalT
  ,testProperty "evalSt = simpT . evalTt" $ forAll prog testEvalST
  ,testProperty "evalSt = evalCt" $ forAll prog testEvalCT
  ,testProperty "evalSt = simpC . evalCt" $ forAll prog testEvalSCT
  ,testProperty "evalSt = simpC . evalCt . simpT" $ forAll prog testEvalSCST
  ,testProperty "Forward primal is id" $ forAll prog testPrimalF
  ,testProperty "Reverse primal is id" $ forAll prog testPrimalR
  ,testProperty "Jacobian Fwd=Rev" $ forAll prog testJacFR
  ,testProperty "Jacobian Fwd=FinDiff" $ forAll prog testJacFD
  ,testProperty "Jacobian Rev=FinDiff" $ forAll prog testJacRD
  ]

-- | Use this operator to build environment generators. In particular, read
-- this with @f ~ Gen@.
(<:) :: (Applicative f, Show t) => f t -> f (ShowVal env) -> f (ShowVal (t ': env))
mx <: menv = SVS <$> mx <*> menv
infixr <:

programGen :: Gen (STerm env t) -> Gen (ShowVal env) -> Gen (ShowVal env) -> Gen (Program env t)
programGen proggen inp fdinp = (\prog -> Program prog inp fdinp) <$> proggen

programArb :: Arbitrary (ShowVal env) => STerm env t -> Gen (Program env t)
programArb prog = pure (Program prog arbitrary arbitrary)

main :: IO ()
main =
  defaultMain $
    localOption (QuickCheckTests 4000) $
      testGroup "CHAD" [referenceTests, adTests]
  where
    referenceTests = testGroup "Reference tests"
      [testProperty "evalSt (Paper example 1) ~= reference" $
         property $ \arg -> isApproxQC ("evalSt", evalSt (makeVal arg) paper_ex1)
                                       ("ref", paper_ex1_ref (envToTup arg))
      ,testProperty "evalSt (Paper example 2) ~= reference" $
         property $ \arg -> isApproxQC ("evalSt", evalSt (makeVal arg) paper_ex2)
                                       ("ref", paper_ex2_ref (envToTup arg))
      ,testProperty "evalSt (Paper example 3) ~= reference" $
         property $ \arg -> isApproxQC ("evalSt", evalSt (makeVal arg) (paper_ex3 @10))
                                       ("ref", paper_ex3_ref (envToTup arg))
      ,testProperty "evalSt (Paper example 4) ~= reference" $
         property $ \arg -> isApproxQC ("evalSt", evalSt (makeVal arg) (paper_ex4 @10))
                                       ("ref", paper_ex4_ref (envToTup arg))
      ]

    adTests = testGroup "AD"
      [testAll "polynomial" (programArb polynomial)
      ,testAll "slid" (programArb slid)
      ,testAll "pair" (programArb pair)
      ,testAll "abs'" (programArb (abs' :: STerm '[Scal] Scal))
      ,testAll "add" (programArb add)
      ,testAll "add2" (programArb add2)
      ,testAll "prod" (programArb prod)
      ,testAll "prod2" (programArb prod2)
      ,testAll "addCopy" (programArb addCopy)
      ,testAll "cX" (programGen (cX <$> arbitrary) arbitrary arbitrary)
      ,testAll "xSquared" (programArb xSquared)
      ,testAll "xCubed" (programArb xCubed)
      ,testAll "quadratic" (programGen (quadratic <$> arbitrary) arbitrary arbitrary)
      ,testAll "mapQuadratic" (programGen (mapQuadratic <$> arbitrary) arbitrary arbitrary)
      ,testAll "Paper example 1" (pure $
          Program paper_ex1 arbitrary (choose (-6, 6) <: pure SVZ))
      ,testAll "Paper example 2" (pure $
          Program paper_ex2 arbitrary (choose (-6, 6) <: choose (-6, 6) <:
                                       choose (-6, 6) <: choose (-6, 6) <: pure SVZ))
      ,testAll "Paper example 3" (programArb (paper_ex3 @5))
      ,testAll "Paper example 4" (programArb (paper_ex4 @5))
      ]
