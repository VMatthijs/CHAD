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
-- This module contains supporting definitions for finite differencing. The
-- specified tests verify (using QuickCheck) that CHAD forward AD, CHAD reverse
-- AD and finite differencing all agree on the examples programs in the
-- "Examples" module.
--
-- Note that not all examples are tested using finite differencing, because of
-- numerical instability.
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
import Lambda.Examples
import ReverseAD
import Simplify
import SourceLanguage
import STConvert
import TargetLanguage
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
  EnvType (t ': ts) = (t, EnvType ts)

class TypeEnvironment env where
  envToTup :: ShowVal env -> EnvType env
  tupToEnv :: EnvType env -> ShowVal env

instance TypeEnvironment '[] where
  envToTup SVZ = ()
  tupToEnv () = SVZ

instance (Show t, TypeEnvironment ts) =>TypeEnvironment (t ': ts) where
  envToTup (SVS x env) = (x, envToTup env)
  tupToEnv (x, xs) = SVS x (tupToEnv xs)

data Program env t = Program
  { progProgram :: STerm env t
  , progInpGen :: Gen (ShowVal env)
  -- , progTanGen :: Gen (ShowVal (Df1Env env))
  -- , progAdjGen :: Gen (Df2 t)
  }

-- Tests:
-- testEvalT: evalSt ~= evalTt . stConvert
-- testEvalST: evalSt ~= evalTt . simplifyTTerm . stConvert
-- testEvalCT: evalSt ~= evalCt . toConcrete . stConvert
-- testEvalSCT: evalSt ~= evalCt . simplifyCTerm . toConcrete . stConvert
-- testEvalSCST: evalSt ~= evalCt . simplifyCTerm . toConcrete . simplifyTTerm . stConvert
-- testPrimalF: forward_primal ~= evalSt
-- testPrimalR: reverse_primal ~= evalSt
-- testJacFR: forward_jacobian ~= reverse_jacobian
-- testJacFD: forward_jacobian ~= fd_jacobian
-- testJacRD: reverse_jacobian ~= fd_jacobian

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
  evalCt' val . simplifyCTerm defaultSettings . toConcrete . stConvert)

testEvalSCST :: (Approx t, t ~ UnLin t, env ~ UnLinEnv env) => Program env t -> Property
testEvalSCST = testEvalStVersus (\val ->
  evalCt' val . simplifyCTerm defaultSettings . toConcrete . simplifyTTerm . stConvert)

testPrimalF :: (Approx t
               ,t ~ UnLin (Df1 t)
               ,env ~ UnLinEnv (Df1Env env)
               ,LT (Df2Env env), LT (UnLin (Df2Env env)))
            => Program env t -> Property
testPrimalF prog = forAll (progInpGen prog) $ \inp ->
  isApproxQC ("evalSt", evalSt (makeVal inp) (progProgram prog))
             ("fwdprim", fst (evalCt' (makeVal inp) cterm))
  where cterm = simplifyCTerm defaultSettings (toConcrete (df (progProgram prog)))

testPrimalR :: (Approx t
               ,t ~ UnLin (Dr1 t)
               ,env ~ UnLinEnv (Dr1Env env)
               ,LT (Dr2Env env), LT (UnLin (Dr2Env env)))
            => Program env t -> Property
testPrimalR prog = forAll (progInpGen prog) $ \inp ->
  isApproxQC ("evalSt", evalSt (makeVal inp) (progProgram prog))
             ("revprim", fst (evalCt' (makeVal inp) cterm))
  where cterm = simplifyCTerm defaultSettings (toConcrete (dr (progProgram prog)))

computeJacF :: (env ~ UnLinEnv (Df1Env env)
               ,FinDiff (UnLin (Df2Env env))
               ,FinDiff (UnLin (Df2 t)), Element (UnLin (Df2 t)) ~ Scal
               ,LT (Df2Env env))
            => Program env t -> ShowVal env -> [[Scal]]
computeJacF prog = jacobianByCols (\x dx -> snd (evalCt' (makeVal x) fwdterm) dx)
  where fwdterm = simplifyCTerm defaultSettings (toConcrete (df (progProgram prog)))

computeJacR :: (env ~ UnLinEnv (Dr1Env env)
               ,FinDiff (UnLin (Dr2 t))
               ,FinDiff (UnLin (Dr2Env env)), Element (UnLin (Dr2Env env)) ~ Scal
               ,LT (Dr2Env env))
            => Program env t -> ShowVal env -> [[Scal]]
computeJacR prog = jacobianByRows (\x dy -> snd (evalCt' (makeVal x) revterm) dy)
  where revterm = simplifyCTerm defaultSettings (toConcrete (dr (progProgram prog)))

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
testJacFD prog = forAll (progInpGen prog) $ \inp ->
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
testJacRD prog = forAll (progInpGen prog) $ \inp ->
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
        => TestName -> Program env t -> TestTree
testAll name prog = testGroup name
  [testProperty "evalSt = evalTt" $ testEvalT prog
  ,testProperty "evalSt = simpT . evalTt" $ testEvalST prog
  ,testProperty "evalSt = evalCt" $ testEvalCT prog
  ,testProperty "evalSt = simpC . evalCt" $ testEvalSCT prog
  ,testProperty "evalSt = simpC . evalCt . simpT" $ testEvalSCST prog
  ,testProperty "Forward primal" $ testPrimalF prog
  ,testProperty "Reverse primal" $ testPrimalR prog
  ,testProperty "Jacobian Fwd=Rev" $ testJacFR prog
  ,testProperty "Jacobian Fwd=FinDiff" $ testJacFD prog
  ,testProperty "Jacobian Rev=FinDiff" $ testJacRD prog
  ]

main :: IO ()
main = defaultMain $ testGroup "AD"
  [testAll "Paper example 1" (Program paper_ex1 arbitrary)
  ,testAll "Paper example 2" (Program paper_ex2 arbitrary)
  ,testAll "Paper example 3" (Program (paper_ex3 @5) arbitrary)
  ,testAll "Paper example 4" (Program (paper_ex4 @5) arbitrary)
  ]
