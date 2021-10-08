{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module FinDiff where

import Data.Proxy
import Data.List (transpose)
import GHC.TypeNats
import qualified Data.Vector.Unboxed.Sized as V

import Types


class LT a => FinDiff a where
  type Element a
  elements :: a -> [Element a]
  rebuild' :: [Element a] -> (a, [Element a])  -- ^ returns any excess elements
  oneElement :: Proxy a -> Element a

  -- | Rebuild a value from the list of elements. Assumes that the list has the
  -- right length.
  rebuild :: [Element a] -> a
  rebuild = fst . rebuild'

  oneHotVecs :: [a]
  oneHotVecs = go id (elements (zero @a))
    where go :: FinDiff a => ([Element a] -> [Element a]) -> [Element a] -> [a]
          go _ [] = []
          go prefix (x:xs) = rebuild (prefix (oneElement (Proxy @a) : xs)) : go (prefix . (x:)) xs

-- | Element type is assumed to be Scal
instance FinDiff () where
  type Element () = Scal
  elements _ = []
  rebuild' l = ((), l)
  oneElement _ = 1.0

instance (FinDiff a, FinDiff b, Element a ~ Element b) => FinDiff (a, b) where
  type Element (a, b) = Element a
  elements (x, y) = elements x ++ elements y
  rebuild' l = let (x, l1) = rebuild' l
                   (y, l2) = rebuild' l1
               in ((x, y), l2)
  oneElement _ = oneElement (Proxy @a)

instance FinDiff Scal where
  type Element Scal = Scal
  elements x = [x]
  rebuild' ~(x:xs) = (x, xs)
  oneElement _ = 1.0

instance KnownNat n => FinDiff (Vect n) where
  type Element (Vect n) = Scal
  elements = V.toList
  rebuild' l =
    let (l1, l2) = splitAt (fromIntegral (natVal (Proxy @n))) l
        Just v = V.fromList l1
    in (v, l2)
  oneElement _ = 1.0

-- | Given the reverse derivative of some function of type @a -> b@, return the
-- Jacobian of the function at the given input.
jacobianByRows :: forall a b' a'. (FinDiff b', FinDiff a', Element a' ~ Scal)
               => (a -> b' -> a') -> a -> [[Scal]]
jacobianByRows revad inp = [elements (revad inp adjoint) | adjoint <- oneHotVecs @b']

-- | Given the forward derivative of some function of type @a -> b@, return the
-- Jacobian of the function at the given input.
jacobianByCols :: forall a a' b'. (FinDiff a', FinDiff b', Element b' ~ Scal)
               => (a -> a' -> b') -> a -> [[Scal]]
jacobianByCols fwdad inp = transpose [elements (fwdad inp tangent) | tangent <- oneHotVecs @a']

-- | Given a finite-differencing derivative of some function of type @a -> b@,
-- return the Jacobian of the function at the given input.
--
-- The finite-differencing derivative takes three arguments: an input value
-- @x@, a one-hot input vector @v@, and a one-hot output vector @w@. Let @f@ be
-- the function that is to be differentiated. The output should be an estimate
-- of the partial derivative of the component of @f@ indicated by the
-- one-position in @w@, with respect to the input component indicated by the
-- one-position in @v@.
--
-- For finite-differencing, this means that a calculation similar to the
-- following is expected:
-- @1/h ((f(x + h v) - f(x)) `dot` w)@.
jacobianByElts :: forall a b. (FinDiff a, Element a ~ Scal, FinDiff b, Element b ~ Scal)
               => (a -> a -> b -> Scal) -> a -> [[Scal]]
jacobianByElts fd inp = [[fd inp v w | v <- oneHotVecs @a] | w <- oneHotVecs @b]

-- | Compute a single element of the Jacobian of @f@ using finite differencing.
-- In the arguments @f@, @x@, @dx@, @dy@, the argument @x@ is the input value,
-- and @dx@ and @dy@ should respectively be one-hot vectors indicating the
-- column and row of the Jacobian, respectively.
--
-- This function is suitable to be used with 'jacobianByElts'.
finiteDifference :: (FinDiff a, FinDiff b, Element a ~ Scal, Element b ~ Scal)
                 => (a -> b) -> a -> a -> b -> Scal
finiteDifference f x dx dy =
  let veczip :: FinDiff a => (Element a -> Element a -> Element a) -> a -> a -> a
      veczip g a b = rebuild (zipWith g (elements a) (elements b))
      vecsum = sum . elements
      add = veczip (+)
      sub = veczip (-)
      dot a b = vecsum (veczip (*) a b)
      scale :: forall a. (FinDiff a, Num (Element a)) => Element a -> a -> a
      scale e a = veczip (*) (rebuild (e <$ elements (zero @a))) a
  in recip h * ((f (x `add` scale h dx) `sub` f x) `dot` dy)
  where
    h = 0.00001 :: Scal
