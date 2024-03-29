{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Examples of programs in the source languages. The testsuite checks that AD
-- on these programs does the right thing.
module Examples where

import GHC.TypeNats
import qualified Data.Vector.Unboxed.Sized as V

import Env
import Operation
import SourceLanguage
import Types


bin :: (a ~ Df1 a, b ~ Df1 b, c ~ Df1 c, a ~ Dr1 a, b ~ Dr1 b, c ~ Dr1 c
       ,a ~ UnLin a, b ~ UnLin b, c ~ UnLin c
       ,LT2 a, LT2 b, LT2 c, LT (UnLin (Df2 c)))
    => Operation (a, b) c -> STerm env a -> STerm env b -> STerm env c
bin op x y = SOp op (SPair x y)

infixl 6 `scaladd`
scaladd :: STerm env Scal -> STerm env Scal -> STerm env Scal
scaladd = bin EScalAdd

infixl 7 `scalprod`
scalprod :: STerm env Scal -> STerm env Scal -> STerm env Scal
scalprod = bin EScalProd

constant :: (a ~ Df1 a, a ~ Dr1 a, a ~ UnLin a, LT a, LT2 a, LT (UnLin (Df2 a)), Show a) => a -> STerm env a
constant x = SOp (Constant x) SUnit

-- | Mixed-second-order map (as used in the examples in the paper) expressed in
-- terms of the first-order map in the AD macros.
--
-- > map2 f xs = map1 (f x) with x from xs
map2 :: KnownNat n
     => STerm env (Scal -> Scal)
     -> STerm env (Vect n)
     -> STerm env (Vect n)
map2 fun arg = SMap1 (sinkSt1 fun `SApp` SVar Z) arg


-- First example program in the paper
paper_ex1 :: STerm '[Scal] ((Scal, Scal), Scal)
paper_ex1 =
  SLet (constant 2 `scalprod` SVar Z) $  -- y
  SLet (SVar (S Z) `scalprod` SVar Z) $  -- z
  SLet (SOp EScalCos (SVar Z)) $  -- w
  SLet (SPair (SPair (SVar (S (S Z))) (SVar (S Z))) (SVar Z)) $  -- v
    SVar Z

paper_ex1_ref :: ((), Scal) -> ((Scal, Scal), Scal)
paper_ex1_ref ((), x) =
  let y = 2 * x
      z = x * y
      w = cos z
      v = ((y, z), w)
  in v

-- Second example program in the paper
--
-- Simplified: sin (x1 * x4 * x3 + 2 * x2 * x3 + x4)
paper_ex2 :: STerm '[Scal, Scal, Scal, Scal] Scal
paper_ex2 =
  SLet (SVar (S (S (S Z))) `scalprod` SVar Z
          `scaladd` constant 2 `scalprod` SVar (S (S Z))) $  -- y
  SLet (SVar Z `scalprod` SVar (S (S Z))) $  -- z
  SLet (SVar Z `scaladd` SVar (S (S Z))) $  -- w
  SLet (SOp EScalSin (SVar Z)) $  -- v
    SVar Z

paper_ex2_ref :: (((((), Scal), Scal), Scal), Scal) -> Scal
paper_ex2_ref (((((), x1), x2), x3), x4) =
  let y = x1 * x4 + 2 * x2
      z = y * x3
      w = z + x4
      v = sin w
  in v

-- Third example program in the paper
--
-- Simplified, this program is equivalent to:
--   map (\z -> x * z + 1) (replicate x)
--   = replicate (x * x + 1)
-- and hence the reverse derivative, given x : Scal and d : dScal^n, is:
--   sum (map (\dx -> dx * 2 * x) d)
--   = 2 * sum (map (*x) d)
paper_ex3 :: KnownNat n => STerm '[Scal] (Vect n)
paper_ex3 =
  SLet (SLambda $ SVar (S Z) `scalprod` SVar Z `scaladd` constant 1) $  -- f
  SLet (SReplicate (SVar (S Z))) $  -- zs
  SLet (map2 (SVar (S Z)) (SVar Z)) $  -- ys
    SVar Z

paper_ex3_ref :: KnownNat n => ((), Scal) -> Vect n
paper_ex3_ref ((), x) =
  let f = \z -> x * z + 1
      zs = V.replicate x
      ys = V.map f zs
  in ys

-- Fourth example program in the paper
--
-- Simplified, this program is equivalent to:
--   sum (map (x1 *) x2)
-- and hence the reverse derivative, given x1 : Scal, x2 : Scal^n and d : dScal, is:
--   - with respect to x1:
--       d * sum x2
--   - with respect to x2:
--       replicate (d * x1)
paper_ex4 :: KnownNat n => STerm '[Vect n, Scal] Scal
paper_ex4 =
  SLet (SLambda $ SVar (S (S Z)) `scalprod` SVar Z) $  -- f
  SLet (map2 (SVar Z) (SVar (S Z))) $  -- ys
  SLet (SSum (SVar Z)) $  -- w
    SVar Z

paper_ex4_ref :: KnownNat n => (((), Scal), Vect n) -> Scal
paper_ex4_ref (((), x1), x2) =
  let f = \x2i -> x1 * x2i
      ys = V.map f x2
      w = V.sum ys
  in w

-- x:Scal |- 2 * ((\y -> y * y) x) + 7 * x + 3
polynomial :: STerm '[Scal] Scal
polynomial =
  constant 2 `scalprod` (square `SApp` SVar Z)
  `scaladd` constant 7 `scalprod` SVar Z
  `scaladd` constant 3
  where square :: STerm env (Scal -> Scal)
        square = SLambda (SVar Z `scalprod` SVar Z)

-- x
slid :: STerm '[Scal] Scal
slid = SVar Z

-- (x, x)
pair :: STerm '[Scal] (Scal, Scal)
pair = SPair (SVar Z) (SVar Z)

-- x + y
add :: STerm '[Scal, Scal] Scal
add = SVar (S Z) `scaladd` SVar Z

-- x + y, from a tuple
add2 :: STerm '[(Scal, Scal)] Scal
add2 = SOp EScalAdd (SVar Z)

-- x * y
prod :: STerm '[Scal, Scal] Scal
prod = SVar (S Z) `scalprod` SVar Z

-- x * y, from a tuple
prod2 :: STerm '[(Scal, Scal)] Scal
prod2 = SOp EScalProd (SVar Z)

-- let z = x + y in (z, z)
addCopy :: STerm '[Scal, Scal] (Scal, Scal)
addCopy = SLet (SVar (S Z) `scaladd` SVar Z)
               (SPair (SVar Z) (SVar Z))

-- c * x
cX :: Double -> STerm '[Scal] Scal
cX c = SOp (Constant c) SUnit `scalprod` SVar Z

-- x^2
xSquared :: STerm '[Scal] Scal
xSquared = SVar Z `scalprod` SVar Z

-- x^3
xCubed :: STerm '[Scal] Scal
xCubed = xSquared `scalprod` SVar Z

-- c * x + x^2
quadratic :: Double -> STerm '[Scal] Scal
quadratic c = cX c `scaladd` xSquared

-- Map a quadratic function (c*x + x^2) over an input vector
mapQuadratic :: Double -> STerm '[Vect 3] (Vect 3)
mapQuadratic c = SMap1 (generaliseEnv (quadratic c)) (SVar Z)
  where
    generaliseEnv :: STerm '[a] t -> STerm (a ': env) t
    generaliseEnv = sinkSt (wSink wNil)

abs' :: STerm (Scal ': env) Scal
abs' =
  SCase (SOp EScalSign (SVar Z))
    (SOp EScalSubt (SPair (SOp (Constant 0) SUnit) (SVar (S Z))))
    (SVar (S Z))
