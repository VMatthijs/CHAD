{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Lambda.Examples where

import GHC.TypeNats

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

-- \x -> x * x
square :: STerm env (Scal -> Scal)
square = SLambda (SOp EScalProd (SPair (SVar Z) (SVar Z)))

-- x:Scal |- 2 * x * x + 7 * x + 3, using 'square' for the squaring
polynomial :: STerm '[Scal] Scal
polynomial =
  constant 2 `scalprod` (square `SApp` SVar Z)
  `scaladd` constant 7 `scalprod` SVar Z
  `scaladd` constant 3

-- First example program in the paper
--
-- x : Scal |- paper_ex1 : ((Scal, Scal), Scal)
-- let y = 2 * x
--     z = x * y
--     w = cos z
--     v = ((y, z), w)
-- in v
--
-- TEST: simplifyTTerm (stConvert paper_ex1) == simplifyTTerm (Fst (dr paper_ex1))
paper_ex1 :: STerm '[Scal] ((Scal, Scal), Scal)
paper_ex1 =
  SLet (constant 2 `scalprod` SVar Z) $  -- y
  SLet (SVar (S Z) `scalprod` SVar Z) $  -- z
  SLet (SOp EScalCos (SVar Z)) $  -- w
  SLet (SPair (SPair (SVar (S (S Z))) (SVar (S Z))) (SVar Z)) $  -- v
    SVar Z

-- Second example program in the paper
--
-- x1 : Scal, x2 : Scal, x3 : Scal, x4 : Scal |- paper_ex2 : Scal
-- let y = x1 * x4 + 2 * x2
--     z = y * x3
--     w = z + x4
--     v = sin w
-- in v
--
-- TEST: simplifyTTerm (stConvert paper_ex2) == simplifyTTerm (Fst (dr paper_ex2))
paper_ex2 :: STerm '[Scal, Scal, Scal, Scal] Scal
paper_ex2 =
  SLet (SVar (S (S (S Z))) `scalprod` SVar Z
          `scaladd` constant 2 `scalprod` SVar (S (S Z))) $  -- y
  SLet (SVar Z `scalprod` SVar (S (S Z))) $  -- z
  SLet (SVar Z `scaladd` SVar (S (S Z))) $  -- w
  SLet (SOp EScalSin (SVar Z)) $  -- v
    SVar Z

-- Third example program in the paper
--
-- x : Scal |- paper_ex3 : Scal^n
-- let f = \z -> x * z + 1
--     zs = replicate x
--     ys = map f zs
-- in ys
--
-- TEST: simplifyTTerm (stConvert (paper_ex3 @5)) == simplifyTTerm (Fst (dr (paper_ex3 @5)))
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
  SLet (SMap (SVar (S Z)) (SVar Z)) $  -- ys
    SVar Z

-- Fourth example program in the paper
--
-- x1 : Scal, x2 : Scal^n |- paper_ex4 : Scal
-- let f = \x2i -> x1 * x2i
--     ys = map f x2
--     w = sum ys
-- in w
--
-- TEST: simplifyTTerm (stConvert (paper_ex4 @5)) == simplifyTTerm (Fst (dr (paper_ex4 @5)))
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
  SLet (SMap (SVar Z) (SVar (S Z))) $  -- ys
  SLet (SSum (SVar Z)) $  -- w
    SVar Z
