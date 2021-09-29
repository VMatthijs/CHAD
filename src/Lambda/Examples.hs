{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
module Lambda.Examples where

import Env
import Operation
import SourceLanguage
import Types


bin :: (a ~ Dr1 a, b ~ Dr1 b, c ~ Dr1 c, LT2 a, LT2 b, LT2 c) => Operation (a, b) c -> STerm env a -> STerm env b -> STerm env c
bin op x y = SOp op (SPair x y)

infixl 6 `scaladd`
scaladd :: STerm env Scal -> STerm env Scal -> STerm env Scal
scaladd = bin EScalAdd

infixl 7 `scalprod`
scalprod :: STerm env Scal -> STerm env Scal -> STerm env Scal
scalprod = bin EScalProd

constant :: (a ~ Dr1 a, LT a, LT2 a, Show a) => a -> STerm env a
constant x = SOp (Constant x) SUnit

-- \x -> x * x
square :: STerm env (Scal -> Scal)
square = SLambda (SOp EScalProd (SPair (SVar Z) (SVar Z)))

-- \x -> 2 * x * x + 7 * x + 3, using 'square' for the squaring
polynomial :: STerm env (Scal -> Scal)
polynomial = SLambda $
  constant 2 `scalprod` (square `SApp` SVar Z)
  `scaladd` constant 7 `scalprod` SVar Z
  `scaladd` constant 3

-- First example program in the paper
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
-- TEST: simplifyTTerm (stConvert paper_ex2) == simplifyTTerm (Fst (dr paper_ex2))
paper_ex2 :: STerm '[Scal, Scal, Scal, Scal] Scal
paper_ex2 =
  SLet (SVar (S (S (S Z))) `scalprod` SVar Z
          `scaladd` constant 2 `scalprod` SVar (S (S Z))) $  -- y
  SLet (SVar Z `scalprod` SVar (S (S Z))) $  -- z
  SLet (SVar Z `scaladd` SVar (S (S Z))) $  -- w
  SLet (SOp EScalSin (SVar Z)) $  -- v
    SVar Z
