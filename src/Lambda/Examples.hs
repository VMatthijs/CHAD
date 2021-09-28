{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Lambda.Examples where

import GHC.TypeNats

import Lambda
import Operation
import TargetLanguage.Env
import Types


bin :: Type c -> Operation (a, b) c -> Lambda env a -> Lambda env b -> Lambda env c
bin t op x y = Op t op (Pair x y)

infixl 6 `scaladd`
scaladd :: Lambda env Scal -> Lambda env Scal -> Lambda env Scal
scaladd = bin TScal EScalAdd

infixl 7 `scalprod`
scalprod :: Lambda env Scal -> Lambda env Scal -> Lambda env Scal
scalprod = bin TScal EScalProd

class MagicType a where magicType :: Type a
instance MagicType Scal where magicType = TScal
instance MagicType () where magicType = TNil
instance (MagicType a, MagicType b) => MagicType (a, b) where magicType = TPair magicType magicType
instance (MagicType a, MagicType b) => MagicType (a -> b) where magicType = TFun magicType magicType
instance (MagicType a, MagicType b) => MagicType (LFun a b) where magicType = TLFun magicType magicType
instance (MagicType a, MagicType b) => MagicType (Copower a b) where magicType = TCopow magicType magicType
instance KnownNat n => MagicType (Vect n) where magicType = TVect

constant :: (LT a, LT2 a, Show a, MagicType a) => a -> Lambda env a
constant x = Op magicType (Constant x) Unit

-- \x -> x * x
square :: Lambda env (Scal -> Scal)
square = Lambda TScal (Op TScal EScalProd (Pair (Var TScal Z) (Var TScal Z)))

-- \x -> 2 * x * x + 7 * x + 3, using 'square' for the squaring
polynomial :: Lambda env (Scal -> Scal)
polynomial = Lambda TScal $
  constant 2 `scalprod` (square `App` Var TScal Z)
  `scaladd` constant 7 `scalprod` Var TScal Z
  `scaladd` constant 3

-- First example program in the paper
--
-- TEST: simplify paper_ex1 == simplify (Fst (dr (EPush TScal ENil) paper_ex1))
paper_ex1 :: Lambda '[Scal] ((Scal, Scal), Scal)
paper_ex1 =
  let x = Var TScal Z
  in Let (constant 2 `scalprod` x) $  -- y
     Let (x `scalprod` Var TScal Z) $  -- z
     Let (Op TScal EScalCos (Var TScal Z)) $  -- w
     Let (Pair (Pair (Var TScal (S (S Z))) (Var TScal (S Z))) (Var TScal Z)) $  -- v
       Var (TPair (TPair TScal TScal) TScal) Z
