{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

-- | Definition of the source language
module SourceLanguage where

import           Data.Vector.Unboxed.Sized as V (Unbox, foldr, map)

import           GHC.TypeNats              (KnownNat)
import           Helper                    ((&&&))
import           Operation                 (Operation, evalOp)
import           Types                     (Df1, Df2, Dr1, Dr2, LT, Scal, Vect)

-- | Terms of the source language
data STerm a b
    -- | Identity function
      where
  Id :: (LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)) => STerm a a
    -- | Composition
    --   Read as: f; g
  Comp
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       , LT c
       , LT (Dr1 c)
       , LT (Dr2 c)
       , LT (Df1 c)
       , LT (Df2 c)
       )
    => STerm a b
    -> STerm b c
    -> STerm a c
    -- Product tuples
  Unit :: (LT a, LT (Dr1 a), LT (Dr2 a), LT (Df1 a), LT (Df2 a)) => STerm a ()
  Pair
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       , LT c
       , LT (Dr1 c)
       , LT (Dr2 c)
       , LT (Df1 c)
       , LT (Df2 c)
       )
    => STerm a b
    -> STerm a c
    -> STerm a (b, c)
  Fst
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       )
    => STerm (a, b) a
  Snd
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       )
    => STerm (a, b) b
    -- | Evaluation
  Ev
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       )
    => STerm (a -> b, a) b
    -- | Curry
  Curry
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       , LT c
       , LT (Dr1 c)
       , LT (Dr2 c)
       , LT (Df1 c)
       , LT (Df2 c)
       )
    => STerm (a, b) c
    -> STerm a (b -> c)
    -- | Operators
  Op
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       , a ~ Dr1 a
       , b ~ Dr1 b
       , a ~ Df1 a
       , b ~ Df1 b
       )
    => Operation a b
    -> STerm a b
    -- | Map
  Map :: KnownNat n => STerm (Scal -> Scal, Vect n) (Vect n)
  Foldr
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , V.Unbox (Df1 a)
       , V.Unbox (Df2 a)
       , V.Unbox (Dr1 a)
       , V.Unbox (Dr2 a)
       , KnownNat n
       )
    => STerm (((Scal, a) -> a, a), Vect n) a
  Inl
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       )
    => STerm a (Either a b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  Inr
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       )
    => STerm b (Either a b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  CoPair
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       , LT c
       , LT (Dr1 c)
       , LT (Dr2 c)
       , LT (Df1 c)
       , LT (Df2 c)
       )
    => STerm b a
    -> STerm c a
    -> STerm (Either b c) a
  It
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       , LT c
       , LT (Dr1 c)
       , LT (Dr2 c)
       , LT (Df1 c)
       , LT (Df2 c)
       )
    => STerm (a, b) (Either c b)
    -> STerm (a, b) c
  Sign :: STerm Scal (Either () ()) -- EXPERIMENTAL SUPPORT FOR REAL CONDITIONALS
  Rec
    :: ( LT a
       , LT (Dr1 a)
       , LT (Dr2 a)
       , LT (Df1 a)
       , LT (Df2 a)
       , LT b
       , LT (Dr1 b)
       , LT (Dr2 b)
       , LT (Df1 b)
       , LT (Df2 b)
       )
    => STerm (a, b) b
    -> STerm a b -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION

--     -- | Foldr
-- | Evaluate the source language
evalSt :: STerm a b -> a -> b
evalSt Id = id
evalSt (Comp f g) = evalSt g . evalSt f
evalSt Unit = const ()
evalSt (Pair a b) = evalSt a &&& evalSt b
evalSt Fst = fst
evalSt Snd = snd
evalSt Ev = uncurry ($)
evalSt (Curry a) = curry $ evalSt a
evalSt (Op op) = evalOp op
evalSt Map = \(f, v) -> V.map f v
evalSt Foldr = \((f, v), xs) -> V.foldr (\r a -> f (r, a)) v xs
evalSt (Rec t) = fix (evalSt t)
  where
    fix f a = f (a, fix f a)
evalSt Inl = Left -- EXPERIMENTAL SUPPORT FOR SUM TYPES
evalSt Inr = Right -- EXPERIMENTAL SUPPORT FOR SUM TYPES
evalSt (CoPair f g) =
  \x ->
    case x -- EXPERIMENTAL SUPPORT FOR SUM TYPES
          of
      Left a  -> evalSt f a
      Right b -> evalSt g b
evalSt (It t) = fix (evalSt t) -- EXPERIMENTAL SUPPORT FOR ITERATION
  where
    fix f (a, b) =
      case f (a, b) of
        Left c   -> c
        Right b' -> fix f (a, b')
evalSt Sign = \r -> if r < 0 then Left () else if r > 0 then Right () else error "Tried to call real conditional at 0" 