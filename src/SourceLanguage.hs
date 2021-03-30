{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

-- | Definition of the source language
module SourceLanguage where

import           Data.Vector.Unboxed.Sized as V (Unbox, foldr, map)

import           Control.Arrow             ((&&&))
import           GHC.TypeNats              (KnownNat)
import           Operation                 (Operation, evalOp)
import           Types                     (DZ, Df1, Df2, Dr1, Dr2, LT2, Scal,
                                            Vect)

-- | Terms of the source language
data STerm a b where
  -- | Identity function
  Id :: LT2 a => STerm a a
  -- | Composition
  --   Read as: f; g
  Comp :: (LT2 a, LT2 b, LT2 c) => STerm a b -> STerm b c -> STerm a c
  -- Product tuples
  Unit :: (LT2 a) => STerm a ()
  Pair :: (LT2 a, LT2 b, LT2 c) => STerm a b -> STerm a c -> STerm a (b, c)
  Fst :: (LT2 a, LT2 b) => STerm (a, b) a
  Snd :: (LT2 a, LT2 b) => STerm (a, b) b
  -- | Evaluation
  Ev :: (LT2 a, LT2 b) => STerm (a -> b, a) b
  -- | Curry
  Curry :: (LT2 a, LT2 b, LT2 c) => STerm (a, b) c -> STerm a (b -> c)
  -- | Operators
  -- For operators we also require that the primal images of the domain and
  -- codomain are equal to the original types. This means in essence that 'a'
  -- nor 'b' contain function types.
  Op
    :: (a ~ Df1 a, b ~ Df1 b, a ~ Dr1 a, b ~ Dr1 b)
    => Operation a b
    -> STerm a b
  -- | Map
  Map :: KnownNat n => STerm (Scal -> Scal, Vect n) (Vect n)
  Foldr
    :: ( V.Unbox (Df1 a)
       , V.Unbox (Df2 a)
       , V.Unbox (Dr1 a)
       , V.Unbox (Dr2 a)
       , KnownNat n
       , LT2 a
       )
    => STerm (((Scal, a) -> a, a), Vect n) a
  Inl :: (LT2 a, LT2 b) => STerm a (Either a b)
  Inr :: (LT2 a, LT2 b) => STerm b (Either a b)
  CoPair
    :: (LT2 a, LT2 b, LT2 c) => STerm b a -> STerm c a -> STerm (Either b c) a
  It :: (LT2 a, LT2 b, LT2 c) => STerm (a, b) (Either c b) -> STerm (a, b) c
  Sign :: STerm Scal (Either () ())
  Rec :: (LT2 a, LT2 b, DZ (Dr2 b)) => STerm (a, b) b -> STerm a b

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
evalSt Foldr = \((f, v), xs) -> V.foldr (curry f) v xs
evalSt (Rec t) = fix (evalSt t)
  where
    fix f a = f (a, fix f a)
evalSt Inl = Left
evalSt Inr = Right
evalSt (CoPair f g) =
  \x ->
    case x of
      Left a  -> evalSt f a
      Right b -> evalSt g b
evalSt (It t) = fix (evalSt t)
  where
    fix f (a, b) =
      case f (a, b) of
        Left c   -> c
        Right b' -> fix f (a, b')
evalSt Sign =
  \r ->
    if r < 0
      then Left ()
      else if r > 0
             then Right ()
             else error "Tried to call real conditional at 0"
