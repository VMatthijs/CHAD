{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

-- | Definition of the source language
module SourceLanguage where

import           Data.Vector.Unboxed.Sized as V (Unbox, foldr, map)

import           GHC.TypeNats              (KnownNat)
import           Control.Arrow             ((&&&))
import           Operation                 (Operation, evalOp)
import           Types                     (Df1, Df2, Dr1, Dr2, Scal, Vect,
                                            LTall)

-- | Terms of the source language
data STerm a b where
  -- | Identity function
  Id :: LTall a => STerm a a
  -- | Composition
  --   Read as: f; g
  Comp
    :: (LTall a, LTall b, LTall c)
    => STerm a b
    -> STerm b c
    -> STerm a c
  -- Product tuples
  Unit :: LTall a => STerm a ()
  Pair
    :: (LTall a, LTall b, LTall c)
    => STerm a b
    -> STerm a c
    -> STerm a (b, c)
  Fst
    :: (LTall a, LTall b)
    => STerm (a, b) a
  Snd
    :: (LTall a, LTall b)
    => STerm (a, b) b
  -- | Evaluation
  Ev
    :: (LTall a, LTall b)
    => STerm (a -> b, a) b
  -- | Curry
  Curry
    :: (LTall a, LTall b, LTall c)
    => STerm (a, b) c
    -> STerm a (b -> c)
  -- | Operators
  -- For operators we also require that the primal images of the domain and
  -- codomain are equal to the original types. This means in essence that 'a'
  -- nor 'b' contain function types.
  Op
    :: ( LTall a, LTall b
       , a ~ Df1 a, b ~ Df1 b, a ~ Dr1 a, b ~ Dr1 b)
    => Operation a b
    -> STerm a b
  -- | Map
  Map :: KnownNat n => STerm (Scal -> Scal, Vect n) (Vect n)
  Foldr
    :: ( LTall a
       , V.Unbox (Df1 a)
       , V.Unbox (Df2 a)
       , V.Unbox (Dr1 a)
       , V.Unbox (Dr2 a)
       , KnownNat n
       )
    => STerm (((Scal, a) -> a, a), Vect n) a
  Inl
    :: (LTall a, LTall b)
    => STerm a (Either a b)
  Inr
    :: (LTall a, LTall b)
    => STerm b (Either a b)
  CoPair
    :: (LTall a, LTall b, LTall c)
    => STerm b a
    -> STerm c a
    -> STerm (Either b c) a
  It
    :: (LTall a, LTall b, LTall c)
    => STerm (a, b) (Either c b)
    -> STerm (a, b) c
  Sign :: STerm Scal (Either () ())
  Rec
    :: (LTall a, LTall b)
    => STerm (a, b) b
    -> STerm a b

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
