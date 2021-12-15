{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Type definitions used for the languages and AD, and definition of linear
-- functions.
--
-- Besides type definitions used in the various languages in this project, as
-- well as the core type families for CHAD ('Df1', 'Df2', 'Dr1', 'Dr2'), this
-- module defines the type of linear functions, 'LFun', and gives
-- implementations for a variety of such linear functions. Since the
-- constructor of 'LFun' is not exported, this module is the only place where
-- the programmer has the burden of proving that the written definitions are
-- indeed linear; outside of this module, we can trust that any fully-defined
-- 'LFun' value is really a linear function.
module Types
  ( Vect
  , Scal
  , LFun
  , lId
  , lNegate
  , lDup
  , lComp
  , lApp
  , lEval
  , lUncurry
  , lZipWith
  , lUnit
  , lPair
  , lMapTuple
  , lAdd
  , lSubt
  , lNeg
  , lProd
  , lSum
  , lExpand
  , lPlus
  , lFst
  , lSnd
  , lSwap
  , lCopowFold
  , lZip
  , lMap
  , Copower
  , singleton
  , Df1
  , Df2
  , Dr1
  , Dr2
  , LT(..)
  , LT2
  , LTU
  , LT2U
  , UnLin
  ) where

import           Data.Kind                 (Constraint)
import qualified Data.Vector.Unboxed.Sized as V (Vector, map, replicate,
                                                 sum, toList, zip, zipWith)
import           GHC.TypeNats              (KnownNat)

-- | Real scalars
type Scal = Double

-- | Vector of size n containing real scalars
type Vect n = V.Vector n Double

-- | Copower
newtype Copower a b =
  MkCopow [(a, b)]

-- | Linear function
newtype LFun a b =
  MkLFun (a -> b)

-- Methods for copowers
singleton :: LT b => a -> LFun b (Copower a b)
singleton t = MkLFun $ \x -> MkCopow [(t, x)]

-- Methods for linear functions
lId :: LT a => LFun a a
lId = MkLFun id

lNegate :: LFun Scal Scal
lNegate = MkLFun (\x -> -x)

lDup :: LT a => LFun a (a, a)
lDup = MkLFun $ \a -> (a, a)

lComp :: (LT a, LT b, LT c) => LFun a b -> LFun b c -> LFun a c
lComp (MkLFun f) (MkLFun g) = MkLFun $ g . f

lApp :: (LT a, LT b) => LFun a b -> a -> b
lApp (MkLFun f) = f

lEval :: LT b => a -> LFun (a -> b) b
lEval x = MkLFun (\f -> f x)

-- | Linear uncurry
lUncurry :: (LT a, LT b, LT c) => (a -> LFun b c) -> LFun (a, b) c
lUncurry f = MkLFun $ uncurry (lApp . f)

-- | Linear zipWith
lZipWith :: (Scal -> LFun Scal Scal) -> Vect n -> LFun (Vect n) (Vect n)
lZipWith f a = MkLFun $ V.zipWith (lApp . f) a

lZip :: Vect n -> LFun (Vect n) (Copower Scal Scal)
lZip x = MkLFun $ \y -> MkCopow $ V.toList $ V.zip x y

-- | Linear unit
lUnit :: LT a => LFun a ()
lUnit = MkLFun (const ())

-- | Pair two functions
lPair :: (LT a, LT b, LT c) => LFun a b -> LFun a c -> LFun a (b, c)
lPair a b = MkLFun $ \x -> (lApp a x, lApp b x)

-- | Map a tuple
lMapTuple ::
     (LT a, LT b, LT a', LT b')
  => LFun a a'
  -> LFun b b'
  -> LFun (a, b) (a', b')
lMapTuple f g = MkLFun $ \(a, b) -> (lApp f a, lApp g b)

-- | Addition is linear
lAdd :: LT a => LFun (a, a) a
lAdd = MkLFun $ uncurry plus

-- | Scalar subtraction is linear
lSubt :: LFun (Scal, Scal) Scal
lSubt = MkLFun $ uncurry (-)

-- | Scalar negation is linear
lNeg :: LFun Scal Scal
lNeg = MkLFun negate

-- | Multiplication linear in second argument
lProd :: (LT a, Num a) => a -> LFun a a
lProd x = MkLFun $ \y -> x * y

lSum :: LFun (Vect n) Scal
lSum = MkLFun V.sum

lExpand :: KnownNat n => LFun Scal (Vect n)
lExpand = MkLFun V.replicate

lFst :: (LT a, LT b) => LFun (a, b) a
lFst = MkLFun fst

lSnd :: (LT a, LT b) => LFun (a, b) b
lSnd = MkLFun snd

lSwap :: (LT b, LT c) => (a -> LFun b c) -> LFun b (a -> c)
lSwap t = MkLFun $ \x y -> lApp (t y) x

lCopowFold :: (LT b, LT c) => (a -> LFun b c) -> LFun (Copower a b) c
lCopowFold f = MkLFun g
  where
    g (MkCopow abs') =
      foldr plus zero (map (\(a,b) -> f a `lApp` b) abs')

lPlus :: (LT a, LT b) => LFun a b -> LFun a b -> LFun a b
lPlus (MkLFun f) (MkLFun g) = MkLFun $ \x -> plus (f x) (g x)

lMap :: KnownNat n => Vect n -> LFun (Scal -> Scal) (Vect n)
lMap x = MkLFun $ \g -> V.map g x

-- Forward mode AD type families
type family Df1 a = r | r -> a where
  Df1 Scal = Scal
  Df1 (Vect n) = Vect n
  Df1 (a -> b) = Df1 a -> (Df1 b, LFun (Df2 a) (Df2 b))
  Df1 (a, b) = (Df1 a, Df1 b)
  Df1 () = ()

type family Df2 a where
  Df2 Scal = Scal
  Df2 (Vect n) = Vect n
  Df2 (a -> b) = Df1 a -> Df2 b
  Df2 (a, b) = (Df2 a, Df2 b)
  Df2 () = ()

-- Reverse mode AD type families
type family Dr1 a = r | r -> a where
  Dr1 Scal = Scal
  Dr1 (Vect n) = Vect n
  Dr1 (a, b) = (Dr1 a, Dr1 b)
  Dr1 () = ()
  Dr1 (a -> b) = Dr1 a -> (Dr1 b, LFun (Dr2 b) (Dr2 a))

type family Dr2 a where
  Dr2 Scal = Scal
  Dr2 (Vect n) = Vect n
  Dr2 (a, b) = (Dr2 a, Dr2 b)
  Dr2 () = ()
  Dr2 (a -> b) = Copower (Dr1 a) (Dr2 b)

-- | "Linear types": types with the structure of a symmetric monoid under
-- arithmetic addition. These types are used as tangent and adjoint types in
-- automatic differentiation.
class LTctx a =>
      LT a
  where
  zero :: a
  plus :: a -> a -> a

-- This type family is used to provide bidirectional typeclass inference. The
-- trick is gleaned from:
--   https://github.com/ghc-proposals/ghc-proposals/pull/284#issuecomment-542322728
-- The idea is that normally, 'LT b' of course implies 'LT (a -> b)', but the
-- inverse cannot be inferred because type class instances need not be
-- injective. This type family explicitly requires the context 'LT b' on the
-- instance for 'LT (a -> b)', and due to the rules for injectivity of type
-- families, this is allowed.
-- At the time of writing, this is used in a few places:
-- - makeProj in the case for LinVar in evalLTt' in TargetLanguage.hs.
--
-- The superclass constraint 'LTctx a =>' on 'LT' requires UndecidableSuperClasses.
type family LTctx a :: Constraint

type instance LTctx () = ()

instance LT () where
  zero = ()
  plus _ _ = ()

type instance LTctx (a, b) = (LT a, LT b)

instance (LT a, LT b) => LT (a, b) where
  zero = (zero, zero)
  plus a b = (fst a `plus` fst b, snd a `plus` snd b)

type instance LTctx Scal = ()

instance LT Scal where
  zero = 0
  plus = (+)

type instance LTctx (Vect n) = ()

instance KnownNat n => LT (Vect n) where
  zero = V.replicate zero
  plus = V.zipWith plus

type instance LTctx (a -> b) = LT b

instance LT b => LT (a -> b) where
  zero = const zero
  plus f g = \x -> plus (f x) (g x)

type instance LTctx (Copower a b) = LT b

instance LT b => LT (Copower a b) where
  zero = MkCopow []
  plus (MkCopow x) (MkCopow y) = MkCopow (x ++ y)

type instance LTctx (LFun a b) = LT b

instance (LT a, LT b) => LT (LFun a b) where
  zero = MkLFun (const zero)
  plus = lPlus

type instance LTctx [a] = ()

instance LT [a] where
    zero = []
    plus = (++)

-- | Convenience constraint set that requires 'LT' on the types of (co)tangents
type LT2 a = (LT (Df2 a), LT (Dr2 a))

-- | Convenience constraint set that requires 'LT' on the un-linearised type as
-- well as the type itself
type LTU a = (LT a, LT (UnLin a))

-- | Convenience constraint set that requires 'LT' on the (co)tangents of the
-- type, as well as their un-linearised types.
type LT2U a = (LT2 a, LT (UnLin (Df2 a)), LT (UnLin (Dr2 a)))

-- | Conversion of linear function to ordinary functions. This is the
-- type-level change from @TargetLanguage@ to @Concrete@.
type family UnLin a where
  UnLin Scal = Scal
  UnLin (a, b) = (UnLin a, UnLin b)
  UnLin () = ()
  UnLin (a -> b) = UnLin a -> UnLin b
  UnLin (LFun a b) = UnLin a -> UnLin b
  UnLin (Copower a b) = [(UnLin a, UnLin b)]
  UnLin (Vect n) = Vect n
