{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

-- | Different type definitions used in the language
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
  , dFoldr
  , dtFoldr
  , dIt
  , dtIt
  , lRec
  , lIt
  , LEither
  , lInl
  , lInr
  , lCoPair
  , Copower
  , singleton
  , Df1
  , Df2
  , Dr1
  , Dr2
  , LT(..)
  , DZ(..)
  , LTall
  ) where

import qualified Data.Vector.Unboxed.Sized as V (Unbox, Vector, foldr, init,
                                                 last, map, prescanr, replicate,
                                                 scanl, sum, toList, zip,
                                                 zipWith)
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

-- | Linear coproduct
newtype LEither a b =
  MkLEither (Maybe (Either a b)) 

-- Methods for copowers

singleton :: a -> LFun b (Copower a b)
singleton t = MkLFun $ \x -> MkCopow [(t, x)]

-- Methods for linear coproducts
lInl :: LFun a (LEither a b)
lInl = MkLFun (MkLEither . Just . Left)

lInr :: LFun b (LEither a b)
lInr = MkLFun (MkLEither . Just . Right)

lCoPair :: LT c => LFun a c -> LFun b c -> LFun (LEither a b) c
lCoPair (MkLFun f) (MkLFun g) = MkLFun h
  where
    h (MkLEither Nothing)          = zero
    h (MkLEither (Just (Left a)))  = f a
    h (MkLEither (Just (Right b))) = g b

-- Methods for linear functions
lId :: LFun a a
lId = MkLFun id

lNegate :: LFun Scal Scal
lNegate = MkLFun (\x -> -x)

lDup :: LFun a (a, a)
lDup = MkLFun $ \a -> (a, a)

lComp :: LFun a b -> LFun b c -> LFun a c
lComp (MkLFun f) (MkLFun g) = MkLFun $ g . f

lApp :: LFun a b -> a -> b
lApp (MkLFun f) = f

lEval :: a -> LFun (a -> b) b
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
lUnit :: LFun a () 
lUnit = MkLFun (const ())

-- | Pair two functions
lPair :: (LT a, LT b, LT c) => LFun a b -> LFun a c -> LFun a (b, c)
lPair a b = MkLFun $ \x -> (lApp a x, lApp b x)

-- | Map a tuple
lMapTuple ::
     (LT a, LT a', LT b, LT b')
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

-- | Multiplication linear in second argument
lProd :: Num a => (a -> LFun a a)
lProd x = MkLFun $ \y -> x * y

lSum :: LFun (Vect n) Scal
lSum = MkLFun V.sum

lExpand :: KnownNat n => LFun Scal (Vect n)
lExpand = MkLFun $ \a -> V.replicate a

lFst :: LFun (a, b) a
lFst = MkLFun fst

lSnd :: LFun (a, b) b
lSnd = MkLFun snd

lSwap :: (LT a, LT b, LT c) => (a -> LFun b c) -> LFun b (a -> c)
lSwap t = MkLFun $ \x y -> lApp (t y) x

lCopowFold :: (LT b, LT c) => (a -> LFun b c) -> LFun (Copower a b) c
lCopowFold f = MkLFun $ g
  where
    g (MkCopow abs') = foldr (\(a, b) acc -> (f a `lApp` b) `plus` acc) zero abs'

lPlus :: (LT a, LT b) => LFun a b -> LFun a b -> LFun a b
lPlus (MkLFun f) (MkLFun g) = MkLFun $ \x -> plus (f x) (g x)

lMap :: KnownNat n => Vect n -> LFun (Scal -> Scal) (Vect n)
lMap x = MkLFun $ \g -> V.map g x

dFoldr ::
     (KnownNat n, V.Unbox a, V.Unbox b, LT b)
  => ((Scal, a) -> (a, LFun (Scal, b) b))
  -> a
  -> (Vect n)
  -> LFun (((Scal, a) -> b, b), Vect n) b
dFoldr f i v =
  MkLFun $ \((f', i'), v') ->
    let s = V.prescanr (curry (fst . f)) i v
        vvps = V.zip v (V.zip v' s)
        g (vi, (vpi, si)) acc =
          lApp (snd (f (vi, si))) (vpi, f' (vi, si) `plus` acc)
     in V.foldr g i' vvps

dtFoldr ::
     (V.Unbox a, V.Unbox b, LT b)
  => ((Scal, a) -> (a, LFun b (Scal, b)))
  -> a
  -> (Vect n)
  -> LFun b ((Copower (Scal, a) b, b), Vect n)
dtFoldr f i v =
  MkLFun $ \w ->
    let s = V.prescanr (curry (fst . f)) i v
        vs = V.zip v s
        svs = V.scanl (flip $ curry (snd . uncurry (lApp . snd . f))) w vs
        vssvs = V.zip vs (V.init svs)
     in ( (MkCopow (V.toList vssvs), V.last svs)
        , V.map (fst . uncurry (lApp . snd . f)) vssvs)

dIt ::
     (LT d2a, LT d2b, LT d2c)
  => ((d1a, d1b) -> Either d1c d1b)
  -> ((d1a, d1b) -> LFun (d2a, d2b) (LEither d2c d2b))
  -> ((d1a, d1b) -> LFun (d2a, d2b) d2c)
dIt d1t d2t (d1a, d1b) =
  MkLFun $ \(d2a, d2b) ->
    let d1bs = scanIt d1t (d1a, d1b)
        vfst (MkLEither Nothing)          = zero
        vfst (MkLEither (Just (Left a)))  = a
        vfst (MkLEither (Just (Right _))) = error "This should never happen."
        vsnd (MkLEither Nothing)          = zero
        vsnd (MkLEither (Just (Left _)))  = error "This should never happen."
        vsnd (MkLEither (Just (Right b))) = b
     in vfst
          (d2t (d1a, last d1bs) `lApp`
           ( d2a
           , foldl
               (\acc d1b' -> vsnd (d2t (d1a, d1b') `lApp` (d2a, acc)))
               d2b
               (init d1bs)))

dtIt ::
     (LT d2a, LT d2b, LT d2c)
  => ((d1a, d1b) -> Either d1c d1b)
  -> ((d1a, d1b) -> LFun (LEither d2c d2b) (d2a, d2b))
  -> ((d1a, d1b) -> LFun d2c (d2a, d2b))
dtIt d1t d2t (d1a, d1b) =
  MkLFun $ \d2c ->
    let d1bs = scanIt d1t (d1a, d1b)
        d2ad2b = d2t (d1a, last d1bs) `lApp` (lInl `lApp` d2c)
        d2ad2bs =
          scanr
            (\d1b' acc -> d2t (d1a, d1b') `lApp` (lInr `lApp` snd acc))
            d2ad2b
            (init d1bs)
     in (foldr plus zero (map fst d2ad2bs), snd (head d2ad2bs))

scanIt :: ((c, a) -> Either b a) -> (c, a) -> [a]
scanIt f (c, a) =
  case f (c, a) of
    Left _ -> [a]
    Right a' ->
      let as = scanIt f (c, a')
       in a : as

lRec :: LFun (a, b) b -> LFun a b
lRec (MkLFun g) = MkLFun $ lrec g
  where
    lrec f a = f (a, lrec f a)

lIt :: (LT a, DZ b) => LFun b (a, b) -> LFun b a
lIt f =
  MkLFun $ \b ->
    if isZero b -- Note that this will be decidable in practice as b will not contain any function types (being a Dr2 type)!
      then zero
      else let (a, b') = f `lApp` b
            in plus a (lIt f `lApp` b')

-- Forward mode AD type families
type family Df1 a = r | r -> a where
  Df1 Scal = Scal
  Df1 (Vect n) = Vect n
  Df1 (a -> b) = Df1 a -> (Df1 b, LFun (Df2 a) (Df2 b))
  Df1 (a, b) = (Df1 a, Df1 b)
  Df1 () = ()
  Df1 (Either a b) = Either (Df1 a) (Df1 b)

type family Df2 a where
  Df2 Scal = Scal
  Df2 (Vect n) = Vect n
  Df2 (a -> b) = Df1 a -> Df2 b
  Df2 (a, b) = (Df2 a, Df2 b)
  Df2 () = ()
  Df2 (Either a b) = LEither (Df2 a) (Df2 b) -- TODO: better to work with Either (Dr2 a) (Dr2 b), but that requires dynamic types or explicit retainment of primals.

-- Reverse mode AD type families
type family Dr1 a = r | r -> a where
  Dr1 Scal = Scal
  Dr1 (Vect n) = Vect n
  Dr1 (a, b) = (Dr1 a, Dr1 b)
  Dr1 () = ()
  Dr1 (Either a b) = Either (Dr1 a) (Dr1 b)
  Dr1 (a -> b) = Dr1 a -> (Dr1 b, LFun (Dr2 b) (Dr2 a))

type family Dr2 a where
  Dr2 Scal = Scal
  Dr2 (Vect n) = Vect n
  Dr2 (a, b) = (Dr2 a, Dr2 b)
  Dr2 () = ()
  Dr2 (Either a b) = LEither (Dr2 a) (Dr2 b) -- TODO: better to work with Either (Dr2 a) (Dr2 b), but that requires dynamic types or explicit retainment of primals.
  Dr2 (a -> b) = Copower (Dr1 a) (Dr2 b)

-- | Operators defined over multiple language types
class LT a where
  zero :: a -- For automatic differentiation
  plus :: a -> a -> a -- For automatic differentiation

instance LT () where
  zero = ()
  plus _ _ = ()

instance (LT a, LT b) => LT (a, b) where
  zero = (zero, zero)
  plus a b = (fst a `plus` fst b, snd a `plus` snd b)

instance (LT a, LT b) => LT (Either a b) where
  zero = error "This should never be used." -- This doesn't make sense.
  plus (Left a) (Left a')   = Left (a `plus` a')
  plus (Right a) (Right a') = Right (a `plus` a')
  plus _ _                  = error "This should never be used." -- This doesn't make sense.

instance LT Scal where
  zero = 0
  plus = (+)

instance KnownNat n => LT (Vect n) where
  zero = V.replicate 0
  plus = V.zipWith (+)

instance (LT a, LT b) => LT (a -> b) where
  zero = const zero
  plus f g = \x -> plus (f x) (g x)

instance (LT a, LT b) => LT (Copower a b) where
  zero = MkCopow []
  plus (MkCopow x) (MkCopow y) = MkCopow (x ++ y)

instance (LT a, LT b) => LT (LFun a b) where
  zero = MkLFun zero
  plus = lPlus

instance (LT a, LT b) => LT (LEither a b) where
  zero = MkLEither Nothing
  plus (MkLEither Nothing) b = b
  plus a (MkLEither Nothing) = a
  plus (MkLEither (Just (Left a))) (MkLEither (Just (Left a'))) =
    MkLEither (Just (Left (a `plus` a')))
  plus (MkLEither (Just (Right b))) (MkLEither (Just (Right b'))) =
    MkLEither (Just (Right (b `plus` b')))
  plus _ _ = error "This should never be used." -- This doesn't make sense.

-- | Decidable Zero: types for which it is decidable whether a value of that
-- type equals zero.
-- This class is only used for reverse AD of recursion.
class LT a => DZ a where
  -- TODO: superclass constraint should be the class that has 'zero', not full 'LT'
  isZero :: a -> Bool

instance DZ () where
  isZero _ = True

instance (DZ a, DZ b) => DZ (a, b) where
  isZero (a, b) = isZero a && isZero b

instance DZ Scal where
  isZero = (== zero)

instance KnownNat n => DZ (Vect n) where
  isZero = (== zero)

instance (DZ a, DZ b) => DZ (Copower a b) where
  isZero (MkCopow xs) = all isZero (map snd xs)

instance (DZ a, DZ b) => DZ (LEither a b) where
  isZero (MkLEither Nothing)          = True
  isZero (MkLEither (Just (Left a)))  = isZero a
  isZero (MkLEither (Just (Right b))) = isZero b

-- | Convenience constraint set that requires 'LT' on the type itself and all
-- its mapped types under the AD maps.
type LTall a = (LT a, LT (Df1 a), LT (Df2 a), LT (Dr1 a), LT (Dr2 a))
