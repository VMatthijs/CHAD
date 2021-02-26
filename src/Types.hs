{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE StandaloneDeriving     #-}

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
  , lCur
  , lZip
  , lMap
  , dFoldr
  , dtFoldr
  , dIt
  , dtIt
  , lRec
  , lIt
  , Tens
  , empty
  , (Types.++)
  , singleton
  , Df1
  , Df2
  , Dr1
  , Dr2
  , Type(..)
  , eqTy
  , LT(..)
  ) where

import           Data.Proxy                (Proxy (Proxy))
import           Data.Type.Equality        ((:~:) (Refl))
import qualified Data.Vector.Unboxed.Sized as V (Unbox, Vector, foldr, init,
                                                 last, map, prescanr, replicate,
                                                 scanl, sum, toList, zip,
                                                 zipWith)
import           GHC.TypeNats              (KnownNat, sameNat)

-- | Real scalars
type Scal = Double

-- | Vector of size n containing real scalars
type Vect n = V.Vector n Double

-- | Tensor products
newtype Tens a b =
  MkTens [(a, b)]

-- | Linear function
newtype LFun a b =
  MkLFun (a -> b)

-- Methods for tensor products
-- | Empty tensor product
empty :: Tens a b
empty = MkTens []

(++) :: Tens a b -> Tens a b -> Tens a b
(MkTens x) ++ (MkTens y) = MkTens (x Prelude.++ y)

singleton :: a -> LFun b (Tens a b)
singleton t = MkLFun $ \x -> MkTens [(t, x)]

-- Methods for linear functions
lId :: LFun a a
lId = MkLFun id

lNegate :: LFun Scal Scal
lNegate = MkLFun (\x -> -x)

lDup :: LFun a (a, a)
lDup = MkLFun $ \a -> (a, a)

lComp :: LFun a b -> LFun b c -> LFun a c
lComp (MkLFun f) (MkLFun g) = MkLFun $ g . f

lApp :: (LT a, LT b) => LFun a b -> a -> b
lApp (MkLFun f) = f

lEval :: a -> LFun (a -> b) b
lEval x = MkLFun (\f -> f x)

-- | Linear uncurry
lUncurry :: (LT a, LT b, LT c) => (a -> LFun b c) -> LFun (a, b) c
lUncurry f = MkLFun $ uncurry (lApp . f)

-- | Linear zipWith
lZipWith :: (Scal -> LFun Scal Scal) -> Vect n -> LFun (Vect n) (Vect n)
lZipWith f a = MkLFun $ V.zipWith (lApp . f) a

lZip :: Vect n -> LFun (Vect n) (Tens Scal Scal)
lZip x = MkLFun $ \y -> MkTens $ V.toList $ V.zipWith f x y
  where
    f a b = (a, b)

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

-- | Subtraction is linear
lSubt :: LT a => LFun (a, a) a
lSubt = MkLFun $ uncurry minus

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

lCur :: (LT b, LT c) => (a -> LFun b c) -> LFun (Tens a b) c
lCur f = MkLFun $ g where 
  g (MkTens abs') = foldr (\(a, b) acc -> (f a `lApp` b) `plus` acc) zero abs'

lPlus :: (LT a, LT b) => LFun a b -> LFun a b -> LFun a b
lPlus (MkLFun f) (MkLFun g) = MkLFun $ \x -> plus (f x) (g x)

lMinus :: (LT a, LT b) => LFun a b -> LFun a b -> LFun a b
lMinus (MkLFun f) (MkLFun g) = MkLFun $ \x -> minus (f x) (g x)

lScalProd :: (LT b) => Scal -> LFun a b -> LFun a b
lScalProd r (MkLFun g) = MkLFun $ \x -> scalProd r (g x)

lScalDiv :: (LT b) => LFun a b -> Scal -> LFun a b
lScalDiv (MkLFun g) r = MkLFun $ \x -> scalDiv (g x) r

lMap :: KnownNat n => Vect n -> LFun (Scal -> Scal) (Vect n)
lMap x = MkLFun $ \g -> V.map g x

dFoldr ::
     (KnownNat n, V.Unbox a, V.Unbox b, LT b)
  => (((Scal, a) -> (a, LFun (Scal, b) b), a), Vect n)
  -> LFun (((Scal, a) -> b, b), Vect n) b
dFoldr ((f, i), v) =
  MkLFun $ \((f', i'), v') ->
    let s = V.prescanr (curry (fst . f)) i v
        vvps = V.zip v (V.zip v' s)
        g (vi, (vpi, si)) acc =
          lApp (snd (f (vi, si))) (vpi, f' (vi, si) `plus` acc)
     in V.foldr g i' vvps

dtFoldr ::
     (V.Unbox a, V.Unbox b, LT b)
  => (((Scal, a) -> (a, LFun b (Scal, b)), a), Vect n)
  -> LFun b ((Tens (Scal, a) b, b), Vect n)
dtFoldr ((f, i), v) =
  MkLFun $ \w ->
    let s = V.prescanr (curry (fst . f)) i v
        vs = V.zip v s
        svs = V.scanl (flip $ curry (snd . uncurry (lApp . snd . f))) w vs
        vssvs = V.zip vs (V.init svs)
     in ( (MkTens (V.toList vssvs), V.last svs)
        , V.map (fst . uncurry (lApp . snd . f)) vssvs)

dIt ::
     (LT d2a, LT d2b, LT d2c)
  => ((d1a, d1b) -> Either d1c d1b)
  -> ((d1a, d1b) -> LFun (d2a, d2b) (d2c, d2b))
  -> ((d1a, d1b) -> LFun (d2a, d2b) d2c) -- EXPERIMENTAL SUPPORT FOR ITERATION
dIt d1t d2t (d1a, d1b) =
  MkLFun $ \(d2a, d2b) ->
    let d1bs = scanIt d1t (d1a, d1b)
     in fst
          (d2t (d1a, last d1bs) `lApp`
           ( d2a
           , foldl
               (\acc d1b' -> snd (d2t (d1a, d1b') `lApp` (d2a, acc)))
               d2b
               (init d1bs)))

dtIt ::
     (LT d2a, LT d2b, LT d2c)
  => ((d1a, d1b) -> Either d1c d1b)
  -> ((d1a, d1b) -> LFun (d2c, d2b) (d2a, d2b))
  -> ((d1a, d1b) -> LFun d2c (d2a, d2b)) -- EXPERIMENTAL SUPPORT FOR ITERATION
dtIt d1t d2t (d1a, d1b) =
  MkLFun $ \d2c ->
    let d1bs = scanIt d1t (d1a, d1b)
        d2ad2b = d2t (d1a, last d1bs) `lApp` (d2c, zero)
        d2ad2bs =
          scanr
            (\d1b' acc -> d2t (d1a, d1b') `lApp` (zero, snd acc))
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

lRec :: LFun (a, b) b -> LFun a b -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
lRec (MkLFun g) = MkLFun $ lrec g where 
    lrec f a = f (a, lrec f a)

lIt' :: LT a => Int -> LFun b (a, b) -> LFun b a -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION -- THIS ALMOST WORKS. WE NEED TO BREAK OUT OF THE POTENTIALLY INFINITE LOOP THOUGH, SOMEHOW
lIt' n (MkLFun g) = MkLFun $ lit n g where 
    lit n f b = let (a, b') = f b in if n <= 0 then a else plus a (lit (n-1) f b')

lIt :: LT a => LFun b (a, b) -> LFun b a
lIt = lIt' 1000

-- Forward mode AD type families
type family Df1 a where
  Df1 Scal = Scal
  Df1 (Vect n) = Vect n
  Df1 (a -> b) = Df1 a -> (Df1 b, LFun (Df2 a) (Df2 b))
  Df1 (a, b) = (Df1 a, Df1 b)
  Df1 () = ()
  Df1 (Either a b) = Either (Df1 a) (Df1 b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

type family Df2 a where
  Df2 Scal = Scal
  Df2 (Vect n) = Vect n
  Df2 (a -> b) = Df1 a -> Df2 b
  Df2 (a, b) = (Df2 a, Df2 b)
  Df2 () = ()
  Df2 (Either a b) = (Df2 a, Df2 b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

-- Reverse mode AD type families
type family Dr1 a where
  Dr1 Scal = Scal
  Dr1 (Vect n) = Vect n
  Dr1 (a -> b) = Dr1 a -> (Dr1 b, LFun (Dr2 b) (Dr2 a))
  Dr1 (a, b) = (Dr1 a, Dr1 b)
  Dr1 () = ()
  Dr1 (Either a b) = Either (Dr1 a) (Dr1 b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

type family Dr2 a where
  Dr2 Scal = Scal
  Dr2 (Vect n) = Vect n
  Dr2 (a -> b) = Tens (Dr1 a) (Dr2 b)
  Dr2 (a, b) = (Dr2 a, Dr2 b)
  Dr2 () = ()
  Dr2 (Either a b) = (Dr2 a, Dr2 b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

data Type a where
  TScal :: Type Scal
  TVect :: KnownNat n => Proxy n -> Type (Vect n)
  TArrow :: Type a -> Type b -> Type (a -> b)
  TPair :: Type a -> Type b -> Type (a, b)
  TUnit :: Type ()
  TEither :: Type a -> Type b -> Type (Either a b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  TLinFun :: Type a -> Type b -> Type (LFun a b)
  TTens :: Type a -> Type b -> Type (Tens a b)

deriving instance Show (Type a)

eqTy :: Type u -> Type v -> Maybe (u :~: v)
eqTy (TVect n) (TVect m) =
  case sameNat n m of
    Just Refl -> Just Refl
    Nothing   -> Nothing
eqTy TUnit TUnit = Just Refl
eqTy (TArrow u1 u2) (TArrow v1 v2) = do
  Refl <- eqTy u1 v1
  Refl <- eqTy u2 v2
  return Refl
eqTy (TPair u1 u2) (TPair v1 v2) = do
  Refl <- eqTy u1 v1
  Refl <- eqTy u2 v2
  return Refl
eqTy (TLinFun u1 u2) (TLinFun v1 v2) = do
  Refl <- eqTy u1 v1
  Refl <- eqTy u2 v2
  return Refl
eqTy (TTens u1 u2) (TTens v1 v2) = do
  Refl <- eqTy u1 v1
  Refl <- eqTy u2 v2
  return Refl
eqTy TScal TScal = return Refl
eqTy (TEither u1 u2) (TEither v1 v2) = do
  Refl <- eqTy u1 v1
  Refl <- eqTy u2 v2
  return Refl
eqTy _ _ = Nothing

-- | Operators defined over multiple language types
class LT a where
  zero :: a -- For automatic differentiation
  plus :: a -> a -> a -- For automatic differentiation
  inferType :: Type a -- For interpreter of target language
  scalProd :: Scal -> a -> a -- For finite differencing
  scalDiv :: a -> Scal -> a -- For finite differencing
  minus :: a -> a -> a -- For finite differencing

instance LT () where
  zero = ()
  plus _ _ = ()
  inferType = TUnit
  scalProd _ _ = ()
  scalDiv _ _ = ()
  minus _ _ = ()

instance (LT a, LT b) => LT (a, b) where
  zero = (zero, zero)
  plus a b = (fst a `plus` fst b, snd a `plus` snd b)
  inferType = TPair inferType inferType
  scalProd r a = (scalProd r (fst a), scalProd r (snd a))
  scalDiv a r = (scalDiv (fst a) r, scalDiv (snd a) r)
  minus a b = (fst a `minus` fst b, snd a `minus` snd b)


instance (LT a, LT b) => LT (Either a b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
                                                                               where
  zero = error "This should never be used." -- This doesn't make sense.
  plus (Left a) (Left a') = Left (a `plus` a')
  plus (Right a) (Right a') = Right (a `plus` a')
  plus _ _ = error "This should never be used." -- This doesn't make sense.
  inferType = TEither inferType inferType
  scalProd r (Left a) = Left (scalProd r a)
  scalProd r (Right a) = Right (scalProd r a)
  scalDiv (Left a) r = Left (scalDiv a r)
  scalDiv (Right a) r = Right (scalDiv a r)
  minus (Left a) (Left a') = Left (a `minus` a')
  minus (Right a) (Right a') = Right (a `minus` a')
  minus _ _ = error "This should never be used." -- This doesn't make sense.

instance LT Scal where
  zero = 0
  plus = (+)
  inferType = TScal
  scalProd = (*)
  scalDiv = (/)
  minus = (-)

instance KnownNat n => LT (Vect n) where
  zero = V.replicate 0
  plus = V.zipWith (+)
  inferType = TVect (Proxy @n)
  scalProd r = V.map (* r)
  scalDiv v r = V.map (/ r) v
  minus = V.zipWith (-)

instance (LT a, LT b) => LT (a -> b) where
  zero = const zero
  plus f g = \x -> plus (f x) (g x)
  inferType = TArrow inferType inferType
  scalProd r f = \x -> scalProd r (f x)
  scalDiv f r = \x -> scalDiv (f x) r
  minus f g = \x -> minus (f x) (g x)

instance (LT a, LT b) => LT (Tens a b) where
  zero = empty
  plus = (Types.++)
  inferType = TTens inferType inferType
  scalProd = error "This should never be used." -- This doesn't make sense.
  scalDiv = error "This should never be used." -- This doesn't make sense.
  minus = error "This should never be used." -- This doesn't make sense.

instance (LT a, LT b) => LT (LFun a b) where
  zero = MkLFun zero
  plus = lPlus
  inferType = TLinFun inferType inferType
  scalProd = lScalProd
  scalDiv = lScalDiv
  minus = lMinus
