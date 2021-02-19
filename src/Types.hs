{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Different type definitions used in the language
module Types (
    RealN,
    LFun, lId, lConst, lDup, lComp, lApp, lEval, lUncurry, lZipWith, lZipWith', lPair,
          lMapTuple, lAdd, lProd, lSum, lExpand, lPlus, lFst, lSnd,
          lSwap, lCur, lZip, lMap, lRec, lIt,
    Tens, empty, (Types.++), tensFoldr, singleton, isZeroTens,
    Df1, Df2, Dr1, Dr2,
    Type(..), eqTy,
    LT(..),
) where


import Data.Proxy (Proxy, Proxy(Proxy))
import Data.Type.Equality ((:~:)(Refl), (:~:))
import qualified Data.Vector.Unboxed.Sized as V (
    Vector, zipWith, sum, singleton, replicate, index, toList, map
    )
import GHC.TypeNats (KnownNat, sameNat)


-- | Vector of size n containing real values
type RealN n = V.Vector n Double

-- | Tensor products
newtype Tens a b = MkTens [(a, b)]
-- | Linear function
newtype LFun a b = MkLFun (a -> b)

-- Methods for tensor products

-- | Empty tensor product
empty :: Tens a b
empty = MkTens []

(++) :: Tens a b -> Tens a b -> Tens a b
(MkTens x) ++ (MkTens y) = MkTens (x Prelude.++ y)

tensFoldr :: ((a, b) -> c -> c) -> c -> Tens a b -> c
tensFoldr f d (MkTens xs) = foldr f d xs

singleton :: a -> LFun b (Tens a b)
singleton t = MkLFun $ \x -> MkTens [(t, x)]

isZeroTens :: Tens a b -> Bool
isZeroTens (MkTens []) = True
isZeroTens _           = False

-- Methods for linear functions

lId :: LFun a a
lId = MkLFun id

lConst :: b -> LFun a b
lConst x = MkLFun $ const x

lDup :: LFun a (a, a)
lDup = MkLFun $ \a -> (a, a)

lComp :: LFun a b -> LFun b c -> LFun a c
lComp (MkLFun f) (MkLFun g) = MkLFun $ g . f

lApp :: (LT a, LT b) => LFun a b -> a -> b
lApp (MkLFun f) a | isZero a = zero 
                  | otherwise = f a

lEval :: a -> LFun (a -> b) b
lEval x = MkLFun (\f -> f x)

-- | Linear uncurry
lUncurry :: (LT a, LT b, LT c) => (a -> LFun b c) -> LFun (a, b) c
lUncurry f = MkLFun $ uncurry (lApp . f)

-- | Linear zipWith
lZipWith :: (Double -> LFun Double Double) -> RealN n -> LFun (RealN n) (RealN n)
lZipWith f a = MkLFun $ V.zipWith (lApp . f) a

lZipWith' :: (RealN 1 -> LFun (RealN 1) (RealN 1)) -> RealN n -> LFun (RealN n) (RealN n)
lZipWith' f a = MkLFun $ V.zipWith f' a
    where f' x y = V.index (lApp (f (V.singleton x)) (V.singleton y)) 0

lZip :: RealN n -> LFun (RealN n) (Tens (RealN 1) (RealN 1))
lZip x = MkLFun $ \y -> MkTens $ V.toList $ V.zipWith f x y
    where f a b = (V.singleton a, V.singleton b)

-- | Pair two functions
lPair :: (LT a, LT b, LT c) => LFun a b -> LFun a c -> LFun a (b, c)
lPair a b = MkLFun $ \x -> (lApp a x, lApp b x)

-- | Map a tuple
lMapTuple :: (LT a, LT a', LT b, LT b') => LFun a a' -> LFun b b' -> LFun (a, b) (a', b')
lMapTuple f g = MkLFun $ \(a, b) -> (lApp f a, lApp g b)

-- | Addition linear in second argument
lAdd :: Num a => (a -> LFun a a)
lAdd x = MkLFun $ \y -> x + y

-- | Multiplication linear in second argument
lProd :: Num a => (a -> LFun a a)
lProd x = MkLFun $ \y -> x * y

lSum :: LFun (RealN n) (RealN 1)
lSum = MkLFun $ V.singleton . V.sum

lExpand :: KnownNat n => LFun (RealN 1) (RealN n)
lExpand = MkLFun $ \a -> V.replicate $ V.index a 0

lFst :: LFun (a, b) a
lFst = MkLFun fst

lSnd :: LFun (a, b) b
lSnd = MkLFun snd

lSwap :: (LT a, LT b, LT c) => (a -> LFun b c) -> LFun b (a -> c)
lSwap t = MkLFun $ \x y -> lApp (t y) x

lCur :: (LT b, LT c) => ((a, b) -> c -> c) -> LFun (Tens a b) c
lCur f = MkLFun $ tensFoldr f zero

lPlus :: (LT a, LT b) => LFun a b -> LFun a b -> LFun a b
lPlus (MkLFun f) (MkLFun g) = MkLFun $ \x -> plus (f x) (g x)

lMap :: KnownNat n => RealN n -> LFun (RealN 1 -> RealN 1) (RealN n)
lMap x = MkLFun $ \g -> V.map (flip V.index 0 . g . V.singleton) x

lRec :: LFun (a, b) b -> LFun a b -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
lRec (MkLFun g) = MkLFun $ lrec g where 
    lrec f a = f (a, lrec f a)

lIt :: (LT a, LT b) => LFun b (a, b) -> LFun b a -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
lIt (MkLFun g) = MkLFun $ lit g where 
    lit f b = let (a, b') = f b in plus a (MkLFun (lit f) `lApp` b') --- AARGH. THIS IS PROBLEMATIC AS IT'LL NEVER TERMINATE, SEEING THAT plus IS STRICT IN BOTH ARGUMENTS
-- CAN WE MAKE THIS THING TERMINATE UNDER ANY CIRCUMSTANCES? E.G. FIRST ORDER b SO WE CAN CHECK WHETHER THEY ARE 0? (IMPLEMENT TYPE CLASS FOR THIS)
-- SIMILAR IDEA: CAN WE IMPLEMENT ONE FOR ALL TYPES IN THE HIERARCHY? THEN, WE CAN ALSO CHECK WHETHER LINEAR FUNCTIONS ARE ZERO.
-- YES, SO WE SHOULD JUST CHECK WHETHER b' IS 0 AND THEN JUST RETURN a.
-- THE REAL PROBLEM IS THAT + IS STRICT IN BOTH ARGUMENTS, SO THE CONDITIONS FOR DEFINING ITERATION AS A FIXPOINT ARE PROBABLY NOT MET.
-- UNLESS THAT FIXPOINT IS BOT
-- AH! What we really need is to enforce in some way that linear function application is really linear in the sense that 
-- f(0) = 0 even if f=bot. 
-- So linear function application is going to be lazy in the function argument.
-- Of course,this will be a bit hard to achieve at arbitrary types, as we cannot compare for equality.
-- However, perhaps we can do it for all the types that we will need for reverse AD, using some type class? Yes!

-- Forward mode AD type families

type family Df1 a where
    Df1 (RealN n) = RealN n
    Df1 (a -> b)  = Df1 a -> (Df1 b, LFun (Df2 a) (Df2 b))
    Df1 (a, b)    = (Df1 a, Df1 b)
    Df1 ()        = ()
    Df1 (Either a b) = Either (Df1 a) (Df1 b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

type family Df2 a where
    Df2 (RealN n) = RealN n
    Df2 (a -> b)  = Df1 a -> Df2 b
    Df2 (a, b)    = (Df2 a, Df2 b)
    Df2 ()        = ()
    Df2 (Either a b) = (Df2 a, Df2 b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

-- Reverse mode AD type families

type family Dr1 a where
    Dr1 (RealN n) = RealN n
    Dr1 (a -> b)  = Dr1 a -> (Dr1 b, LFun (Dr2 b) (Dr2 a))
    Dr1 (a, b)    = (Dr1 a, Dr1 b)
    Dr1 ()        = ()
    Dr1 (Either a b) = Either (Dr1 a) (Dr1 b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

type family Dr2 a where
    Dr2 (RealN n) = RealN n
    Dr2 (a -> b)  = Tens (Dr1 a) (Dr2 b)
    Dr2 (a, b)    = (Dr2 a, Dr2 b)
    Dr2 ()        = ()
    Dr2 (Either a b) = (Dr2 a, Dr2 b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

data Type a where
    TDouble :: Type Double
    TRealN  :: KnownNat n => Proxy n -> Type (RealN n)
    TArrow  :: Type a -> Type b -> Type (a -> b)
    TPair   :: Type a -> Type b -> Type (a, b)
    TUnit   :: Type ()
    TEither :: Type a -> Type b -> Type (Either a b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES

    TLinFun :: Type a -> Type b -> Type (LFun a b)
    TTens   :: Type a -> Type b -> Type (Tens a b)


eqTy :: Type u -> Type v -> Maybe (u :~: v)
eqTy (TRealN n) (TRealN m) = case sameNat n m of
    Just Refl -> Just Refl
    Nothing   -> Nothing
eqTy TUnit   TUnit  = Just Refl
eqTy (TArrow  u1 u2) (TArrow  v1 v2) =
    do Refl <- eqTy u1 v1
       Refl <- eqTy u2 v2
       return Refl
eqTy (TPair   u1 u2) (TPair   v1 v2) =
    do Refl <- eqTy u1 v1
       Refl <- eqTy u2 v2
       return Refl
eqTy (TLinFun u1 u2) (TLinFun v1 v2) =
    do Refl <- eqTy u1 v1
       Refl <- eqTy u2 v2
       return Refl
eqTy (TTens u1 u2) (TTens v1 v2) =
    do Refl <- eqTy u1 v1
       Refl <- eqTy u2 v2
       return Refl
eqTy _ _ = Nothing


-- | Operators defined over multiple language types
class LT a where
    zero      :: a
    plus      :: a -> a -> a
    inferType :: Type a
    isZero    :: a -> Bool

instance LT () where
    zero      = ()
    plus _ _  = ()
    inferType = TUnit
    isZero    = const True

instance (LT a, LT b) => LT (a, b) where
    zero          = (zero, zero)
    plus a b      = (fst a `plus` fst b, snd a `plus` snd b)
    inferType     = TPair inferType inferType
    isZero (a, b) = isZero a && isZero b

instance (LT a, LT b) => LT (Either a b) where -- EXPERIMENTAL SUPPORT FOR SUM TYPES
    zero      = error "This should never be used." -- This doesn't make sense.
    plus      = error "This should never be used." -- This doesn't make sense.
    inferType = TEither inferType inferType
    isZero    = error "This should never be used." -- This doesn't make sense.

instance LT Double where
    zero      = 0
    plus      = (+)
    inferType = TDouble
    isZero    = (== 0)

instance KnownNat n => LT (RealN n) where
    zero      = V.replicate 0
    plus      = V.zipWith (+)
    inferType = TRealN (Proxy @n)
    isZero    = (== zero)

instance (LT a, LT b) => LT (a -> b) where
    zero      = const zero
    plus f g  = \x -> plus (f x) (g x)
    inferType = TArrow inferType inferType
    isZero    =  error "This should never be used." -- undecidable

instance (LT a, LT b) => LT (Tens a b) where
    zero      = empty
    plus      = (Types.++)
    inferType = TTens inferType inferType
    isZero    = isZeroTens


instance (LT a, LT b) => LT (LFun a b) where
    zero      = lConst zero
    plus      = lPlus
    inferType = TLinFun inferType inferType
    isZero    =  error "This should never be used."-- undecidable
