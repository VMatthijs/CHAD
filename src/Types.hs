{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
-- | Different type definitions used in the language
module Types (
    RealN,
    LFun, lId, lConst, lDup, lComp, lApp, lEval, lUncurry, lZipWith, lZipWith', lPair,
          lMapTuple, lAdd, lProd, lSum, lExpand, lPlus, lFst, lSnd,
          lSwap, lCur, lZip, lMap, lRec, lIt,
    Tens, empty, (Types.++), tensFoldr, singleton,
    Df1, Df2, Dr1, Dr2,
    Type(..), eqTy,
    LT(..),
) where


import Data.Proxy (Proxy)
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

-- Methods for linear functions

lId :: LFun a a
lId = MkLFun id

lConst :: b -> LFun a b
lConst x = MkLFun $ const x

lDup :: LFun a (a, a)
lDup = MkLFun $ \a -> (a, a)

lComp :: LFun a b -> LFun b c -> LFun a c
lComp (MkLFun f) (MkLFun g) = MkLFun $ g . f

lApp :: LFun a b -> a -> b
lApp (MkLFun f) = f

lEval :: a -> LFun (a -> b) b
lEval x = MkLFun (\f -> f x)

-- | Linear uncurry
lUncurry :: (a -> LFun b c) -> LFun (a, b) c
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
lPair :: LFun a b -> LFun a c -> LFun a (b, c)
lPair a b = MkLFun $ \x -> (lApp a x, lApp b x)

-- | Map a tuple
lMapTuple :: LFun a a' -> LFun b b' -> LFun (a, b) (a', b')
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

lSwap :: (a -> LFun b c) -> LFun b (a -> c)
lSwap t = MkLFun $ \x y -> lApp (t y) x

lCur :: (LT b, LT c) => ((a, b) -> c -> c) -> LFun (Tens a b) c
lCur f = MkLFun $ tensFoldr f zero

lMap :: KnownNat n => RealN n -> LFun (RealN 1 -> RealN 1) (RealN n)
lMap x = MkLFun $ \g -> V.map (flip V.index 0 . g . V.singleton) x

lRec :: LFun (a, b) b -> LFun a b -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
lRec (MkLFun g) = MkLFun $ lrec g where 
    lrec f a = f (a, lrec f a)

lIt :: LT a => LFun b (a, b) -> LFun b a -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
lIt (MkLFun g) = MkLFun $ lit g where 
    lit f b = let (a, b') = f b in plus a (lit f b) --- AARGH. THIS IS PROBLEMATIC AS IT'LL NEVER TERMINATE, SEEING THAT plus IS STRICT IN BOTH ARGUMENTS
-- CAN WE MAKE THIS THING TERMINATE UNDER ANY CIRCUMSTANCES? E.G. FIRST ORDER a, b SO WE CAN CHECK WHETHER THEY ARE 0?

-- Forward mode AD type families

type family Df1 a = r | r -> a where
    Df1 (RealN n) = RealN n
    Df1 (a -> b)  = Df1 a -> (Df1 b, LFun (Df2 a) (Df2 b))
    Df1 (a, b)    = (Df1 a, Df1 b)
    Df1 ()        = ()

type family Df2 a = r | r -> a where
    Df2 (RealN n) = RealN n
    Df2 (a -> b)  = Df1 a -> Df2 b
    Df2 (a, b)    = (Df2 a, Df2 b)
    Df2 ()        = ()

-- Reverse mode AD type families

type family Dr1 a = r | r -> a where
    Dr1 (RealN n) = RealN n
    Dr1 (a -> b)  = Dr1 a -> (Dr1 b, LFun (Dr2 b) (Dr2 a))
    Dr1 (a, b)    = (Dr1 a, Dr1 b)
    Dr1 ()        = ()

type family Dr2 a = r | r -> a where
    Dr2 (RealN n) = RealN n
    Dr2 (a -> b)  = Tens (Dr1 a) (Dr2 b)
    Dr2 (a, b)    = (Dr2 a, Dr2 b)
    Dr2 ()        = ()

data Type a where
    TRealN  :: KnownNat n => Proxy n -> Type (RealN n)
    TArrow  :: Type a -> Type b -> Type (a -> b)
    TPair   :: Type a -> Type b -> Type (a, b)
    TUnit   :: Type ()

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

lPlus :: (LT a, LT b) => LFun a b -> LFun a b -> LFun a b
lPlus (MkLFun f) (MkLFun g) = MkLFun $ \x -> plus (f x) (g x)
