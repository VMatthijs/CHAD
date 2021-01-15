{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Types (
    RealN,
    LFun(..), lId, lConst, lDup, lComp, lApp, lUncurry, lZipWith, lPair,
          lMapTuple, lAdd, lProd, lSum, lExpand, lPlus, lFst, lSnd,
          lSwap, lCur,
    Tens(..), empty, (Types.++), tensFoldr, singleton,
    Df1, Df2, Dr1, Dr2,
    Type(..), eqTy,
    LT(..),
) where


import Data.Proxy (Proxy)
import Data.Type.Equality ((:~:)(Refl), (:~:))
import qualified Data.Vector.Unboxed.Sized as V (Vector, zipWith, sum, singleton, replicate, index)
import GHC.TypeNats (KnownNat, sameNat)

-- | Vector of size n containing real values
type RealN n = V.Vector n Double

-- | Tensor products
newtype Tens a b = Tens [(a, b)]
-- | Linear function
newtype LFun a b = LFun (a -> b)

-- Methods for tensor products

-- | Empty tensor product
empty :: Tens a b
empty = Tens []

(++) :: Tens a b -> Tens a b -> Tens a b
(Tens x) ++ (Tens y) = Tens (x Prelude.++ y)

tensFoldr :: ((a, b) -> c -> c) -> c -> Tens a b -> c
tensFoldr f d (Tens xs) = foldr f d xs

singleton :: a -> LFun b (Tens a b)
singleton t = LFun $ \x -> Tens [(t, x)]

-- Methods for linear functions

lId :: LFun a a
lId = LFun id

lConst :: b -> LFun a b
lConst x = LFun $ const x

lDup :: LFun a (a, a)
lDup = LFun $ \a -> (a, a)

lComp :: LFun a b -> LFun b c -> LFun a c
lComp (LFun f) (LFun g) = LFun $ g . f

lApp :: LFun a b -> a -> b
lApp (LFun f) = f

-- | Linear uncurry
lUncurry :: (a -> LFun b c) -> LFun (a, b) c
lUncurry f = LFun $ uncurry (lApp . f)

-- | Linear zipWith
lZipWith :: (Double -> LFun Double Double) -> RealN n -> LFun (RealN n) (RealN n)
lZipWith f a = LFun $ V.zipWith (lApp . f) a

-- | Pair two functions
lPair :: LFun a b -> LFun a c -> LFun a (b, c)
lPair a b = LFun $ \x -> (lApp a x, lApp b x)

-- | Map a tuple
lMapTuple :: LFun a a' -> LFun b b' -> LFun (a, b) (a', b')
lMapTuple f g = LFun $ \(a, b) -> (lApp f a, lApp g b)

-- | Addition linear in second argument
lAdd :: Num a => (a -> LFun a a)
lAdd x = LFun $ \y -> x + y

-- | Multiplication linear in second argument
lProd :: Num a => (a -> LFun a a)
lProd x = LFun $ \y -> x * y

lSum :: LFun (RealN n) (RealN 1)
lSum = LFun $ V.singleton . V.sum

lExpand :: KnownNat n => LFun (RealN 1) (RealN n)
lExpand = LFun $ \a -> V.replicate $ V.index a 0

lFst :: LFun (a, b) a
lFst = LFun fst

lSnd :: LFun (a, b) b
lSnd = LFun snd

lSwap :: (a -> LFun b c) -> LFun b (a -> c)
lSwap t = LFun $ \x y -> lApp (t y) x

lCur :: (LT b, LT c) => ((a, b) -> c -> c) -> LFun (Tens a b) c
lCur f = LFun $ tensFoldr f zero

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
lPlus (LFun f) (LFun g) = LFun $ \x -> plus (f x) (g x)
