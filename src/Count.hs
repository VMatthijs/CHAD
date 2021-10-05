{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Count where


data Layout t a where
  LyLeaf :: a -> Layout t a
  LyPair :: Layout t1 a -> Layout t2 a -> Layout (t1, t2) a
deriving instance Show a => Show (Layout t a)

instance Functor (Layout t) where
  fmap f (LyLeaf x)     = LyLeaf (f x)
  fmap f (LyPair l1 l2) = LyPair (fmap f l1) (fmap f l2)

instance Foldable (Layout t) where
  foldMap f (LyLeaf x)     = f x
  foldMap f (LyPair l1 l2) = foldMap f l1 <> foldMap f l2

instance Semigroup a => Semigroup (Layout t a) where
  LyLeaf a <> LyLeaf b = LyLeaf (a <> b)
  LyLeaf n <> LyPair l1 l2 = LyPair (fmap (n <>) l1) (fmap (n <>) l2)
  LyPair l1 l2 <> LyLeaf n = LyPair (fmap (<> n) l1) (fmap (<> n) l2)
  LyPair l1 l2 <> LyPair l3 l4 = LyPair (l1 <> l3) (l2 <> l4)

instance Monoid a => Monoid (Layout t a) where
  mempty = LyLeaf mempty

data TupPick large small where
  TPHere :: TupPick t t
  TPFst :: TupPick t (a, b) -> TupPick t a
  TPSnd :: TupPick t (a, b) -> TupPick t b

layoutFromPick :: (Num s, Monoid s) => TupPick t t' -> Layout t s
layoutFromPick = go (LyLeaf 1)
  where
    go :: (Num s, Monoid s) => Layout t' s -> TupPick t t' -> Layout t s
    go l TPHere = l
    go l (TPFst p) = go (LyPair l mempty) p
    go l (TPSnd p) = go (LyPair mempty l) p
