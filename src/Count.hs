{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Utilities for occurrence counting in functional languages.
module Count where

import Numeric.Natural


-- | A @Layout t a@ is a tree that counts usages of a variable of type @t@,
-- split out over components of nested pairs. The count is expressed using the
-- type @a@.
--
-- For example, the occurrence of @x@ in @f x@ would count as @'LyLeaf' 1@,
-- whereas the occurrence of @x@ in @f (fst x)@ would count as
-- @'LyPair' ('LyLeaf' 1) ('LyLeaf' 0)@.
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

layoutFromPick :: Monoid s => s -> TupPick t t' -> Layout t s
layoutFromPick one = go (LyLeaf one)
  where
    go :: Monoid s => Layout t' s -> TupPick t t' -> Layout t s
    go l TPHere = l
    go l (TPFst p) = go (LyPair l mempty) p
    go l (TPSnd p) = go (LyPair mempty l) p

-- | Either a finite number or "many". 'Many' is considered larger than all
-- finite numbers but not infinite, so @0 * Many = 0@.
--
-- This type should be used with an unsigned argument like 'Numeric.Natural',
-- because there is no negative version of 'Many'.
data FiniteOrMany a = Finite a | Many
  deriving (Show, Eq, Ord)

instance (Num a, Eq a) => Num (FiniteOrMany a) where
  Finite x + Finite y = Finite (x + y)
  Many + _ = Many
  _ + Many = Many

  Finite x * Finite y = Finite (x * y)
  Many * Finite 0 = Finite 0
  Many * _ = Many
  Finite 0 * Many = Finite 0
  _ * Many = Many

  fromInteger = Finite . fromInteger

  abs (Finite x) = Finite (abs x)
  abs Many = Many

  signum (Finite 0) = Finite 0
  signum _ = Finite 1

  negate (Finite x) = Finite (negate x)
  negate Many = error "negate Many"

-- | The number of occurrences of a variable in an expression. This is split
-- out in the number of /syntactic occurrences/ (the number of times the
-- variable appears in the expression as written) and the number of /dynamic
-- occurrences/ (an upper bound on the number of runtime computations of a
-- value inlined for the variable in question). The number of dynamic
-- occurrences ('runtimeOccs') may be 'Many' if the exact number depends on
-- quantities that are unknown at compile time.
--
-- It is important that we count both of these things because when deciding
-- whether to inline a variable in a let-binding, we have two considerations:
--
-- 1. We do not want to significantly increase code size by duplication of the
--    inlined value. This means that we may only inline if the variable appears
--    only once syntactically, or the value to be inlined is itself considered
--    small enough to duplicate.
--
-- 2. We do not want to increase runtime by destroying sharing that the
--    let-binding gave us. This means that we may only inline if we can prove
--    that once inlined, the value that replaces the variable will only be
--    executed (at most) once if the former let-expression would be executed
--    once -- that, or we consider the value to be inlined so trivial to
--    compute that we are allowed to duplicate its computation.
--
-- In general these considerations differ on precisely one point: their
-- treatment of function abstractions. Function abstractions can be
-- syntactically arbitrarily large but have no inherent runtime cost (only
-- their /execution/ has actual runtime cost). (We consider the construction of
-- a closure object to be trivial runtime cost.) Hence, if they appear just
-- once syntactically, they are allowed to be inlined in another function
-- abstraction: the lambda itself might then get computed multiple times, but
-- the number of times it gets /called/ doesn't change. Using purely dynamic
-- occurrence counting would prohibit such an inlining; this is quite
-- disastrous for the readability of CHAD's transformed output because of all
-- the linear functions (which act as continuations that get composed
-- together).
data OccCount = OccCount
  { -- | The number of syntactic occurrences. This counts @\a -> x@ as having
    -- one occurrence of @x@.
    syntacticOccs :: Natural
  , -- | An upper bound on the number of runtime computations of a value
    -- inlined for this variable. This counts @\a -> x@ as having 'Many'
    -- occurrences of @x@.
    runtimeOccs :: FiniteOrMany Natural
  }

instance Semigroup OccCount where
  OccCount a b <> OccCount a' b' = OccCount (a + a') (b + b')

instance Monoid OccCount where
  mempty = OccCount 0 0

-- | Given an occurrence count of a variable inside a loop or function
-- abstraction, return the occurrence count of that variable as seen from
-- outside the loop or function abstraction. This multiplies the runtime
-- occurrence count ('runtimeOccs') with 'Many'.
occRepeatRuntime :: OccCount -> OccCount
occRepeatRuntime count = count { runtimeOccs = Many * runtimeOccs count }
