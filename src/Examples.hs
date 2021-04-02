{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

module Examples where

import           Data.Maybe                (fromMaybe)
import qualified Data.Vector.Unboxed.Sized as V (Unbox, Vector, fromList)
import           Prelude                   hiding (replicate)

import           GHC.TypeNats              (KnownNat)
import           Operation                 (Operation (..))
import qualified SourceLanguage            as SL
import           Types

-- | Helper function to create a vector from a list
fromList' :: (KnownNat n, V.Unbox a) => [a] -> V.Vector n a
fromList' = fromMaybe (error "Incorrect vector size") . V.fromList

-- Constant
constant ::
     (LT b, LT2 a, LT2 b, Show b, b ~ Df1 b, b ~ Dr1 b) => b -> SL.STerm a b
constant c = SL.Comp SL.Unit (SL.Op (Constant c))

-- c * x
cX :: Double -> SL.STerm Scal Scal
cX c = SL.Comp (SL.Pair cons SL.Id) (SL.Op EScalProd)
  where
    cons = constant c

-- x^2
xSquared :: SL.STerm Scal Scal
xSquared = SL.Comp (SL.Pair SL.Id SL.Id) (SL.Op EScalProd)

-- x^3
xCubed :: SL.STerm Scal Scal
xCubed = SL.Comp (SL.Pair xSquared SL.Id) (SL.Op EScalProd)

-- c * x + x^2
quadratic :: Double -> SL.STerm Scal Scal
quadratic c = SL.Comp (SL.Pair (cX c) xSquared) (SL.Op EScalAdd)

-- Map the quadratic function over an input vector
mapQuadratic :: Double -> SL.STerm (Vect 3) (Vect 3)
mapQuadratic c = SL.Comp pair' SL.Map
  where
    mapOp = SL.Curry $ SL.Comp SL.Snd (quadratic c)
    pair' = SL.Pair mapOp SL.Id

-- x
slid :: SL.STerm Scal Scal
slid = SL.Id

-- (x, x)
pair :: SL.STerm Scal (Scal, Scal)
pair = SL.Pair SL.Id SL.Id

-- x + y
add :: SL.STerm (Scal, Scal) Scal
add = SL.Op EScalAdd

-- x * y
prod :: SL.STerm (Scal, Scal) Scal
prod = SL.Op EScalProd

-- (x + y, x + y)
addCopy :: SL.STerm (Scal, Scal) (Scal, Scal)
addCopy = SL.Comp add pair

-- fold (*) 1 xs
foldProd :: KnownNat n => SL.STerm (Vect n) Scal
foldProd =
  SL.Comp
    (SL.Pair
       (SL.Pair (SL.Curry (SL.Comp SL.Snd (SL.Op EScalProd))) (constant 1))
       SL.Id)
    SL.Foldr

-- fold (*) v [1,2,3]
foldProd2 :: SL.STerm Scal Scal
foldProd2 =
  SL.Comp
    (SL.Pair
       (SL.Pair (SL.Curry (SL.Comp SL.Snd (SL.Op EScalProd))) SL.Id)
       (constant v))
    SL.Foldr
  where
    v :: Vect 3
    v = fromList' [1, 2, 3]

-- case t of inl () -> s | inr () -> r
realCase ::
     (LT (Df2 a), LT (Df2 b), LT (Dr2 a), LT (Dr2 b))
  => SL.STerm a (Either () ())
  -> SL.STerm a b
  -> SL.STerm a b
  -> SL.STerm a b
realCase c l r =
  SL.Comp
    (SL.Pair
       (SL.Comp
          c
          (SL.CoPair (SL.Curry (SL.Comp SL.Snd l)) (SL.Curry (SL.Comp SL.Snd r))))
       SL.Id)
    SL.Ev

-- factorial function, implemented using iteration
fact :: SL.STerm Scal Scal
fact =
  SL.Comp
    (SL.Pair SL.Unit (SL.Pair SL.Id (constant 1)))
    (SL.It
       (realCase
          (SL.Comp (SL.Comp SL.Snd SL.Fst) SL.Sign)
          (SL.Comp (SL.Comp SL.Snd SL.Snd) SL.Inl)
          (SL.Comp
             (SL.Pair
                (SL.Comp
                   (SL.Pair (SL.Comp SL.Snd SL.Fst) (constant 1))
                   (SL.Op EScalSubt))
                (SL.Comp
                   (SL.Pair (SL.Comp SL.Snd SL.Fst) (SL.Comp SL.Snd SL.Snd))
                   (SL.Op EScalProd)))
             SL.Inr)))

-- variant of factorial to test derivatives of parameterized iteration w.r.t. parameter
factExtra :: SL.STerm (Scal, Scal) Scal
factExtra =
  SL.Comp
    (SL.Pair SL.Unit SL.Id)
    (SL.It
       (realCase
          (SL.Comp (SL.Comp SL.Snd SL.Fst) SL.Sign)
          (SL.Comp (SL.Comp SL.Snd SL.Snd) SL.Inl)
          (SL.Comp
             (SL.Pair
                (SL.Comp
                   (SL.Pair (SL.Comp SL.Snd SL.Fst) (constant 1))
                   (SL.Op EScalSubt))
                (SL.Comp
                   (SL.Pair (SL.Comp SL.Snd SL.Fst) (SL.Comp SL.Snd SL.Snd))
                   (SL.Op EScalProd)))
             SL.Inr)))

-- factorial function implemented with recursion
fact2 :: SL.STerm Scal Scal
fact2 =
  SL.Pair
    (constant 1 `SL.Comp`
     SL.Rec
       (SL.Curry
          (realCase
             (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt `SL.Comp`
              SL.Sign)
             (SL.Fst `SL.Comp` SL.Fst)
             (SL.Pair
                SL.Snd
                (SL.Pair
                   (SL.Fst `SL.Comp` SL.Snd)
                   (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt) `SL.Comp`
                 SL.Ev) `SL.Comp`
              SL.Op EScalProd))))
    SL.Id `SL.Comp`
  SL.Ev

-- variant of recursive factorial function to test derivative of parameterized recursion w.r.t. parameter
fact2Extra :: SL.STerm (Scal, Scal) Scal
fact2Extra =
  SL.Pair
    (SL.Snd `SL.Comp`
     SL.Rec
       (SL.Curry
          (realCase
             (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt `SL.Comp`
              SL.Sign)
             (SL.Fst `SL.Comp` SL.Fst)
             (SL.Pair
                SL.Snd
                (SL.Pair
                   (SL.Fst `SL.Comp` SL.Snd)
                   (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt) `SL.Comp`
                 SL.Ev) `SL.Comp`
              SL.Op EScalProd))))
    SL.Fst `SL.Comp`
  SL.Ev

-- some recursive function that makes multiple recursive calls, leading to a tree structured form of recursion
tree :: SL.STerm Scal Scal
tree =
  SL.Pair
    (constant 1 `SL.Comp`
     SL.Rec
       (SL.Curry
          (realCase
             (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt `SL.Comp`
              SL.Sign)
             (SL.Fst `SL.Comp` SL.Fst)
             (SL.Pair
                (SL.Pair
                   SL.Snd
                   (SL.Pair
                      (SL.Fst `SL.Comp` SL.Snd)
                      (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt) `SL.Comp`
                    SL.Ev) `SL.Comp`
                 SL.Op EScalProd)
                (SL.Pair
                   (SL.Fst `SL.Comp` SL.Snd)
                   (SL.Pair SL.Snd (constant 0.5) `SL.Comp` SL.Op EScalProd) `SL.Comp`
                 SL.Ev) `SL.Comp`
              SL.Op EScalProd))))
    SL.Id `SL.Comp`
  SL.Ev

-- similar to tree, but to test the derivatives of parameterized recursion w.r.t. the parameter
treeExtra :: SL.STerm (Scal, Scal) Scal
treeExtra =
  SL.Pair
    (SL.Snd `SL.Comp`
     SL.Rec
       (SL.Curry
          (realCase
             (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt `SL.Comp`
              SL.Sign)
             (SL.Fst `SL.Comp` SL.Fst)
             (SL.Pair
                (SL.Pair
                   SL.Snd
                   (SL.Pair
                      (SL.Fst `SL.Comp` SL.Snd)
                      (SL.Pair SL.Snd (constant 1) `SL.Comp` SL.Op EScalSubt) `SL.Comp`
                    SL.Ev) `SL.Comp`
                 SL.Op EScalProd)
                (SL.Pair
                   (SL.Fst `SL.Comp` SL.Snd)
                   (SL.Pair SL.Snd (constant 0.5) `SL.Comp` SL.Op EScalProd) `SL.Comp`
                 SL.Ev) `SL.Comp`
              SL.Op EScalProd))))
    SL.Fst `SL.Comp`
  SL.Ev
