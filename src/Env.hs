{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE EmptyCase          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}

-- | De Bruijn environment and index definitions.
--
-- Our embedded languages use a well-typed well-scoped De Bruijn representation;
-- in order to do this in Haskell, a term has a type-level
-- environment containing the types of the bound variables that are in scope.
-- This module contains definitions for indices into such an environment (used
-- for representing /variables/ in the target language) as well as some
-- utilities for working with such environments.
module Env where

import Data.GADT.Compare
import Data.Type.Equality ((:~:)(Refl))


-- | Typed De Bruijn index
data Idx env t where
  Z :: Idx (t ': env) t
  S :: Idx env t -> Idx (s ': env) t

deriving instance Show (Idx env t)

-- | Forget type information from a De Bruijn index and realise it as an integer
idxToInt :: Idx env t -> Int
idxToInt Z = 0
idxToInt (S i) = succ (idxToInt i)

-- instance Show (Idx env t) where
--   showsPrec d idx = showParen (d > 10) $ showString ("Idx " ++ show (idxToInt idx))

instance GEq (Idx env) where
  geq Z Z = Just Refl
  geq (S i) (S i')
    | Just Refl <- geq i i'
    = Just Refl
  geq _ _ = Nothing

-- | Valuation; the environment in an interpreter
data Val env where
  VZ :: Val '[]
  VS :: t -> Val env -> Val (t ': env)

-- | Project a value from a valuation
valProject :: Val env -> Idx env t -> t
valProject (VS x _) Z = x
valProject (VS _ env) (S i) = valProject env i

-- | An index transformation function, generally for weakening environments
newtype env :> env' = Weaken { (>:>) :: forall t'. Idx env t' -> Idx env' t' }

-- | Compose index transformation functions
infixr 9 .>
(.>) :: env2 :> env3 -> env1 :> env2 -> env1 :> env3
Weaken f .> Weaken g = Weaken (f . g)

wId :: env :> env
wId = Weaken id

wSucc :: env :> env' -> env :> (t ': env')
wSucc = (Weaken S .>)

wRaise :: (t ': env) :> env' -> env :> env'
wRaise = (.> Weaken S)

wSink :: env :> env' -> (t ': env) :> (t ': env')
wSink w = Weaken (\case Z -> Z ; S i -> S (w >:> i))

wNil :: '[] :> env
wNil = Weaken (\case {})
