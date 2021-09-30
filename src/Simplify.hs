{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Simplify terms in the target language to aid legibility.
--
-- This should only do simplifications that any basic compiler
-- would also perform.
module Simplify (
  simplifyTTerm,
) where

import           Data.Foldable      (fold)
import           Data.Monoid        (Sum (..))
import           Numeric.Natural

import           TargetLanguage
import           Env
import           Types

-- | Simplify a 'TTerm' using some basic rewriting optimisations.
--
-- Note: inlining of variable definitions is only performed if the variable in
-- question is only used once, or, if it is a 'Pair' expression, if its
-- components are each used at most once due to uses of 'Fst' and 'Snd'.
simplifyTTerm :: TTerm env a -> TTerm env a
simplifyTTerm (Var i) = Var i
simplifyTTerm (Lambda e) = Lambda (simplifyTTerm e)
simplifyTTerm (Let rhs e) = simplifyLet (simplifyTTerm rhs) (simplifyTTerm e)
simplifyTTerm (App f a) = simplifyApp (simplifyTTerm f) (simplifyTTerm a)
simplifyTTerm Unit = Unit
simplifyTTerm (Pair a b) = Pair (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm (Fst p) = simplifyFst (simplifyTTerm p)
simplifyTTerm (Snd p) = simplifySnd (simplifyTTerm p)
simplifyTTerm (Op op a) = Op op (simplifyTTerm a)
simplifyTTerm (Map a b) = Map (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm (AdjPlus a b) = simplifyPlus (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm Zero = Zero
simplifyTTerm (LinFun f) = LinFun (simplifyLinTTerm f)

-- | Simplify a 'LinTTerm' using some basic rewriting optimisations.
simplifyLinTTerm :: LinTTerm env a b -> LinTTerm env a b
simplifyLinTTerm (LinApp term a) = simplifyLinApp (simplifyTTerm term) (simplifyLinTTerm a)
simplifyLinTTerm (LinLet rhs e) = simplifyLinLet (simplifyLinTTerm rhs) (simplifyLinTTerm e)
simplifyLinTTerm LinVar = LinVar
simplifyLinTTerm (LinPair a b) = LinPair (simplifyLinTTerm a) (simplifyLinTTerm b)
simplifyLinTTerm (LinFst p) = simplifyLinFst (simplifyLinTTerm p)
simplifyLinTTerm (LinSnd p) = simplifyLinSnd (simplifyLinTTerm p)
simplifyLinTTerm (LinLOp lop term arg) = LinLOp lop (simplifyTTerm term) (simplifyLinTTerm arg)
simplifyLinTTerm LinZero = LinZero
simplifyLinTTerm (LinPlus a b) = simplifyLinPlus (simplifyLinTTerm a) (simplifyLinTTerm b)
simplifyLinTTerm (LinSingleton term b) = LinSingleton (simplifyTTerm term) (simplifyLinTTerm b)
simplifyLinTTerm (LinCopowFold term b) = LinCopowFold (simplifyTTerm term) (simplifyLinTTerm b)

-- | Simplify the App form. This converts immediate lambda application into
-- let-binding.
simplifyApp :: TTerm env (a -> b) -> TTerm env a -> TTerm env b
simplifyApp (Lambda e) a = simplifyLet a e
simplifyApp Zero _ = Zero
simplifyApp f a = App f a

-- | Simplify the LinApp form. This converts immediate lambda application into
-- let-binding.
simplifyLinApp :: (LT a, LT b, LT c) => TTerm env (LFun b c) -> LinTTerm env a b -> LinTTerm env a c
simplifyLinApp (LinFun e) a = simplifyLinLet a e
simplifyLinApp Zero _ = LinZero
simplifyLinApp f a = LinApp f a

-- | Simplify the Let form.
--
-- We perform let-of-pair splitting.
simplifyLet :: TTerm env a -> TTerm (a ': env) b -> TTerm env b
simplifyLet (Let rhs e) body =
  simplifyLet rhs (simplifyLet e (sinkTt (wSink (wSucc wId)) body))
simplifyLet (Pair a1 a2) e =
  simplifyLet a1 $
    simplifyLet (sinkTt (wSucc wId) a2) $
      simplifyTTerm $ substTt (wSucc (wSucc wId)) (Pair (Var (S Z)) (Var Z)) e
simplifyLet a e
  | duplicable a || (fold (usesOf' Z e) :: Sum Natural) <= 1
  = simplifyTTerm $ substTt wId a e
  | otherwise
  = Let a e

simplifyLinLet :: (LT a, LT s, LT t) => LinTTerm env a s -> LinTTerm env s t -> LinTTerm env a t
simplifyLinLet LinVar body = body
simplifyLinLet rhs body
  | let count = usesOfLinVar body
  , decideInlinableLin count rhs
  = simplifyLinTTerm $ substLinVar rhs body
  | otherwise
  = LinLet rhs body

decideInlinableLin :: Layout b (Sum Natural) -> LinTTerm env a b -> Bool
decideInlinableLin (LyPair ly1 ly2) (LinPair e1 e2) =
  decideInlinableLin ly1 e1 && decideInlinableLin ly2 e2
decideInlinableLin (fold -> count) e = count <= 1 || duplicableLin e

duplicable :: TTerm env a -> Bool
duplicable Var{} = True
duplicable Unit{} = True
duplicable (Pair a b) = duplicable a && duplicable b
duplicable (Fst e) = duplicable e
duplicable (Snd e) = duplicable e
duplicable (AdjPlus a b) = duplicable a && duplicable b
duplicable Zero = True
duplicable (LinFun _) = False  -- TODO: something here?
duplicable _ = False

duplicableLin :: LinTTerm env a b -> Bool
duplicableLin LinVar = True
duplicableLin (LinPair a b) = duplicableLin a && duplicableLin b
duplicableLin (LinFst e) = duplicableLin e
duplicableLin (LinSnd e) = duplicableLin e
duplicableLin (LinPlus a b) = duplicableLin a && duplicableLin b
duplicableLin LinZero = True
duplicableLin _ = False

-- | Simplify the Fst form
simplifyFst :: TTerm env (a, b) -> TTerm env a
simplifyFst (Pair t _)  = t
simplifyFst (Let rhs e) = simplifyLet rhs (simplifyFst e)
simplifyFst p           = Fst p

-- | Simplify the LinFst form
simplifyLinFst :: (LT s, LT a, LT b) => LinTTerm env s (a, b) -> LinTTerm env s a
simplifyLinFst (LinPair t _) = t
-- simplifyLinFst (Let rhs e) = simplifyLet rhs (simplifyLinFst e)
simplifyLinFst p             = LinFst p

-- | Simplify the LinSnd form
simplifyLinSnd :: (LT s, LT a, LT b) => LinTTerm env s (a, b) -> LinTTerm env s b
simplifyLinSnd (LinPair _ t) = t
-- simplifyLinSnd (Let rhs e) = simplifyLet rhs (simplifyLinSnd e)
simplifyLinSnd p             = LinSnd p

-- | Simplify the Snd form
simplifySnd :: TTerm env (a, b) -> TTerm env b
simplifySnd (Pair _ s)  = s
simplifySnd (Let rhs e) = simplifyLet rhs (simplifySnd e)
simplifySnd p           = Snd p

-- | Simplify the Plus form
simplifyPlus :: LT a => TTerm env a -> TTerm env a -> TTerm env a
simplifyPlus a Zero = a
simplifyPlus Zero b = b
simplifyPlus a b    = AdjPlus a b

simplifyLinPlus :: (LT a, LT b) => LinTTerm env a b -> LinTTerm env a b -> LinTTerm env a b
simplifyLinPlus a LinZero = a
simplifyLinPlus LinZero b = b
simplifyLinPlus (LinPair a b) (LinPair a' b') =
  simplifyLinTTerm (LinPair (LinPlus a a') (LinPlus b b'))
simplifyLinPlus a b = LinPlus a b
