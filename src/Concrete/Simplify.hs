{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Simplify terms in the target language to aid legibility.
--
-- This should only do simplifications that any basic compiler
-- would also perform.
module Concrete.Simplify (
  simplifyCTerm,
) where

import           Data.Foldable      (fold)
import qualified Data.Monoid        as Mon
import           Numeric.Natural

import           Concrete
import           Env
import           Types

-- | Simplify a 'CTerm' using some basic rewriting optimisations.
--
-- Note: inlining of variable definitions is only performed if the variable in
-- question is only used once, or, if it is a 'Pair' expression, if its
-- components are each used at most once due to uses of 'Fst' and 'Snd'.
simplifyCTerm :: CTerm env a -> CTerm env a
simplifyCTerm (CVar i) = CVar i
simplifyCTerm (CLambda e) = CLambda (simplifyCTerm e)
simplifyCTerm (CLet rhs e) = simplifyLet (simplifyCTerm rhs) (simplifyCTerm e)
simplifyCTerm (CApp f a) = simplifyApp (simplifyCTerm f) (simplifyCTerm a)
simplifyCTerm CUnit = CUnit
simplifyCTerm (CPair a b) = CPair (simplifyCTerm a) (simplifyCTerm b)
simplifyCTerm (CFst p) = simplifyFst (simplifyCTerm p)
simplifyCTerm (CSnd p) = simplifySnd (simplifyCTerm p)
simplifyCTerm (COp op a) = COp op (simplifyCTerm a)
simplifyCTerm (CMap a b) = CMap (simplifyCTerm a) (simplifyCTerm b)
simplifyCTerm (CZipWith a b c) = CZipWith (simplifyCTerm a) (simplifyCTerm b) (simplifyCTerm c)
simplifyCTerm (CReplicate x) = CReplicate (simplifyCTerm x)
simplifyCTerm (CSum a) = CSum (simplifyCTerm a)
simplifyCTerm (CToList a) = CToList (simplifyCTerm a)
simplifyCTerm CLNil = CLNil
simplifyCTerm (CLCons a b) = CLCons (simplifyCTerm a) (simplifyCTerm b)
simplifyCTerm (CLMap a b) = CLMap (simplifyCTerm a) (simplifyCTerm b)
simplifyCTerm (CLFoldr a b c) = CLFoldr (simplifyCTerm a) (simplifyCTerm b) (simplifyCTerm c)
simplifyCTerm (CLSum a) = CLSum (simplifyCTerm a)
simplifyCTerm (CLZipWith a b c) = CLZipWith (simplifyCTerm a) (simplifyCTerm b) (simplifyCTerm c)
simplifyCTerm CZero = CZero
simplifyCTerm (CPlus a b) = simplifyPlus (simplifyCTerm a) (simplifyCTerm b)

-- | Simplify the App form. This converts immediate lambda application into
-- let-binding.
simplifyApp :: CTerm env (a -> b) -> CTerm env a -> CTerm env b
simplifyApp (CLambda e) a = simplifyLet a e
simplifyApp CZero _ = CZero
simplifyApp f a = CApp f a

-- | Simplify the Let form.
--
-- We perform let-of-pair splitting.
simplifyLet :: CTerm env a -> CTerm (a ': env) b -> CTerm env b
simplifyLet (CLet rhs e) body =
  simplifyLet rhs (simplifyLet e (sinkCt (wSink (wSucc wId)) body))
simplifyLet (CPair a1 a2) e =
  simplifyLet a1 $
    simplifyLet (sinkCt (wSucc wId) a2) $
      simplifyCTerm $ substCt (wSucc (wSucc wId)) (CPair (CVar (S Z)) (CVar Z)) e
simplifyLet a e
  | duplicable a || (fold (usesOf' Z e) :: Mon.Sum Natural) <= 1
  = simplifyCTerm $ substCt wId a e
  | otherwise
  = CLet a e

duplicable :: CTerm env a -> Bool
duplicable CVar{} = True
duplicable CUnit{} = True
duplicable (CPair a b) = duplicable a && duplicable b
duplicable (CFst e) = duplicable e
duplicable (CSnd e) = duplicable e
duplicable (CPlus a b) = duplicable a && duplicable b
duplicable CZero = True
duplicable _ = False

-- | Simplify the Fst form
simplifyFst :: CTerm env (a, b) -> CTerm env a
simplifyFst (CPair t _)  = t
simplifyFst (CLet rhs e) = simplifyLet rhs (simplifyFst e)
simplifyFst p            = CFst p

-- | Simplify the Snd form
simplifySnd :: CTerm env (a, b) -> CTerm env b
simplifySnd (CPair _ s)  = s
simplifySnd (CLet rhs e) = simplifyLet rhs (simplifySnd e)
simplifySnd p            = CSnd p

-- | Simplify the Plus form
simplifyPlus :: LT a => CTerm env a -> CTerm env a -> CTerm env a
simplifyPlus a CZero = a
simplifyPlus CZero b = b
simplifyPlus a b     = CPlus a b
