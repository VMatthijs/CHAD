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

-- | Simplify a TTerm using some basic rewriting optimisations.
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
simplifyTTerm LId = LId
simplifyTTerm (LPair a b) = LPair (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm LFst = LFst
simplifyTTerm LSnd = LSnd
simplifyTTerm (LComp f g) = simplifyLComp (simplifyTTerm f) (simplifyTTerm g)
simplifyTTerm (LSingleton e) = LSingleton (simplifyTTerm e)
simplifyTTerm (LCopowFold e) = LCopowFold (simplifyTTerm e)
simplifyTTerm (LOp lop) = LOp lop

-- | Simplify the App form. This converts immediate lambda application into
-- let-binding.
simplifyApp :: TTerm env (a -> b) -> TTerm env a -> TTerm env b
simplifyApp (Lambda e) a = simplifyLet a e
simplifyApp Zero _ = Zero
simplifyApp f a = App f a

-- | Simplify the Let form.
--
-- We allow substituting Pair expressions where each element of the pair is
-- individually only used once in the body (because of Fst and Snd
-- projections).
simplifyLet :: TTerm env a -> TTerm (a ': env) b -> TTerm env b
simplifyLet (Let rhs e) body =
  simplifyLet rhs (simplifyLet e (sinkTt (wSink (wSucc wId)) body))
simplifyLet (Pair a1 a2) e =
  simplifyLet a1 $
    simplifyLet (sinkTt (wSucc wId) a2) $
      simplifyTTerm $ substTt (wSucc (wSucc wId)) (Pair (Var (S Z)) (Var Z)) e
simplifyLet a e
  | decideInlinable (usesOf' Z e :: Layout (Sum Natural)) a
  = simplifyTTerm $ substTt wId a e
  | otherwise
  = Let a e

decideInlinable :: (Num s, Ord s) => Layout (Sum s) -> TTerm env a -> Bool
decideInlinable (LyPair ly1 ly2) (Pair e1 e2) =
  decideInlinable ly1 e1 && decideInlinable ly2 e2
decideInlinable (fold -> count) e = count <= 1 || duplicable e

duplicable :: TTerm env a -> Bool
duplicable Var{} = True
duplicable Unit{} = True
duplicable (Pair a b) = duplicable a && duplicable b
duplicable (Fst e) = duplicable e
duplicable (Snd e) = duplicable e
duplicable (AdjPlus a b) = duplicable a && duplicable b
duplicable Zero = True
duplicable LId = True
duplicable (LPair a b) = duplicable a && duplicable b
duplicable LFst = True
duplicable LSnd = True
duplicable (LSingleton e) = duplicable e
duplicable (LCopowFold e) = duplicable e
duplicable _ = False

-- | Simplify the Fst form
simplifyFst :: TTerm env (a, b) -> TTerm env a
simplifyFst (Pair t _)  = t
simplifyFst (Let rhs e) = simplifyLet rhs (simplifyFst e)
simplifyFst p           = Fst p

-- | Simplify the Snd form
simplifySnd :: TTerm env (a, b) -> TTerm env b
simplifySnd (Pair _ s)  = s
simplifySnd (Let rhs e) = simplifyLet rhs (simplifySnd e)
simplifySnd p           = Snd p

data LComps env a b where
  LComps :: (LT a, LT b, LT c) => TTerm env (LFun a b) -> LComps env b c -> LComps env a c
  LCompsDone :: LT a => LComps env a a

-- | Simplify the LComp form
simplifyLComp :: (LT a, LT b, LT c) => TTerm env (LFun a b) -> TTerm env (LFun b c) -> TTerm env (LFun a c)
simplifyLComp f1 f2 =
  uncollect . goRev . goFwd . collect simplifyTTerm $ LComp f1 f2
  where
    collect :: (LT a, LT b)
            => (forall c d. TTerm env (LFun c d) -> TTerm env (LFun c d))
            -> TTerm env (LFun a b) -> LComps env a b
    collect conv (LComp a b) = app (collect conv a) (collect conv b)
    collect conv f = LComps (conv f) LCompsDone

    app :: LT c => LComps env a b -> LComps env b c -> LComps env a c
    app (LComps f fs) l = LComps f (app fs l)
    app LCompsDone l = l

    goFwd :: LComps env a b -> LComps env a b
    goFwd LCompsDone                             = LCompsDone
    goFwd (LComps LId l)                         = goFwd l
    goFwd (LComps (LPair a _) (LComps LFst{} l)) = goFwd (LComps a l)
    goFwd (LComps (LPair _ b) (LComps LSnd{} l)) = goFwd (LComps b l)
    goFwd (LComps f l)                           = LComps f (goFwd l)

    goRev :: LComps env a b -> LComps env a b
    goRev LCompsDone = LCompsDone
    goRev (LComps f l) = case (f, goRev l) of
        (_, LComps Zero l') -> LComps Zero l'
        (_, l') -> LComps f l'

    uncollect :: LComps env a b -> TTerm env (LFun a b)
    uncollect LCompsDone = LId
    uncollect (LComps f LCompsDone) = f
    uncollect (LComps f l) = LComp f (uncollect l)

-- | Simplify the Plus form
simplifyPlus :: LT a => TTerm env a -> TTerm env a -> TTerm env a
simplifyPlus a Zero = a
simplifyPlus Zero b = b
simplifyPlus a b    = AdjPlus a b
