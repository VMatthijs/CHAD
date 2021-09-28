{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Simplify terms in the target language to aid legibility.
--
-- This should only do simplifications that any basic compiler
-- would also perform.
module Lambda.Simplify (
  simplify,
) where

import           Data.Foldable      (fold)
import           Data.Monoid        (Sum (..))
import           Numeric.Natural

import           Lambda
import           TargetLanguage.Env
import           Types

-- | Simplify a Lambda term using some basic rewriting optimisations.
--
-- Note: inlining of variable definitions is only performed if the variable in
-- question is only used once, or, if it is a 'Pair' expression, if its
-- components are each used at most once due to uses of 'Fst' and 'Snd'.
simplify :: Lambda env a -> Lambda env a
-- Source language extension
simplify (Var t i) = Var t i
simplify (Lambda t e) = Lambda t (simplify e)
simplify (Let rhs e) = simplifyLet (simplify rhs) (simplify e)
simplify (App f a) = simplifyApp (simplify f) (simplify a)
simplify Unit = Unit
simplify (Pair a b) = Pair (simplify a) (simplify b)
simplify (Fst p) = simplifyFst (simplify p)
simplify (Snd p) = simplifySnd (simplify p)
simplify (Op t op a) = Op t op (simplify a)
simplify (AdjPlus a b) = simplifyPlus (simplify a) (simplify b)
simplify (Zero t) = Zero t
simplify (LId t) = LId t
simplify (LPair a b) = LPair (simplify a) (simplify b)
simplify (LFst t1 t2) = LFst t1 t2
simplify (LSnd t1 t2) = LSnd t1 t2
simplify (LComp f g) = simplifyLComp (simplify f) (simplify g)
simplify (LSingleton t e) = LSingleton t (simplify e)
simplify (LCopowFold e) = LCopowFold (simplify e)
simplify (LOp lop) = LOp lop

-- | Simplify the App form. This converts immediate lambda application into
-- let-binding.
simplifyApp :: Lambda env (a -> b) -> Lambda env a -> Lambda env b
simplifyApp (Lambda _ e) a = simplifyLet a e
simplifyApp (Zero (TFun _ t)) _ = Zero t
simplifyApp f a = App f a

-- | Simplify the Let form.
--
-- We allow substituting Pair expressions where each element of the pair is
-- individually only used once in the body (because of Fst and Snd
-- projections).
simplifyLet :: Lambda env a -> Lambda (a ': env) b -> Lambda env b
simplifyLet (Pair a1 a2) e =
  Let a1 $
    Let (sinkLam (wSucc wId) a2) $
      substLam (wSucc (wSucc wId))
               (Pair (Var (typeof a1) (S Z)) (Var (typeof a2) Z))
               e
simplifyLet a e
  | decideInlinable (usesOf' Z e :: Layout (Sum Natural)) a
  = simplify $ substLam wId a e
  | otherwise
  = smartLet a e

-- | Construct a let-binding while preventing let-let via let rotation.
smartLet :: Lambda env a -> Lambda (a ': env) b -> Lambda env b
smartLet (Let rhs e) body = smartLet rhs (smartLet e (sinkLam (wSink (wSucc wId)) body))
smartLet rhs body = Let rhs body

decideInlinable :: (Num s, Ord s) => Layout (Sum s) -> Lambda env a -> Bool
decideInlinable (LyPair ly1 ly2) (Pair e1 e2) =
  decideInlinable ly1 e1 && decideInlinable ly2 e2
decideInlinable (fold -> count) e = count <= 1 || duplicable e

duplicable :: Lambda env a -> Bool
duplicable Var{} = True
duplicable Unit{} = True
duplicable (Pair a b) = duplicable a && duplicable b
duplicable (Fst e) = duplicable e
duplicable (Snd e) = duplicable e
duplicable (AdjPlus a b) = duplicable a && duplicable b
duplicable (Zero _) = True
duplicable (LId _) = True
duplicable (LPair a b) = duplicable a && duplicable b
duplicable (LFst _ _) = True
duplicable (LSnd _ _) = True
duplicable (LSingleton _ e) = duplicable e
duplicable (LCopowFold e) = duplicable e
duplicable _ = False

-- | Simplify the Fst form
simplifyFst :: Lambda env (a, b) -> Lambda env a
-- Fst of a pair can immediately be resolved
simplifyFst (Pair t _) = t
simplifyFst p          = Fst p

-- | Simplify the Snd form
simplifySnd :: Lambda env (a, b) -> Lambda env b
-- Snd of a pair can immediately be resolved
simplifySnd (Pair _ s) = s
simplifySnd p          = Snd p

data LComps env a b where
  LComps :: Lambda env (LFun a b) -> LComps env b c -> LComps env a c
  LCompsDone :: Type a -> LComps env a a

-- | Simplify the LComp form
simplifyLComp :: Lambda env (LFun a b) -> Lambda env (LFun b c) -> Lambda env (LFun a c)
simplifyLComp f1 f2 =
  uncollect . goRev . goFwd . collect simplify $ LComp f1 f2
  where
    collect :: (forall c d. Lambda env (LFun c d) -> Lambda env (LFun c d))
            -> Lambda env (LFun a b) -> LComps env a b
    collect conv (LComp a b) = app (collect conv a) (collect conv b)
    collect conv f =
      let TLFun _ t = typeof f
      in LComps (conv f) (LCompsDone t)

    app :: LComps env a b -> LComps env b c -> LComps env a c
    app (LComps f fs) l = LComps f (app fs l)
    app (LCompsDone _) l = l

    goFwd :: LComps env a b -> LComps env a b
    goFwd (LCompsDone t)                         = LCompsDone t
    goFwd (LComps (LId _) l)                     = goFwd l
    goFwd (LComps (LPair a _) (LComps LFst{} l)) = goFwd (LComps a l)
    goFwd (LComps (LPair _ b) (LComps LSnd{} l)) = goFwd (LComps b l)
    goFwd (LComps f l)                           = LComps f (goFwd l)

    goRev :: LComps env a b -> LComps env a b
    goRev (LCompsDone t) = LCompsDone t
    goRev (LComps f l) = case (f, goRev l) of
        (_, LComps (Zero (TLFun _ t2)) l') ->
          let TLFun t1 _ = typeof f
          in LComps (Zero (TLFun t1 t2)) l'
        (_, l') -> LComps f l'

    uncollect :: LComps env a b -> Lambda env (LFun a b)
    uncollect (LCompsDone t) = LId t
    uncollect (LComps f (LCompsDone _)) = f
    uncollect (LComps f l) = LComp f (uncollect l)

-- | Simplify the Plus form
simplifyPlus :: Lambda env a -> Lambda env a -> Lambda env a
simplifyPlus a (Zero _) = a
simplifyPlus (Zero _) b = b
simplifyPlus a b    = AdjPlus a b
