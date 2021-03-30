{-# LANGUAGE GADTs #-}

-- | Simplify terms in the target language to aid legibility.
--   This should only do simplifications that any basic compiler
--   would also perform.
module Simplify
  ( simplifyTTerm
  ) where

import           Data.Foldable      (toList)
import           Data.Monoid        (Sum (..))

import           TargetLanguage     (Layout (..), TTerm (..), substTt,
                                     truncateLayoutWithExpr, usesOf')
import           TargetLanguage.Env
import           Types

-- | Simplify a TTerm
--   We do this by defining this function as some sort of fold,
--   to make pattern matching easier.
simplifyTTerm :: TTerm env a -> TTerm env a
-- Source language extension
simplifyTTerm (Var i) = Var i
simplifyTTerm (Lambda e) = Lambda (simplifyTTerm e)
simplifyTTerm (App f a) = simplifyApp (simplifyTTerm f) (simplifyTTerm a)
simplifyTTerm Unit = Unit
simplifyTTerm (Pair a b) = Pair (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm (Fst p) = simplifyFst (simplifyTTerm p)
simplifyTTerm (Snd p) = simplifySnd (simplifyTTerm p)
simplifyTTerm (Inl p) = Inl (simplifyTTerm p)
simplifyTTerm (Inr p) = Inr (simplifyTTerm p)
simplifyTTerm (Case p f g) = simplifyCase p f g
simplifyTTerm (Op op a) = Op op (simplifyTTerm a)
simplifyTTerm (Map f a) = Map (simplifyTTerm f) (simplifyTTerm a)
simplifyTTerm (Foldr f v xs) =
  Foldr (simplifyTTerm f) (simplifyTTerm v) (simplifyTTerm xs)
simplifyTTerm (Rec t) = Rec (simplifyTTerm t)
simplifyTTerm (It t) = It (simplifyTTerm t)
simplifyTTerm (Sign t) = Sign (simplifyTTerm t)
-- Target language extension
simplifyTTerm LId = LId
simplifyTTerm (LComp f g) = simplifyLComp (simplifyTTerm f) (simplifyTTerm g)
simplifyTTerm (LApp f a) = simplifyLApp (simplifyTTerm f) (simplifyTTerm a)
simplifyTTerm (LEval t) = LEval (simplifyTTerm t)
simplifyTTerm LUnit = LUnit
simplifyTTerm LFst = LFst
simplifyTTerm LSnd = LSnd
simplifyTTerm (LPair a b) = LPair (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm LInl = LInl
simplifyTTerm LInr = LInr
simplifyTTerm (LCoPair a b) = LCoPair (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm (Singleton t) = Singleton (simplifyTTerm t)
simplifyTTerm Zero = Zero
simplifyTTerm (Plus a b) = simplifyPlus (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm (LSwap t) = LSwap (simplifyTTerm t)
simplifyTTerm (LCopowFold t) = LCopowFold (simplifyTTerm t)
simplifyTTerm (LOp lop) = LOp lop
simplifyTTerm (DMap f xs) = DMap (simplifyTTerm f) (simplifyTTerm xs)
simplifyTTerm (DtMap f xs) = DtMap (simplifyTTerm f) (simplifyTTerm xs)
simplifyTTerm (DFoldr f v xs) =
  DFoldr (simplifyTTerm f) (simplifyTTerm v) (simplifyTTerm xs)
simplifyTTerm (DtFoldr f v xs) =
  DtFoldr (simplifyTTerm f) (simplifyTTerm v) (simplifyTTerm xs)
simplifyTTerm (DIt d1t d2t) = DIt (simplifyTTerm d1t) (simplifyTTerm d2t)
simplifyTTerm (DtIt d1t d2t) = DtIt (simplifyTTerm d1t) (simplifyTTerm d2t)
simplifyTTerm (LRec t) = LRec (simplifyTTerm t)
simplifyTTerm (LIt t) = LIt (simplifyTTerm t)
simplifyTTerm (Error s) = Error s

-- | Simplify the App TTerm.
-- We allow substituting Pair expressions where each element of the pair is
-- individually only used once in the function body.
simplifyApp :: TTerm env (a -> b) -> TTerm env a -> TTerm env b
simplifyApp (Lambda e) (Var j) = substTt (Var j) e
simplifyApp (Lambda e) a
        -- Count the usages of the components of 'a' in the body, 'e'
  | let layout = usesOf' Z e
        -- Then truncate the resulting layout with the actual Pair structure of 'a'
        count = getSum <$> truncateLayoutWithExpr layout a :: Layout Integer
    -- Require that every component is used at most once
  , all (<= 1) (toList count) = simplifyTTerm $ substTt a e
  | otherwise = App (Lambda e) a
simplifyApp Zero _ = Zero
simplifyApp f a = App f a

-- | Simplify the Fst TTerm
simplifyFst :: TTerm env (a, b) -> TTerm env a
-- Fst of a pair can immediately be resolved
simplifyFst (Pair t _) = t
simplifyFst p          = Fst p

-- | Simplify the Snd TTerm
simplifySnd :: TTerm env (a, b) -> TTerm env b
-- Snd of a pair can immediately be resolved
simplifySnd (Pair _ s) = s
simplifySnd p          = Snd p

simplifyCase ::
     TTerm env (Either a b)
  -> TTerm env (a -> c)
  -> TTerm env (b -> c)
  -> TTerm env c
simplifyCase (Inl p) f _ = simplifyTTerm $ App f p
simplifyCase (Inr p) _ g = simplifyTTerm $ App g p
simplifyCase x f g       = Case x (simplifyTTerm f) (simplifyTTerm g)

-- | Simplify the LComp TTerm
simplifyLComp ::
     (LT a, LT b, LT c)
  => TTerm env (LFun a b)
  -> TTerm env (LFun b c)
  -> TTerm env (LFun a c)
-- Remove LId
simplifyLComp f LId                        = f
simplifyLComp LId g                        = g
-- Simplify LUnit
simplifyLComp _ LUnit                      = LUnit
-- Remove redundant LPair
simplifyLComp (LPair a _) LFst             = a
simplifyLComp (LPair _ b) LSnd             = b
simplifyLComp (LComp f (LPair a _)) LFst   = LComp f a
simplifyLComp (LComp f (LPair _ b)) LSnd   = LComp f b
simplifyLComp LInl (LCoPair a _)           = a
simplifyLComp LInr (LCoPair _ b)           = b
simplifyLComp LInl (LComp (LCoPair a _) f) = LComp a f
simplifyLComp LInr (LComp (LCoPair _ b) f) = LComp b f
simplifyLComp _ Zero                       = Zero
-- Base case
simplifyLComp f g                          = LComp f g

-- | Simplify the LApp TTerm
simplifyLApp ::
     (LT a, LT b) => TTerm env (LFun a b) -> TTerm env a -> TTerm env b
simplifyLApp LId a = a
simplifyLApp f a   = LApp f a

-- | Simplify the Plus TTerm
simplifyPlus :: LT a => TTerm env a -> TTerm env a -> TTerm env a
simplifyPlus a Zero = a
simplifyPlus Zero b = b
simplifyPlus a b    = Plus a b
