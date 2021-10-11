{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Simplify terms in the concrete language to aid legibility.
--
-- This should only do simplifications that any basic compiler
-- would also perform.
--
-- The simplifier in this module is /parametrised/: all the individual
-- simplifications can be turned on or off by setting the corresponding flag in
-- the 'Settings' object passed to 'simplifyCTerm'.
module Concrete.Simplify (
  simplifyCTerm,
  Settings(..), defaultSettings, allSettings,
) where

import Concrete
import Count
import Env
import Types

data Settings = Settings
  { simpLamAppLet :: Bool        -- ^ @(\x -> e) a@  ~>  @let x = a in e@
  , simpZeroApp :: Bool          -- ^ @zero a@  ~>  @zero@
  , simpLetRotate :: Bool        -- ^ @let x = (let y = a in b) in e@  ~>  @let y = a in let x = b in e@
  , simpLetPairSplit :: Bool     -- ^ @let x = (a, b) in @e  ~>  @let x1 = a in let x2 = b in e[(x1,x2)/x]@
  , simpLetInline :: Bool        -- ^ @let x = a in e@  ~>  @e[a/x]@  (if @a@ is cheap or used at most once in e)
  , simpPairProj :: Bool         -- ^ @fst (a, b)@  ~>  @a@  (and similarly for @snd@)
  , simpLetProj :: Bool          -- ^ @fst (let x = a in e)@  ~>  @let x = a in fst e@  (and similarly for @snd@)
  , simpPlusZero :: Bool         -- ^ @plus zero a@  ~>  @a@  (also symmetrically)
  , simpPlusPair :: Bool         -- ^ @plus (a, b) (c, d)@  ~>  @(plus a c, plus b d)@
  , simpPlusLet :: Bool          -- ^ @plus (let x = e in a) b@  ~>  @let x = e in plus a b@  (also symmetrically)
  , simpLetLamPairSplit :: Bool  -- ^ @let f = \x -> (a, b) in e@  ~>  @let f1 = \x -> a ; f2 = \x -> b in e[(\x->(f1 x,f2 x))/f]@
  , simpMapPairSplit :: Bool     -- ^ @map (\x -> (b, c)) a@  ~>  @let a' = a in (map (\x -> b) a', map (\x -> c) a')@
  , simpMapZero :: Bool          -- ^ @map (\x -> zero) a@  ~>  @zero@
  , simpSumZip :: Bool           -- ^ @sum (zip a b)@  ~>  @(sum a, sum b)@
  , simpSumZero :: Bool          -- ^ @sum zero@  ~>  @zero@
  }
  deriving (Show, Eq)

instance Semigroup Settings where
  Settings a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 <>
      Settings b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =
    Settings (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) (a5 || b5)
             (a6 || b6) (a7 || b7) (a8 || b8) (a9 || b9) (a10 || b10)
             (a11 || b11) (a12 || b12) (a13 || b13) (a14 || b14)
             (a15 || b15)

instance Monoid Settings where
  mempty = Settings False False False False False False False False
                    False False False False False False False

defaultSettings :: Settings
defaultSettings = Settings
  { simpLamAppLet       = True
  , simpZeroApp         = True
  , simpLetRotate       = True
  , simpLetPairSplit    = True
  , simpLetInline       = True
  , simpPairProj        = True
  , simpLetProj         = True
  , simpPlusZero        = True
  , simpPlusPair        = True
  , simpPlusLet         = True
  , simpLetLamPairSplit = False
  , simpMapPairSplit    = False
  , simpMapZero         = False
  , simpSumZip          = False
  , simpSumZero         = False
  }

allSettings :: Settings
allSettings = Settings
  { simpLamAppLet       = True
  , simpZeroApp         = True
  , simpLetRotate       = True
  , simpLetPairSplit    = True
  , simpLetInline       = True
  , simpPairProj        = True
  , simpLetProj         = True
  , simpPlusZero        = True
  , simpPlusPair        = True
  , simpPlusLet         = True
  , simpLetLamPairSplit = True
  , simpMapPairSplit    = True
  , simpMapZero         = True
  , simpSumZip          = True
  , simpSumZero         = True
  }

simplifyCTerm :: Settings -> CTerm env a -> CTerm env a
simplifyCTerm settings = let ?settings = settings in simplifyCTerm'

-- | Simplify a 'CTerm' using some basic rewriting optimisations.
--
-- Note: inlining of variable definitions is only performed if the variable in
-- question is only used once. Let-splitting is performed.
simplifyCTerm' :: (?settings :: Settings) => CTerm env a -> CTerm env a
simplifyCTerm' (CVar i) = CVar i
simplifyCTerm' (CLambda e) = CLambda (simplifyCTerm' e)
simplifyCTerm' (CLet rhs e) = simplifyLet (simplifyCTerm' rhs) (simplifyCTerm' e)
simplifyCTerm' (CApp f a) = simplifyApp (simplifyCTerm' f) (simplifyCTerm' a)
simplifyCTerm' CUnit = CUnit
simplifyCTerm' (CPair a b) = CPair (simplifyCTerm' a) (simplifyCTerm' b)
simplifyCTerm' (CFst p) = simplifyFst (simplifyCTerm' p)
simplifyCTerm' (CSnd p) = simplifySnd (simplifyCTerm' p)
simplifyCTerm' (COp op a) = COp op (simplifyCTerm' a)
simplifyCTerm' (CMap a b) = CMap (simplifyCTerm' a) (simplifyCTerm' b)
simplifyCTerm' (CZipWith a b c) = CZipWith (simplifyCTerm' a) (simplifyCTerm' b) (simplifyCTerm' c)
simplifyCTerm' (CReplicate x) = CReplicate (simplifyCTerm' x)
simplifyCTerm' (CSum a) = CSum (simplifyCTerm' a)
simplifyCTerm' (CToList a) = CToList (simplifyCTerm' a)
simplifyCTerm' CLNil = CLNil
simplifyCTerm' (CLCons a b) = CLCons (simplifyCTerm' a) (simplifyCTerm' b)
simplifyCTerm' (CLMap a b) = simplifyCLMap (simplifyCTerm' a) (simplifyCTerm' b)
simplifyCTerm' (CLFoldr a b c) = CLFoldr (simplifyCTerm' a) (simplifyCTerm' b) (simplifyCTerm' c)
simplifyCTerm' (CLSum a) = simplifyCLSum (simplifyCTerm' a)
simplifyCTerm' (CLZip b c) = CLZip (simplifyCTerm' b) (simplifyCTerm' c)
simplifyCTerm' CZero = CZero
simplifyCTerm' (CPlus a b) = simplifyPlus (simplifyCTerm' a) (simplifyCTerm' b)

-- | Simplify the App form. This converts immediate lambda application into
-- let-binding.
simplifyApp :: (?settings :: Settings) => CTerm env (a -> b) -> CTerm env a -> CTerm env b
simplifyApp (CLambda e) a | simpLamAppLet ?settings = simplifyLet a e
simplifyApp CZero _ | simpZeroApp ?settings = CZero
simplifyApp f a = CApp f a

data SplitLambda env t where
  SLam :: CTerm env a
       -> CTerm env b
       -> (forall env'. CTerm (b ': a ': env') t)
       -> SplitLambda env t

splitLambda :: (?settings :: Settings) => CTerm env t -> Maybe (SplitLambda env t)
splitLambda (CLambda e) =
  fmap (\(SLam f1 f2 re) -> SLam (CLambda f1) (CLambda f2)
            (CLambda $
              substCt wId (CApp (CVar (S (S Z))) (CVar Z)) $
                substCt wId (CApp (CVar (S (S Z))) (CVar (S Z))) $
                  sinkCt (wSink (wSink (wSink (wSucc (wSucc wId)))))
                    re))
       (splitLambda e)
splitLambda (CPair a b) = Just (SLam a b (CPair (CVar (S Z)) (CVar Z)))
splitLambda _ = Nothing

-- | Simplify the Let form.
--
-- We perform let-of-pair splitting, also when that pair is hidden behind a lambda.
simplifyLet :: (?settings :: Settings) => CTerm env a -> CTerm (a ': env) b -> CTerm env b
simplifyLet (CLet rhs e) body | simpLetRotate ?settings =
  simplifyLet rhs (simplifyLet e (sinkCt (wSink (wSucc wId)) body))
simplifyLet (CPair a1 a2) e | simpLetPairSplit ?settings =
  simplifyLet a1 $
    simplifyLet (sinkCt (wSucc wId) a2) $
      simplifyCTerm' $ substCt (wSucc (wSucc wId)) (CPair (CVar (S Z)) (CVar Z)) e
simplifyLet a e
  | simpLetLamPairSplit ?settings
  , Just (SLam a1 a2 re) <- splitLambda a
  , let re' = substCt wId (CVar (S Z)) . substCt wId (CVar (S Z)) $ re
  = simplifyCTerm' $
      CLet a1 $
        CLet (sinkCt (wSucc wId) a2) $
          substCt wId re' (sinkCt (wSink (wSucc (wSucc wId))) e)
  | simpLetInline ?settings
  , -- Occurrence counting for variable inlining is tricky. See the documentation of 'OccCount'.
    let OccCount synUses runUses = usesOfCt Z e
  , duplicableSyntactic a || synUses <= 1
  , duplicableRuntime a || runUses <= 1
  = simplifyCTerm' $ substCt wId a e
  | otherwise
  = CLet a e

duplicableRuntime :: CTerm env a -> Bool
duplicableRuntime = \case
  CLambda{} -> True
  t -> duplicableSyntactic t

duplicableSyntactic :: CTerm env a -> Bool
duplicableSyntactic = \case
  CVar{} -> True
  CUnit{} -> True
  CPair a b -> duplicableSyntactic a && duplicableSyntactic b
  CFst e -> duplicableSyntactic e
  CSnd e -> duplicableSyntactic e
  CPlus a b -> duplicableSyntactic a && duplicableSyntactic b
  CZero -> True
  _ -> False

-- | Simplify the Fst form
simplifyFst :: (?settings :: Settings) => CTerm env (a, b) -> CTerm env a
simplifyFst (CPair t _)  | simpPairProj ?settings = t
simplifyFst (CLet rhs e) | simpLetProj ?settings = simplifyLet rhs (simplifyFst e)
simplifyFst p            = CFst p

-- | Simplify the Snd form
simplifySnd :: (?settings :: Settings) => CTerm env (a, b) -> CTerm env b
simplifySnd (CPair _ s)  | simpPairProj ?settings = s
simplifySnd (CLet rhs e) | simpLetProj ?settings = simplifyLet rhs (simplifySnd e)
simplifySnd p            = CSnd p

simplifyCLMap :: (?settings :: Settings) => CTerm env (a -> b) -> CTerm env [a] -> CTerm env [b]
simplifyCLMap (CLambda (CPair a b)) l | simpMapPairSplit ?settings =
  simplifyCTerm' $
    CLet l $
      CLZip (CLMap (CLambda (sinkCt (wSink (wSucc wId)) a)) (CVar Z))
            (CLMap (CLambda (sinkCt (wSink (wSucc wId)) b)) (CVar Z))
simplifyCLMap (CLambda CZero) _ | simpMapZero ?settings = CZero
simplifyCLMap f l = CLMap f l

simplifyCLSum :: (?settings :: Settings, LT a) => CTerm env [a] -> CTerm env a
simplifyCLSum (CLZip a b) | simpSumZip ?settings =
  simplifyCTerm' $ CPair (simplifyCLSum a) (simplifyCLSum b)
simplifyCLSum CZero | simpSumZero ?settings = CZero
simplifyCLSum l = CLSum l

-- | Simplify the Plus form
simplifyPlus :: (LT a, ?settings :: Settings) => CTerm env a -> CTerm env a -> CTerm env a
simplifyPlus a CZero | simpPlusZero ?settings = a
simplifyPlus CZero b | simpPlusZero ?settings = b
simplifyPlus (CPair a b) (CPair a' b') | simpPlusPair ?settings =
  simplifyCTerm' (CPair (CPlus a a') (CPlus b b'))
simplifyPlus (CLet rhs a) b | simpPlusLet ?settings = simplifyLet rhs (simplifyPlus a (sinkCt (wSucc wId) b))
simplifyPlus a (CLet rhs b) | simpPlusLet ?settings = simplifyLet rhs (simplifyPlus (sinkCt (wSucc wId) a) b)
simplifyPlus a b     = CPlus a b
