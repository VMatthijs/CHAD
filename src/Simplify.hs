{-# LANGUAGE GADTs #-}
-- | Simplify terms in the target language
module Simplify (simplifyTTerm) where

import TargetLanguage (TTerm(..), substTt)
import Types

-- | Simplify a TTerm
--   We do this by defining this function as some sort of fold,
--   to make pattern matching easier.
simplifyTTerm :: TTerm a -> TTerm a
-- Source language extension
simplifyTTerm (Var x t)      = Var x t
simplifyTTerm (Lambda x t e) = Lambda x t  (simplifyTTerm e)
simplifyTTerm (App f a)      = simplifyApp (simplifyTTerm f) (simplifyTTerm a)
simplifyTTerm  Unit          = Unit
simplifyTTerm (Pair a b)     = Pair        (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm (Fst p)        = simplifyFst (simplifyTTerm p)
simplifyTTerm (Snd p)        = simplifySnd (simplifyTTerm p)
simplifyTTerm (Lift x t)     = Lift x t
simplifyTTerm (Op op a)      = Op op (simplifyTTerm a)
simplifyTTerm (Map f a)      = Map   (simplifyTTerm f) (simplifyTTerm a)
-- Target language extension
simplifyTTerm  LId           = LId
simplifyTTerm (LComp f g)    = simplifyLComp (simplifyTTerm f) (simplifyTTerm g)
simplifyTTerm (LApp f a)     = simplifyLApp  (simplifyTTerm f) (simplifyTTerm a)
simplifyTTerm (LEval t)      = LEval (simplifyTTerm t)
simplifyTTerm  LFst          = LFst
simplifyTTerm  LSnd          = LSnd
simplifyTTerm (LPair a b)    = LPair     (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm (Singleton t)  = Singleton (simplifyTTerm t)
simplifyTTerm  Zero          = Zero
simplifyTTerm (Plus a b)     = simplifyPlus (simplifyTTerm a) (simplifyTTerm b)
simplifyTTerm (LSwap t)      = LSwap (simplifyTTerm t)
simplifyTTerm (LCur  t)      = LCur  (simplifyTTerm t)
simplifyTTerm (LOp lop)      = LOp lop
simplifyTTerm (DMap  t)      = DMap  (simplifyTTerm t)
simplifyTTerm (DtMap t)      = DtMap (simplifyTTerm t)
simplifyTTerm (Rec t)        = Rec (simplifyTTerm t)
simplifyTTerm (LRec t)       = LRec (simplifyTTerm t)
simplifyTTerm (LIt t)        = LIt (simplifyTTerm t)



-- | Simplify the App TTerm
simplifyApp :: (LT a, LT b) => TTerm (a -> b) -> TTerm a -> TTerm b
simplifyApp (Lambda x t e) v@(Var _ _)           = substTt x v t e
simplifyApp (Lambda x t e) a | usesOf x t e <= 1 = simplifyTTerm $ substTt x a t e
                             | otherwise         = App (Lambda x t e) a
simplifyApp  Zero          _ = Zero
simplifyApp  f             a = App f a

-- | Simplify the Fst TTerm
simplifyFst :: TTerm (a, b) -> TTerm a
-- Fst of a pair can immediately be resolved
simplifyFst (Pair t _) = t
simplifyFst p          = Fst p

-- | Simplify the Snd TTerm
simplifySnd :: TTerm (a, b) -> TTerm b
-- Snd of a pair can immediately be resolved
simplifySnd (Pair _ s) = s
simplifySnd p          = Snd p


-- | Simplify the LComp TTerm
simplifyLComp :: (LT a, LT b, LT c) => TTerm (LFun a b) -> TTerm (LFun b c) -> TTerm (LFun a c)
-- Remove LId
simplifyLComp f                     LId  = f
simplifyLComp LId                   g    = g
-- Remove redundant LPair
simplifyLComp (LPair a _)           LFst = a
simplifyLComp (LPair _ b)           LSnd = b
simplifyLComp (LComp f (LPair a _)) LFst = LComp f a
simplifyLComp (LComp f (LPair _ b)) LSnd = LComp f b
simplifyLComp _                     Zero = Zero
-- Base case
simplifyLComp f                     g    = LComp f g

-- | Simplify the LApp TTerm
simplifyLApp :: TTerm (LFun a b) -> TTerm a -> TTerm b
simplifyLApp LId a = a
simplifyLApp f   a = LApp f a

-- | Simplify the Plus TTerm
simplifyPlus :: LT a => TTerm a -> TTerm a -> TTerm a
simplifyPlus a    Zero = a
simplifyPlus Zero b    = b
simplifyPlus a    b    = Plus a b

{-
    Other 'helper' functions
-}

-- | Count the uses of a variable in an expression
usesOf :: String -> Type a -> TTerm b -> Integer
usesOf x _ (Var y _)      | x == y    = 1
                          | otherwise = 0
usesOf x t (Lambda y _ e) | x == y    = 0
                          | otherwise = usesOf x t e
usesOf x t (App f a)                  = usesOf x t f + usesOf x t a
usesOf _ _  Unit                      = 0
usesOf x t (Pair a b)                 = usesOf x t a + usesOf x t b
usesOf x t (Fst p)                    = usesOf x t p
usesOf x t (Snd p)                    = usesOf x t p
usesOf _ _ (Lift _ _)                 = 0
usesOf x t (Op _ a)                   = usesOf x t a
usesOf x t (Map f y)                  = usesOf x t f + usesOf x t y
usesOf _ _  LId                       = 0
usesOf x t (LComp f g)                = usesOf x t f + usesOf x t g
usesOf x t (LApp f a)                 = usesOf x t f + usesOf x t a
usesOf x t (LEval e)                  = usesOf x t e
usesOf _ _  LFst                      = 0
usesOf _ _  LSnd                      = 0
usesOf x t (LPair a b)                = usesOf x t a + usesOf x t b
usesOf x t (Singleton s)              = usesOf x t s
usesOf _ _  Zero                      = 0
usesOf x t (Plus a b)                 = usesOf x t a + usesOf x t b
usesOf x t (LSwap s)                  = usesOf x t s
usesOf x t (LCur s)                   = usesOf x t s
usesOf _ _ (LOp _)                    = 0
usesOf x t (DMap s)                   = usesOf x t s
usesOf x t (DtMap s)                  = usesOf x t s
usesOf x t (Rec s)                    = usesOf x t s
usesOf x t (LRec s)                   = usesOf x t s
usesOf x t (LIt s)                    = usesOf x t s
