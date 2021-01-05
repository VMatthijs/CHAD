{-# LANGUAGE GADTs #-}
module TargetLanguage where

import Lib ((&&&))
import Types (Type, LFun, Tens, RealN, eqTy)
import LanguageTypes (LT(..))
import Operation (Operation, evalOp)
import Data.Type.Equality ((:~:)(Refl))


-- | Terms of the target language
data TTerm t where
    -- Terms from source language
    Var    :: String -> Type a -> TTerm a
    Lambda :: String -> Type a -> TTerm b -> TTerm (a -> b)
    App    :: TTerm (a -> b) -> TTerm a -> TTerm b
    Unit   :: TTerm ()
    Pair   :: TTerm a -> TTerm b -> TTerm (a, b)
    Fst    :: TTerm (a, b) -> TTerm a
    Snd    :: TTerm (a, b) -> TTerm b
    Lift   :: a -> Type a -> TTerm a
    -- | Operators
    -- Op  :: Operation n m -> TTerm(RealN n) -> TTerm (RealN m) -- fix arity here
    Op     :: Operation a -> TTerm a -> TTerm RealN

    -- Target language extension

    -- | Linear operation
    -- LOp :: LinearOperation k l m -> TTerm a (RealN k) -> TTerm a (LFun (RealN l) (RealN m)) -- fix arity here

    -- Linear functions
    LId       :: TTerm (LFun b b)
    LComp     :: TTerm (LFun b c) -> TTerm (LFun c d) -> TTerm (LFun b d)
    LApp      :: TTerm (LFun b c) -> TTerm b -> TTerm c
    LEval     :: TTerm b -> TTerm (LFun (b -> c) c)
    -- Tuples
    LFst      :: TTerm (LFun (b, c) b)
    LSnd      :: TTerm (LFun (b, c) c)
    LPair     :: TTerm (LFun b c) -> TTerm (LFun b d) -> TTerm (LFun b (c, d))
    -- | Singleton
    Singleton :: TTerm b -> TTerm (LFun c (Tens b c))
    -- Zero
    Zero      :: LT b => TTerm b
    -- Plus
    Plus      :: LT b => TTerm b -> TTerm b -> TTerm b
    -- Swap
    LSwap     :: TTerm (b -> LFun c d) -> TTerm (LFun c (b -> d))
    -- | Tensor-elimination
    LCur      :: (LT b, LT c, LT d) => TTerm (b -> LFun c d) -> TTerm (LFun (Tens b c) d)


-- | Substitute variable for term
subst :: String -> u -> Type u -> TTerm t -> TTerm t
subst x v u (Var y t)      | x == y    = case eqTy u t of
                                            Just Refl -> Lift v u
                                            Nothing   -> error "ill-typed substitution"
                           | otherwise = Var y t
subst x v u (Lambda y t e) | x == y    = Lambda y t e
                           | otherwise = Lambda y t (subst x v u e)
subst x v u (App f a)                  = App (subst x v u f) (subst x v u a)
subst _ _ _  Unit                      = Unit
subst x v u (Pair a b)                 = Pair (subst x v u a) (subst x v u b)
subst x v u (Fst p)                    = Fst (subst x v u p)
subst x v u (Snd p)                    = Snd (subst x v u p)
subst _ _ _ (Lift x t)                 = Lift x t
-- Target language extension
subst _ _ _  LId                       = LId
subst x v u (LComp f g)                = LComp (subst x v u f) (subst x v u g)
subst x v u (LApp f a)                 = LApp (subst x v u f) (subst x v u a)
subst _ _ _  LFst                      = LFst
subst _ _ _  LSnd                      = LSnd
subst x v u (LPair a b)                = LPair (subst x v u a) (subst x v u b)
subst x v u (Singleton t)              = Singleton (subst x v u t)
subst _ _ _  Zero                      = Zero
subst x v u (Plus a b)                 = Plus (subst x v u a) (subst x v u b)
subst x v u (LSwap t)                  = LSwap (subst x v u t)
subst x v u (LCur t)                   = LCur (subst x v u t)


-- | Evaluate the target language
evalTt :: TTerm t -> t
-- Source language extension
evalTt (Var _ _)         = error "Free variable has no value"
evalTt (Lambda x t e)    = \v -> evalTt $ subst x v t e
evalTt (App f a)         = evalTt f (evalTt a)
evalTt  Unit             = ()
evalTt (Pair a b)        = (evalTt a, evalTt b)
evalTt (Fst p)           = fst $ evalTt p
evalTt (Snd p)           = snd $ evalTt p
evalTt (Lift x _)        = x
evalTt (Op op a)         = evalOp op (evalTt a)
-- Target language extension
evalTt  LId              = id
evalTt (LComp f g)       = evalTt g . evalTt f
evalTt (LApp f a)        = evalTt f (evalTt a)
evalTt  LFst             = fst
evalTt  LSnd             = snd
evalTt (LPair a b)       = evalTt a &&& evalTt b
evalTt (Singleton t)     = \x -> [(evalTt t, x)]
evalTt  Zero             = zero
evalTt (Plus a b)        = plus (evalTt a) (evalTt b)
evalTt (LSwap t)         = flip $ evalTt t
evalTt (LCur  t)         = foldr f zero
    where f x acc = plus (uncurry (evalTt t) x) acc
