{-# LANGUAGE GADTs #-}
module TargetLanguage where

import Lib ((&&&))
import Types
import LanguageTypes (LT(..))
import Operation (Operation, LinearOperation, evalOp, evalLOp, showOp, showLOp)
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
    LOp       :: LinearOperation a b c -> TTerm (a -> LFun b c)

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
subst x v u (Op op y)                  = Op op (subst x v u y)
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
subst _ _ _ (LOp lop)                  = LOp lop

-- | Substitute variable for a TTerm
substTt :: String -> TTerm u -> Type u -> TTerm t -> TTerm t
substTt x v u (Var y t)      | x == y    = case eqTy u t of
                                            Just Refl -> v
                                            Nothing   -> error "ill-typed substTtitution"
                             | otherwise = Var y t
substTt x v u (Lambda y t e) | x == y    = Lambda y t e
                             | otherwise = Lambda y t (substTt x v u e)
substTt x v u (App f a)                  = App (substTt x v u f) (substTt x v u a)
substTt _ _ _  Unit                      = Unit
substTt x v u (Pair a b)                 = Pair (substTt x v u a) (substTt x v u b)
substTt x v u (Fst p)                    = Fst (substTt x v u p)
substTt x v u (Snd p)                    = Snd (substTt x v u p)
substTt _ _ _ (Lift x t)                 = Lift x t
substTt x v u (Op op y)                  = Op op (substTt x v u y)
-- Target language extension
substTt _ _ _  LId                       = LId
substTt x v u (LComp f g)                = LComp (substTt x v u f) (substTt x v u g)
substTt x v u (LApp f a)                 = LApp (substTt x v u f) (substTt x v u a)
substTt _ _ _  LFst                      = LFst
substTt _ _ _  LSnd                      = LSnd
substTt x v u (LPair a b)                = LPair (substTt x v u a) (substTt x v u b)
substTt x v u (Singleton t)              = Singleton (substTt x v u t)
substTt _ _ _  Zero                      = Zero
substTt x v u (Plus a b)                 = Plus (substTt x v u a) (substTt x v u b)
substTt x v u (LSwap t)                  = LSwap (substTt x v u t)
substTt x v u (LCur t)                   = LCur (substTt x v u t)
substTt _ _ _ (LOp lop)                  = LOp lop


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
evalTt (LOp lop)         = evalLOp lop
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


printTt :: TTerm t -> String
-- Source language extension
printTt (Var x _)         = x
printTt (Lambda x t e)    = "\\" ++ x ++ " -> " ++ printTt e
printTt (App f a)         = printTt f ++ "(" ++ printTt a ++ ")"
printTt  Unit             = "()"
printTt (Pair a b)        = "(" ++ printTt a ++ ", " ++ printTt b ++ ")"
printTt (Fst p)           = "Fst(" ++ printTt p ++ ")"
printTt (Snd p)           = "Snd(" ++ printTt p ++ ")"
printTt (Lift x _)        = undefined
printTt (Op op a)         = "evalOp " ++ showOp op ++ " " ++ printTt a
printTt (LOp lop)         = "evalLOp " ++ showLOp lop
-- Target language extension
printTt  LId              = "lid"
printTt (LComp f g)       = printTt g ++ ";;" ++ printTt f
printTt (LApp f a)        = printTt f ++ "(" ++ printTt a ++ ")"
printTt  LFst             = "lfst"
printTt  LSnd             = "lsnd"
printTt (LPair a b)       = "lpair(" ++ printTt a ++ ", " ++ printTt b ++ ")"
printTt (Singleton t)     = "[(" ++ printTt t ++ ", -)]"
printTt  Zero             = "0"
printTt (Plus a b)        = "(" ++ printTt a ++ ") + (" ++ printTt b ++ ")"
printTt (LSwap t)         = "lswap(" ++ printTt t ++ ")"
printTt (LCur  t)         = "lcur⁻¹(" ++ printTt t ++ ")"
