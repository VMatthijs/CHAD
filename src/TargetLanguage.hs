{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

-- | Definition of the target language
module TargetLanguage where

import           Data.Vector.Unboxed.Sized as V (Unbox, foldr, map)

import           Data.Type.Equality        ((:~:) (Refl))
import           GHC.TypeNats              (KnownNat)
import           Operation                 (LinearOperation, Operation, evalLOp,
                                            evalOp, showLOp, showOp)
import           Types                     as T (LFun, LT (..), Scal, Tens,
                                                 Type, Vect, dFoldr, dIt,
                                                 dtFoldr, dtIt, eqTy, lApp,
                                                 lComp, lCur, lEval, lFst, lId,
                                                 lMap, lPair, lSnd, lSwap, lZip,
                                                 lZipWith', singleton)

-- | Terms of the target language
data TTerm t
    -- Terms from source language
      where
  Var :: String -> Type a -> TTerm a
  Lambda :: String -> Type a -> TTerm b -> TTerm (a -> b)
  App :: (LT a, LT b) => TTerm (a -> b) -> TTerm a -> TTerm b
  Unit :: TTerm ()
  Pair :: TTerm a -> TTerm b -> TTerm (a, b)
  Fst :: TTerm (a, b) -> TTerm a
  Snd :: TTerm (a, b) -> TTerm b
  Inl :: (LT a, LT b) => TTerm a -> TTerm (Either a b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  Inr :: (LT a, LT b) => TTerm b -> TTerm (Either a b) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  Case
    :: (LT a, LT b, LT c)
    => TTerm (Either a b)
    -> TTerm (a -> c)
    -> TTerm (b -> c)
    -> TTerm c -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  It :: TTerm ((a, b) -> Either c b) -> TTerm ((a, b) -> c) -- EXPERIMENTAL SUPPORT FOR ITERATION
  Rec :: TTerm ((a, b) -> b) -> TTerm (a -> b) -- EXPERIMENTAL SUPPORT FOR RECURSION (Should we work with a representation that is variable binding instead?)
  Lift :: a -> Type a -> TTerm a
    -- | Operators
  Op :: Operation a b -> TTerm a -> TTerm b
  Map :: TTerm (Scal -> Scal) -> TTerm (Vect n) -> TTerm (Vect n)
  Foldr :: (LT a, KnownNat n) => TTerm ((((Scal, a) -> a, a), Vect n) -> a)
    -- Target language extension
    -- | Linear operation
  LOp :: LinearOperation a b c -> TTerm (a -> LFun b c)
    -- Linear functions
  LId :: TTerm (LFun a a)
  LComp
    :: (LT a, LT b, LT c)
    => TTerm (LFun a b)
    -> TTerm (LFun b c)
    -> TTerm (LFun a c)
  LApp :: (LT a, LT b) => TTerm (LFun a b) -> TTerm a -> TTerm b
  LEval :: TTerm a -> TTerm (LFun (a -> b) b)
    -- Tuples
  LFst :: TTerm (LFun (a, b) a)
  LSnd :: TTerm (LFun (a, b) b)
  LPair
    :: (LT a, LT b, LT c)
    => TTerm (LFun a b)
    -> TTerm (LFun a c)
    -> TTerm (LFun a (b, c))
    -- | Singleton
  Singleton :: TTerm b -> TTerm (LFun c (Tens b c))
    -- Zero
  Zero :: LT a => TTerm a
    -- Plus
  Plus :: LT a => TTerm a -> TTerm a -> TTerm a
    -- Swap
  LSwap
    :: (LT b, LT c, LT d) => TTerm (b -> LFun c d) -> TTerm (LFun c (b -> d))
    -- | Tensor-elimination
  LCur
    :: (LT b, LT c, LT d) => TTerm (b -> LFun c d) -> TTerm (LFun (Tens b c) d)
    -- Map derivatives
  DMap
    :: KnownNat n
    => TTerm (Scal -> (Scal, LFun Scal Scal), Vect n)
    -> TTerm (LFun (Scal -> Scal, Vect n) (Vect n))
  DtMap
    :: KnownNat n
    => TTerm (Scal -> (Scal, LFun Scal Scal), Vect n)
    -> TTerm (LFun (Vect n) (Tens Scal Scal, Vect n))
  DFoldr
    :: (KnownNat n, V.Unbox a, V.Unbox b, LT b)
    => TTerm ((((Scal, a) -> (a, LFun (Scal, b) b), a), Vect n) -> LFun ( ( ( Scal
                                                                            , a) -> b
                                                                          , b)
                                                                        , Vect n) b)
  DtFoldr
    :: (KnownNat n, V.Unbox a, V.Unbox b, LT b)
    => TTerm ((((Scal, a) -> (a, LFun b (Scal, b)), a), Vect n) -> LFun b ( ( Tens ( Scal
                                                                                   , a) b
                                                                            , b)
                                                                          , Vect n))
  DIt
    :: (LT d2a, LT d2b, LT d2c)
    => TTerm ((d1a, d1b) -> Either d1c d1b)
    -> TTerm ((d1a, d1b) -> LFun (d2a, d2b) (d2c, d2b))
    -> TTerm ((d1a, d1b) -> LFun (d2a, d2b) d2c) -- EXPERIMENTAL SUPPORT FOR ITERATION
  DtIt
    :: (LT d2a, LT d2b, LT d2c)
    => TTerm ((d1a, d1b) -> Either d1c d1b)
    -> TTerm ((d1a, d1b) -> LFun (d2c, d2b) (d2a, d2b))
    -> TTerm ((d1a, d1b) -> LFun d2c (d2a, d2b)) -- EXPERIMENTAL SUPPORT FOR ITERATION

-- | Substitute variable for term
subst :: String -> u -> Type u -> TTerm t -> TTerm t
subst x v u (Var y t)
  | x == y =
    case eqTy u t of
      Just Refl -> Lift v u
      Nothing   -> error "ill-typed substitution"
  | otherwise = Var y t
subst x v u (Lambda y t e)
  | x == y = Lambda y t e
  | otherwise = Lambda y t (subst x v u e)
subst x v u (App f a) = App (subst x v u f) (subst x v u a)
subst _ _ _ Unit = Unit
subst x v u (Pair a b) = Pair (subst x v u a) (subst x v u b)
subst x v u (Fst p) = Fst (subst x v u p)
subst x v u (Snd p) = Snd (subst x v u p)
subst _ _ _ (Lift x t) = Lift x t
subst x v u (Op op y) = Op op (subst x v u y)
subst x v u (Map f y) = Map (subst x v u f) (subst x v u y)
subst _ _ _ Foldr = Foldr
subst x v u (Inl t) = Inl (subst x v u t) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
subst x v u (Inr t) = Inr (subst x v u t) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
subst x v u (Case t l r) = Case (subst x v u t) (subst x v u l) (subst x v u r) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
-- Target language extension
subst x v u (Rec t) = Rec (subst x v u t) -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
subst x v u (It t) = It (subst x v u t) -- EXPERIMENTAL SUPPORT FOR ITERATION
subst _ _ _ LId = LId
subst x v u (LComp f g) = LComp (subst x v u f) (subst x v u g)
subst x v u (LApp f a) = LApp (subst x v u f) (subst x v u a)
subst x v u (LEval t) = LEval (subst x v u t)
subst _ _ _ LFst = LFst
subst _ _ _ LSnd = LSnd
subst x v u (LPair a b) = LPair (subst x v u a) (subst x v u b)
subst x v u (Singleton t) = Singleton (subst x v u t)
subst _ _ _ Zero = Zero
subst x v u (Plus a b) = Plus (subst x v u a) (subst x v u b)
subst x v u (LSwap t) = LSwap (subst x v u t)
subst x v u (LCur t) = LCur (subst x v u t)
subst _ _ _ (LOp lop) = LOp lop
subst x v u (DMap t) = DMap (subst x v u t)
subst x v u (DtMap t) = DtMap (subst x v u t)
subst _ _ _ DFoldr = DFoldr
subst _ _ _ DtFoldr = DtFoldr
subst x v u (DIt d1t d2t) = DIt (subst x v u d1t) (subst x v u d2t) -- EXPERIMENTAL SUPPORT FOR ITERATION
subst x v u (DtIt d1t d2t) = DtIt (subst x v u d1t) (subst x v u d2t) -- EXPERIMENTAL SUPPORT FOR ITERATION

-- | Substitute variable for a TTerm
substTt :: String -> TTerm u -> Type u -> TTerm t -> TTerm t
substTt x v u (Var y t)
  | x == y =
    case eqTy u t of
      Just Refl -> v
      Nothing   -> error "ill-typed substitution"
  | otherwise = Var y t
substTt x v u (Lambda y t e)
  | x == y = Lambda y t e
  | otherwise = Lambda y t (substTt x v u e)
substTt x v u (App f a) = App (substTt x v u f) (substTt x v u a)
substTt _ _ _ Unit = Unit
substTt x v u (Pair a b) = Pair (substTt x v u a) (substTt x v u b)
substTt x v u (Fst p) = Fst (substTt x v u p)
substTt x v u (Snd p) = Snd (substTt x v u p)
substTt x v u (Inl t) = Inl (substTt x v u t) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
substTt x v u (Inr t) = Inr (substTt x v u t) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
substTt x v u (Case t l r) =
  Case (substTt x v u t) (substTt x v u l) (substTt x v u r) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
substTt _ _ _ (Lift x t) = Lift x t
substTt x v u (Op op y) = Op op (substTt x v u y)
substTt x v u (Map f y) = Map (substTt x v u f) (substTt x v u y)
substTt _ _ _ Foldr = Foldr
substTt x v u (Rec t) = Rec (substTt x v u t) -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
substTt x v u (It t) = It (substTt x v u t) -- EXPERIMENTAL SUPPORT FOR ITERATION
-- Target language extension
substTt _ _ _ LId = LId
substTt x v u (LComp f g) = LComp (substTt x v u f) (substTt x v u g)
substTt x v u (LApp f a) = LApp (substTt x v u f) (substTt x v u a)
substTt x v u (LEval t) = LEval (substTt x v u t)
substTt _ _ _ LFst = LFst
substTt _ _ _ LSnd = LSnd
substTt x v u (LPair a b) = LPair (substTt x v u a) (substTt x v u b)
substTt x v u (Singleton t) = Singleton (substTt x v u t)
substTt _ _ _ Zero = Zero
substTt x v u (Plus a b) = Plus (substTt x v u a) (substTt x v u b)
substTt x v u (LSwap t) = LSwap (substTt x v u t)
substTt x v u (LCur t) = LCur (substTt x v u t)
substTt _ _ _ (LOp lop) = LOp lop
substTt x v u (DMap t) = DMap (substTt x v u t)
substTt x v u (DtMap t) = DtMap (substTt x v u t)
substTt _ _ _ DFoldr = DFoldr
substTt _ _ _ DtFoldr = DtFoldr
substTt x v u (DIt d1t d2t) = DIt (substTt x v u d1t) (substTt x v u d2t) -- EXPERIMENTAL SUPPORT FOR ITERATION
substTt x v u (DtIt d1t d2t) = DtIt (substTt x v u d1t) (substTt x v u d2t) -- EXPERIMENTAL SUPPORT FOR ITERATION

-- | Evaluate the target language
evalTt :: TTerm t -> t
-- Source language extension
evalTt (Var _ _) = error "Free variable has no value"
evalTt (Lambda x t e) = \v -> evalTt $ subst x v t e
evalTt (App f a) = evalTt f (evalTt a)
evalTt Unit = ()
evalTt (Pair a b) = (evalTt a, evalTt b)
evalTt (Fst p) = fst $ evalTt p
evalTt (Snd p) = snd $ evalTt p
evalTt (Inl p) = Left $ evalTt p -- EXPERIMENTAL SUPPORT FOR SUM TYPES
evalTt (Inr p) = Right $ evalTt p -- EXPERIMENTAL SUPPORT FOR SUM TYPES
evalTt (Case p l r) =
  case evalTt p -- EXPERIMENTAL SUPPORT FOR SUM TYPES
        of
    Left q  -> evalTt l q
    Right q -> evalTt r q
evalTt (Lift x _) = x
evalTt (Op op a) = evalOp op (evalTt a)
evalTt (Map f x) = V.map (evalTt f) (evalTt x)
evalTt Foldr = \((f, v), xs) -> V.foldr (\r a -> f (r, a)) v xs
evalTt (Rec t) = fix (evalTt t) -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
  where
    fix f a = f (a, fix f a)
evalTt (It t) = fix (evalTt t) -- EXPERIMENTAL SUPPORT FOR ITERATION
  where
    fix f (a, b) =
      case f (a, b) of
        Left c   -> c
        Right b' -> fix f (a, b')
-- Target language extension
evalTt (LOp lop) = evalLOp lop
evalTt LId = lId
evalTt (LComp f g) = lComp (evalTt f) (evalTt g)
evalTt (LEval t) = lEval (evalTt t)
evalTt (LApp f a) = lApp (evalTt f) (evalTt a)
evalTt LFst = lFst
evalTt LSnd = lSnd
evalTt (LPair a b) = lPair (evalTt a) (evalTt b)
evalTt (Singleton t) = T.singleton (evalTt t)
evalTt Zero = zero
evalTt (Plus a b) = plus (evalTt a) (evalTt b)
evalTt (LSwap t) = lSwap (evalTt t)
evalTt (LCur t) = lCur f
  where
    f x acc = plus (lApp (evalTt t (fst x)) (snd x)) acc
evalTt (DMap t) =
  plus (lComp lFst (lMap v)) (lComp lSnd (lZipWith' (snd . f) v))
  where
    (f, v) = evalTt t
evalTt (DtMap t) = lPair (lZip v) (lZipWith' (snd . f) v)
  where
    (f, v) = evalTt t
evalTt DFoldr = dFoldr
evalTt DtFoldr = dtFoldr
evalTt (DIt d1t d2t) = dIt (evalTt d1t) (evalTt d2t) -- EXPERIMENTAL SUPPORT FOR ITERATION
evalTt (DtIt d1t d2t) = dtIt (evalTt d1t) (evalTt d2t) -- EXPERIMENTAL SUPPORT FOR ITERATION

-- | Pretty print the target language
printTt :: TTerm t -> String
-- Source language extension
printTt (Var x _) = x
printTt (Lambda x _ e) = "\\" ++ x ++ " -> (" ++ printTt e ++ ")"
printTt (App f a) = printTt f ++ "(" ++ printTt a ++ ")"
printTt Unit = "()"
printTt (Pair a b) = "(" ++ printTt a ++ ", " ++ printTt b ++ ")"
printTt (Fst p) = "Fst(" ++ printTt p ++ ")"
printTt (Snd p) = "Snd(" ++ printTt p ++ ")"
printTt (Inl p) = "Inl(" ++ printTt p ++ ")" -- EXPERIMENTAL SUPPORT FOR SUM TYPES
printTt (Inr p) = "Inr(" ++ printTt p ++ ")" -- EXPERIMENTAL SUPPORT FOR SUM TYPES
printTt (Case p l r) =
  "Case(" ++ printTt p ++ ", " ++ printTt l ++ ", " ++ printTt r ++ ")" -- EXPERIMENTAL SUPPORT FOR SUM TYPES
printTt (Lift _ _) = error "Can't print lifted value"
printTt (Op op a) = "evalOp " ++ showOp op ++ " " ++ printTt a
printTt (Map f a) = "map (" ++ printTt f ++ ") " ++ printTt a
printTt Foldr = "foldr"
printTt (Rec t) = "rec(" ++ printTt t ++ ")" -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
printTt (It t) = "it(" ++ printTt t ++ ")" -- EXPERIMENTAL SUPPORT FOR ITERATION
-- Target language extension
printTt (LOp lop) = "evalLOp " ++ showLOp lop
printTt LId = "lid"
printTt (LComp f g) = "(" ++ printTt f ++ ";;" ++ printTt g ++ ")"
printTt (LEval e) = "leval(" ++ printTt e ++ ")"
printTt (LApp f a) = printTt f ++ "(" ++ printTt a ++ ")"
printTt LFst = "lfst"
printTt LSnd = "lsnd"
printTt (LPair a b) = "lpair(" ++ printTt a ++ ", " ++ printTt b ++ ")"
printTt (Singleton t) = "[(" ++ printTt t ++ ", -)]"
printTt Zero = "0"
printTt (Plus a b) = "(" ++ printTt a ++ ") + (" ++ printTt b ++ ")"
printTt (LSwap t) = "lswap(" ++ printTt t ++ ")"
printTt (LCur t) = "lcur(" ++ printTt t ++ ")"
printTt (DMap t) = "DMap(" ++ printTt t ++ ")"
printTt DFoldr = "DFoldr"
printTt DtFoldr = "DtFoldr"
printTt (DtMap t) = "DtMap(" ++ printTt t ++ ")"
printTt (DIt d1t d2t) = "DIt(" ++ printTt d1t ++ ", " ++ printTt d2t ++ ")" -- EXPERIMENTAL SUPPORT FOR ITERATION
printTt (DtIt d1t d2t) = "DtIt(" ++ printTt d1t ++ ", " ++ printTt d2t ++ ")" -- EXPERIMENTAL SUPPORT FOR ITERATION
