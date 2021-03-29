{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

-- | Definition of the target language
module TargetLanguage where

import           Data.Foldable (fold)
import           Data.GADT.Compare (geq)
import           Data.Maybe (fromMaybe)
import           Data.Monoid (Sum(..))
import           Data.Some

import           Data.Type.Equality        ((:~:) (Refl))
import qualified Data.Vector.Unboxed.Sized as V (Unbox, foldr, map)
import           GHC.TypeNats              (KnownNat)
import           Operation                 (LinearOperation, Operation, evalLOp,
                                            evalOp, showLOp, showOp)
import           TargetLanguage.Env
import           Types

-- | Terms of the target language
data TTerm env t where
  -- Terms from source language
  Var :: Idx env a -> TTerm env a
  Lambda :: Type a -> TTerm (a ': env) b -> TTerm env (a -> b)
  App :: (LT a, LT b) => TTerm env (a -> b) -> TTerm env a -> TTerm env b
  Unit :: TTerm env ()
  Pair :: TTerm env a -> TTerm env b -> TTerm env (a, b)
  Fst :: TTerm env (a, b) -> TTerm env a
  Snd :: TTerm env (a, b) -> TTerm env b
  Inl :: (LT a, LT b) => TTerm env a -> TTerm env (Either a b)
  Inr :: (LT a, LT b) => TTerm env b -> TTerm env (Either a b)
  Case
    :: (LT a, LT b, LT c)
    => TTerm env (Either a b)
    -> TTerm env (a -> c)
    -> TTerm env (b -> c)
    -> TTerm env c
  It :: TTerm env ((a, b) -> Either c b) -> TTerm env ((a, b) -> c)
  Rec :: TTerm env ((a, b) -> b) -> TTerm env (a -> b) -- Should we work with a representation that is variable binding instead?
  Sign :: TTerm env Scal -> TTerm env (Either () ())
  Lift :: a -> Type a -> TTerm env a
  -- | Operators
  Op :: Operation a b -> TTerm env a -> TTerm env b
  Map :: TTerm env (Scal -> Scal)
      -> TTerm env (Vect n)
      -> TTerm env (Vect n)
  Foldr :: (LT a, KnownNat n)
        => TTerm env ((Scal, a) -> a)
        -> TTerm env a
        -> TTerm env (Vect n)
        -> TTerm env a
  -- Target language extension
  -- | Linear operation
  LOp :: LT b => LinearOperation a b c -> TTerm env (a -> LFun b c)
  -- Linear functions
  LId :: TTerm env (LFun a a)
  LComp
    :: (LT a, LT b, LT c)
    => TTerm env (LFun a b)
    -> TTerm env (LFun b c)
    -> TTerm env (LFun a c)
  LApp :: (LT a, LT b) => TTerm env (LFun a b) -> TTerm env a -> TTerm env b
  LEval :: TTerm env a -> TTerm env (LFun (a -> b) b)
  -- Tuples
  LUnit :: TTerm env (LFun a ())
  LFst :: TTerm env (LFun (a, b) a)
  LSnd :: TTerm env (LFun (a, b) b)
  LPair
    :: (LT a, LT b, LT c)
    => TTerm env (LFun a b)
    -> TTerm env (LFun a c)
    -> TTerm env (LFun a (b, c))
  -- Variants
  LInl :: TTerm env (LFun a (LEither a b))
  LInr :: TTerm env (LFun b (LEither a b))
  LCoPair
    :: LT c
    => TTerm env (LFun a c)
    -> TTerm env (LFun b c)
    -> TTerm env (LFun (LEither a b) c)
  -- | Singleton
  Singleton :: TTerm env b -> TTerm env (LFun c (Copower b c))
  -- Zero
  Zero :: LT a => TTerm env a
  -- Plus
  Plus :: LT a => TTerm env a -> TTerm env a -> TTerm env a
  -- Swap
  LSwap
    :: (LT b, LT c, LT d) => TTerm env (b -> LFun c d) -> TTerm env (LFun c (b -> d))
  -- | Copower-elimination
  LCopowFold
    :: (LT b, LT c, LT d) => TTerm env (b -> LFun c d) -> TTerm env (LFun (Copower b c) d)
  -- Map derivatives
  DMap
    :: KnownNat n
    => TTerm env (Scal -> (Scal, LFun Scal Scal))
    -> TTerm env (Vect n)
    -> TTerm env (LFun (Scal -> Scal, Vect n) (Vect n))
  DtMap
    :: KnownNat n
    => TTerm env (Scal -> (Scal, LFun Scal Scal))
    -> TTerm env (Vect n)
    -> TTerm env (LFun (Vect n) (Copower Scal Scal, Vect n))
  DFoldr
    :: (KnownNat n, V.Unbox a, V.Unbox b, LT b)
    => TTerm env (((Scal, a) -> (a, LFun (Scal, b) b)))
    -> TTerm env a
    -> TTerm env (Vect n)
    -> TTerm env (LFun (((Scal, a) -> b, b), Vect n) b)
  DtFoldr
    :: (KnownNat n, V.Unbox a, V.Unbox b, LT b)
    => TTerm env ((Scal, a) -> (a, LFun b (Scal, b)))
    -> TTerm env a
    -> TTerm env (Vect n)
    -> TTerm env (LFun b ((Copower (Scal, a) b, b), Vect n))
  DIt
    :: (LT d2a, LT d2b, LT d2c)
    => TTerm env ((d1a, d1b) -> Either d1c d1b)
    -> TTerm env ((d1a, d1b) -> LFun (d2a, d2b) (LEither d2c d2b))
    -> TTerm env ((d1a, d1b) -> LFun (d2a, d2b) d2c)
  DtIt
    :: (LT d2a, LT d2b, LT d2c)
    => TTerm env ((d1a, d1b) -> Either d1c d1b)
    -> TTerm env ((d1a, d1b) -> LFun (LEither d2c d2b) (d2a, d2b))
    -> TTerm env ((d1a, d1b) -> LFun d2c (d2a, d2b))
  LRec :: TTerm env (LFun (a, b) b) -> TTerm env (LFun a b)
  LIt :: (LT a, LT b) => TTerm env (LFun b (a, b)) -> TTerm env (LFun b a)

-- | Utility function for creating lambda expressions
lambda :: LT a => TTerm (a ': env) t -> TTerm env (a -> t)
lambda = Lambda inferType

-- | Substitute variable with De Bruijn index zero in a 'TTerm'
substTt :: TTerm env u -> TTerm (u ': env) t -> TTerm env t
substTt v = substTt' Z v (Weaken $ \case Z -> error "substTt: replaced variable should've been replaced"
                                         S i -> i)

-- | Substitute given variable with the given environment weakening action in a
-- 'TTerm'
substTt' :: Idx env u -> TTerm env' u -> env :> env' -> TTerm env t -> TTerm env' t
substTt' i v w (Var i')
  | Just Refl <- geq i i' = v
  | otherwise = Var (w >:> i')
substTt' i v w (Lambda ty e) = Lambda ty (substTt' (S i) (sinkTt (wSucc wId) v) (wSink w) e)
substTt' i v w (App f a) = App (substTt' i v w f) (substTt' i v w a)
substTt' _ _ _ Unit = Unit
substTt' i v w (Pair a b) = Pair (substTt' i v w a) (substTt' i v w b)
substTt' i v w (Fst p) = Fst (substTt' i v w p)
substTt' i v w (Snd p) = Snd (substTt' i v w p)
substTt' i v w (Inl t) = Inl (substTt' i v w t)
substTt' i v w (Inr t) = Inr (substTt' i v w t)
substTt' i v w (Case t l r) =
  Case (substTt' i v w t) (substTt' i v w l) (substTt' i v w r)
substTt' _ _ _ (Lift x t) = Lift x t
substTt' i v w (Op op y) = Op op (substTt' i v w y)
substTt' i v w (Map f y) = Map (substTt' i v w f) (substTt' i v w y)
substTt' i v w (Foldr f x t) = Foldr (substTt' i v w f) (substTt' i v w x) (substTt' i v w t)
substTt' i v w (Rec t) = Rec (substTt' i v w t)
substTt' i v w (It t) = It (substTt' i v w t)
substTt' i v w (Sign t) = Sign (substTt' i v w t)
-- Target language extension
substTt' _ _ _ LId = LId
substTt' i v w (LComp f g) = LComp (substTt' i v w f) (substTt' i v w g)
substTt' i v w (LApp f a) = LApp (substTt' i v w f) (substTt' i v w a)
substTt' i v w (LEval t) = LEval (substTt' i v w t)
substTt' _ _ _ LUnit = LUnit
substTt' _ _ _ LFst = LFst
substTt' _ _ _ LSnd = LSnd
substTt' i v w (LPair a b) = LPair (substTt' i v w a) (substTt' i v w b)
substTt' _ _ _ LInl = LInl
substTt' _ _ _ LInr = LInr
substTt' i v w (LCoPair a b) = LCoPair (substTt' i v w a) (substTt' i v w b)
substTt' i v w (Singleton t) = Singleton (substTt' i v w t)
substTt' _ _ _ Zero = Zero
substTt' i v w (Plus a b) = Plus (substTt' i v w a) (substTt' i v w b)
substTt' i v w (LSwap t) = LSwap (substTt' i v w t)
substTt' i v w (LCopowFold t) = LCopowFold (substTt' i v w t)
substTt' _ _ _ (LOp lop) = LOp lop
substTt' i v w (DMap f x) = DMap (substTt' i v w f) (substTt' i v w x)
substTt' i v w (DtMap f x) = DtMap (substTt' i v w f) (substTt' i v w x)
substTt' i v w (DFoldr f x t) = DFoldr (substTt' i v w f) (substTt' i v w x) (substTt' i v w t)
substTt' i v w (DtFoldr f x t) = DtFoldr (substTt' i v w f) (substTt' i v w x) (substTt' i v w t)
substTt' i v w (DIt d1t d2t) = DIt (substTt' i v w d1t) (substTt' i v w d2t)
substTt' i v w (DtIt d1t d2t) = DtIt (substTt' i v w d1t) (substTt' i v w d2t)
substTt' i v w (LRec t) = LRec (substTt' i v w t)
substTt' i v w (LIt t) = LIt (substTt' i v w t)

-- | Evaluate the target language
evalTt :: TTerm '[] t -> t
evalTt = evalTt' VZ

-- | Evaluate the target language in the given environment
evalTt' :: Val env -> TTerm env t -> t
-- Source language extension
evalTt' env (Var i) = valProject env i
evalTt' env (Lambda _ e) = \v -> evalTt' (VS v env) e
evalTt' env (App f a) = evalTt' env f (evalTt' env a)
evalTt' _   Unit = ()
evalTt' env (Pair a b) = (evalTt' env a, evalTt' env b)
evalTt' env (Fst p) = fst $ evalTt' env p
evalTt' env (Snd p) = snd $ evalTt' env p
evalTt' env (Inl p) = Left $ evalTt' env p
evalTt' env (Inr p) = Right $ evalTt' env p
evalTt' env (Case p l r) =
  case evalTt' env p of
    Left q  -> evalTt' env l q
    Right q -> evalTt' env r q
evalTt' _   (Lift x _) = x
evalTt' env (Op op a) = evalOp op (evalTt' env a)
evalTt' env (Map f x) = V.map (evalTt' env f) (evalTt' env x)
evalTt' env (Foldr f v xs) = V.foldr (\r a -> evalTt' env f (r, a)) (evalTt' env v) (evalTt' env xs)
evalTt' env (Rec t) = fix (evalTt' env t)
  where
    fix f a = f (a, fix f a)
evalTt' env (It t) = fix (evalTt' env t)
  where
    fix f (a, b) =
      case f (a, b) of
        Left c   -> c
        Right b' -> fix f (a, b')
evalTt' env (Sign t) =
  let r = evalTt' env t
   in if r < 0
        then Left ()
        else if r > 0
               then Right ()
               else error "Tried to call real conditional at 0"
-- Target language extension
evalTt' _   (LOp lop) = evalLOp lop
evalTt' _   LId = lId
evalTt' env (LComp f g) = lComp (evalTt' env f) (evalTt' env g)
evalTt' env (LEval t) = lEval (evalTt' env t)
evalTt' env (LApp f a) = lApp (evalTt' env f) (evalTt' env a)
evalTt' _   LUnit = lUnit
evalTt' _   LFst = lFst
evalTt' _   LSnd = lSnd
evalTt' env (LPair a b) = lPair (evalTt' env a) (evalTt' env b)
evalTt' _   LInl = lInl
evalTt' _   LInr = lInr
evalTt' env (LCoPair a b) = lCoPair (evalTt' env a) (evalTt' env b)
evalTt' env (Singleton t) = singleton (evalTt' env t)
evalTt' _   Zero = zero
evalTt' env (Plus a b) = plus (evalTt' env a) (evalTt' env b)
evalTt' env (LSwap t) = lSwap (evalTt' env t)
evalTt' env (LCopowFold t) = lCopowFold (evalTt' env t)
evalTt' env (DMap f v) =
    plus (lComp lFst (lMap v')) (lComp lSnd (lZipWith (snd . evalTt' env f) v'))
  where v' = evalTt' env v
evalTt' env (DtMap f v) = lPair (lZip v') (lZipWith (snd . evalTt' env f) v')
  where v' = evalTt' env v
evalTt' env (DFoldr f v xs) = dFoldr (evalTt' env f) (evalTt' env v) (evalTt' env xs)
evalTt' env (DtFoldr f v xs) = dtFoldr (evalTt' env f) (evalTt' env v) (evalTt' env xs)
evalTt' env (DIt d1t d2t) = dIt (evalTt' env d1t) (evalTt' env d2t)
evalTt' env (DtIt d1t d2t) = dtIt (evalTt' env d1t) (evalTt' env d2t)
evalTt' env (LRec t) = lRec (evalTt' env t)
evalTt' env (LIt t) = lIt (evalTt' env t)

sinkTt :: env :> env' -> TTerm env t -> TTerm env' t
sinkTt w (Var i) = Var (w >:> i)
sinkTt w (Lambda ty e) = Lambda ty (sinkTt (wSink w) e)
sinkTt w (App e1 e2) = App (sinkTt w e1) (sinkTt w e2)
sinkTt _ Unit = Unit
sinkTt w (Pair a b) = Pair (sinkTt w a) (sinkTt w b)
sinkTt w (Fst p) = Fst (sinkTt w p)
sinkTt w (Snd p) = Snd (sinkTt w p)
sinkTt w (Inl p) = Inl (sinkTt w p)
sinkTt w (Inr p) = Inr (sinkTt w p)
sinkTt w (Case p g h) = Case (sinkTt w p) (sinkTt w g) (sinkTt w h)
sinkTt _ (Lift x t) = Lift x t
sinkTt w (Op op a) = Op op (sinkTt w a)
sinkTt w (Map g y) = Map (sinkTt w g) (sinkTt w y)
sinkTt w (Foldr f v xs) = Foldr (sinkTt w f) (sinkTt w v) (sinkTt w xs)
sinkTt w (Rec s) = Rec (sinkTt w s)
sinkTt w (It s) = It (sinkTt w s)
sinkTt w (Sign s) = Sign (sinkTt w s)
sinkTt _ LId = LId
sinkTt w (LComp g h) = LComp (sinkTt w g) (sinkTt w h)
sinkTt w (LApp g a) = LApp (sinkTt w g) (sinkTt w a)
sinkTt w (LEval e) = LEval (sinkTt w e)
sinkTt _ LUnit = LUnit
sinkTt _ LFst = LFst
sinkTt _ LSnd = LSnd
sinkTt w (LPair a b) = LPair (sinkTt w a) (sinkTt w b)
sinkTt _ LInl = LInl
sinkTt _ LInr = LInr
sinkTt w (LCoPair a b) = LCoPair (sinkTt w a) (sinkTt w b)
sinkTt w (Singleton s) = Singleton (sinkTt w s)
sinkTt _ Zero = Zero
sinkTt w (Plus a b) = Plus (sinkTt w a) (sinkTt w b)
sinkTt w (LSwap s) = LSwap (sinkTt w s)
sinkTt w (LCopowFold s) = LCopowFold (sinkTt w s)
sinkTt _ (LOp op) = LOp op
sinkTt w (DMap f xs) = DMap (sinkTt w f) (sinkTt w xs)
sinkTt w (DtMap f xs) = DtMap (sinkTt w f) (sinkTt w xs)
sinkTt w (DFoldr f v xs) = DFoldr (sinkTt w f) (sinkTt w v) (sinkTt w xs)
sinkTt w (DtFoldr f v xs) = DtFoldr (sinkTt w f) (sinkTt w v) (sinkTt w xs)
sinkTt w (DIt d1t d2t) = DIt (sinkTt w d1t) (sinkTt w d2t)
sinkTt w (DtIt d1t d2t) = DtIt (sinkTt w d1t) (sinkTt w d2t)
sinkTt w (LRec s) = LRec (sinkTt w s)
sinkTt w (LIt s) = LIt (sinkTt w s)

-- | Pretty print the target language
--
-- Precedences used are as follows:
-- - application is 10
-- - plus is 6
-- - linear composition (;;) is 1
printTt :: Int -> TTerm env t -> ShowS
-- Source language extension
printTt _ (Var i) = shows i
printTt d (Lambda ty e) = showParen (d > 0) $ showString "λ(" . shows ty . showString ")." . printTt 0 e
printTt d (App f a) = showParen (d > 10) $ printTt 10 f . showString " " . printTt 11 a
printTt _ Unit = showString "()"
printTt _ (Pair a b) = showString "(" . printTt 0 a . showString ", " . printTt 0 b . showString ")"
printTt d (Fst p) = showFunction d "Fst" [Some p]
printTt d (Snd p) = showFunction d "Snd" [Some p]
printTt d (Inl p) = showFunction d "Inl" [Some p]
printTt d (Inr p) = showFunction d "Inr" [Some p]
printTt d (Case p l r) =
  showParen (d > 0) $
    showString "Case " . printTt 0 p . showString " in {" . printTt 0 l . showString " } { " . printTt 0 r . showString "}"
printTt _ (Lift _ _) = error "Can't print lifted value"
printTt d (Op op a) = showFunction d ("evalOp " ++ showOp op) [Some a]
printTt d (Map f a) = showFunction d "map" [Some f, Some a]
printTt d (Foldr f v xs) = showFunction d "foldr" [Some f, Some v, Some xs]
printTt d (Rec t) = showFunction d "rec" [Some t]
printTt d (It t) = showFunction d "it" [Some t]
printTt d (Sign t) = showFunction d "sign" [Some t]
-- Target language extension
printTt d (LOp lop) = showParen (d > 10) $ showString ("evalLOp " ++ showLOp lop)
printTt _ LId = showString "lid"
printTt d (LComp f g) = showParen (d > 1) $ printTt 1 f . showString " ;; " . printTt 1 g
printTt d (LEval e) = showFunction d "leval" [Some e]
printTt d (LApp f a) = showParen (d > 10) $ printTt 11 f . showString " " . printTt 11 a
printTt _ LUnit = showString "lunit"
printTt _ LFst = showString "lfst"
printTt _ LSnd = showString "lsnd"
printTt d (LPair a b) = showFunction d "lpair" [Some a, Some b]
printTt _ LInl = showString "linl"
printTt _ LInr = showString "linr"
printTt d (LCoPair a b) = showFunction d "lcopair" [Some a, Some b]
printTt _ (Singleton t) = showString "[(" . printTt 0 t . showString  ", -)]"
printTt _ Zero = showString "0F"
printTt d (Plus f g) = showParen (d > 6) $ printTt 6 f . showString " + " . printTt 6 g
printTt d (LSwap t) = showFunction d "lswap" [Some t]
printTt d (LCopowFold t) = showFunction d "lcopowfold" [Some t]
printTt d (DMap f xs) = showFunction d "DMap" [Some f, Some xs]
printTt d (DtMap f xs) = showFunction d "DtMap" [Some f, Some xs]
printTt d (DFoldr f v xs) = showFunction d "DFoldr" [Some f, Some v, Some xs]
printTt d (DtFoldr f v xs) = showFunction d "DtFoldr" [Some f, Some v, Some xs]
printTt d (DIt d1t d2t) = showFunction d "DIt" [Some d1t, Some d2t]
printTt d (DtIt d1t d2t) = showFunction d "DtIt" [Some d1t, Some d2t]
printTt d (LRec t) = showFunction d "lrec" [Some t]
printTt d (LIt t) = showFunction d "lit" [Some t]

data SomeTTerm = forall env t. SomeTTerm (TTerm env t)

showFunction :: Int -> String -> [Some (TTerm env)] -> ShowS
showFunction d funcname args =
  showParen (d > 10) $
    showString funcname
      . foldr (\(Some t) -> (.) (showString " " . printTt 11 t)) id args

instance Show (TTerm env a) where
  showsPrec p = printTt p

data Layout a = LyLeaf a | LyPair (Layout a) (Layout a)
  deriving (Show)

instance Functor Layout where
  fmap f (LyLeaf x) = LyLeaf (f x)
  fmap f (LyPair l1 l2) = LyPair (fmap f l1) (fmap f l2)

instance Foldable Layout where
  foldMap f (LyLeaf x) = f x
  foldMap f (LyPair l1 l2) = foldMap f l1 <> foldMap f l2

instance Semigroup a => Semigroup (Layout a) where
  LyLeaf a <> LyLeaf b = LyLeaf (a <> b)
  l@(LyLeaf _) <> LyPair l1 l2 = LyPair (l <> l1) (l <> l2)
  LyPair l1 l2 <> l@(LyLeaf _) = LyPair (l1 <> l) (l2 <> l)
  LyPair l1 l2 <> LyPair l3 l4 = LyPair (l1 <> l3) (l2 <> l4)

instance Monoid a => Monoid (Layout a) where
  mempty = LyLeaf mempty

-- Monoid is strictly speaking not necessary here with a more careful implementation
truncateLayoutWithExpr :: Monoid s => Layout s -> TTerm env a -> Layout s
truncateLayoutWithExpr l@(LyLeaf _) _ = l
truncateLayoutWithExpr (LyPair l1 l2) (Pair e1 e2) =
    LyPair (truncateLayoutWithExpr l1 e1) (truncateLayoutWithExpr l2 e2)
truncateLayoutWithExpr l@(LyPair _ _) _ = LyLeaf (fold l)

-- | Count the uses of a variable in an expression
usesOf :: Idx env t -> TTerm env a -> Integer
usesOf x t = getSum (fold (usesOf' x t))

-- | Count the uses of the components of a variable in an expression
usesOf' :: (Num s, Monoid s) => Idx env t -> TTerm env a -> Layout s
usesOf' i (Var i')
  | Just Refl <- geq i i' = LyLeaf 1
  | otherwise = mempty
usesOf' i (Lambda _ e) = usesOf' (S i) e
usesOf' i (App f a) = usesOf' i f <> usesOf' i a
usesOf' _ Unit = mempty
usesOf' i (Pair a b) = usesOf' i a <> usesOf' i b
usesOf' i p@(Fst p') = fromMaybe (usesOf' i p') (usesOfPick i p)
usesOf' i p@(Snd p') = fromMaybe (usesOf' i p') (usesOfPick i p)
usesOf' i (Inl p) = usesOf' i p
usesOf' i (Inr p) = usesOf' i p
usesOf' i (Case p f g) = usesOf' i p <> usesOf' i f <> usesOf' i g
usesOf' _ (Lift _ _) = mempty
usesOf' i (Op _ a) = usesOf' i a
usesOf' i (Map f y) = usesOf' i f <> usesOf' i y
usesOf' i (Foldr f v xs) = usesOf' i f <> usesOf' i v <> usesOf' i xs
usesOf' i (Rec s) = usesOf' i s
usesOf' i (It s) = usesOf' i s
usesOf' i (Sign s) = usesOf' i s
usesOf' _ LId = mempty
usesOf' i (LComp f g) = usesOf' i f <> usesOf' i g
usesOf' i (LApp f a) = usesOf' i f <> usesOf' i a
usesOf' i (LEval e) = usesOf' i e
usesOf' _ LUnit = mempty
usesOf' _ LFst = mempty
usesOf' _ LSnd = mempty
usesOf' i (LPair a b) = usesOf' i a <> usesOf' i b
usesOf' _ LInl = mempty
usesOf' _ LInr = mempty
usesOf' i (LCoPair a b) = usesOf' i a <> usesOf' i b
usesOf' i (Singleton s) = usesOf' i s
usesOf' _ Zero = mempty
usesOf' i (Plus a b) = usesOf' i a <> usesOf' i b
usesOf' i (LSwap s) = usesOf' i s
usesOf' i (LCopowFold s) = usesOf' i s
usesOf' _ (LOp _) = mempty
usesOf' i (DMap f xs) = usesOf' i f <> usesOf' i xs
usesOf' i (DtMap f xs) = usesOf' i f <> usesOf' i xs
usesOf' i (DFoldr f v xs) = usesOf' i f <> usesOf' i v <> usesOf' i xs
usesOf' i (DtFoldr f v xs) = usesOf' i f <> usesOf' i v <> usesOf' i xs
usesOf' i (DIt d1t d2t) = usesOf' i d1t <> usesOf' i d2t
usesOf' i (DtIt d1t d2t) = usesOf' i d1t <> usesOf' i d2t
usesOf' i (LRec s) = usesOf' i s
usesOf' i (LIt s) = usesOf' i s

usesOfPick :: (Num s, Monoid s) => Idx env t -> TTerm env a -> Maybe (Layout s)
usesOfPick i term = do
    path <- getPath i term
    return (increment (reverse path))
  where
    getPath :: Idx env t -> TTerm env a -> Maybe [Pick]
    getPath j (Fst p) = (PickFst :) <$> getPath j p
    getPath j (Snd p) = (PickSnd :) <$> getPath j p
    getPath j (Var j')
      | Just Refl <- geq j j' = Just []
    getPath _ _ = Nothing

    increment :: (Num s, Monoid s) => [Pick] -> Layout s
    increment [] = LyLeaf 1
    increment (PickFst : picks) = LyPair (increment picks) mempty
    increment (PickSnd : picks) = LyPair mempty (increment picks)

data Pick = PickFst | PickSnd
