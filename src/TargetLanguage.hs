{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}

-- | Definition of the target language
module TargetLanguage where

import           Data.Foldable (fold)
import           Data.Maybe (fromMaybe)
import           Data.Monoid (Sum(..))
import qualified Data.Set                  as Set

import           Data.Type.Equality        ((:~:) (Refl))
import qualified Data.Vector.Unboxed.Sized as V (Unbox, foldr, map)
import           GHC.TypeNats              (KnownNat)
import           Operation                 (LinearOperation, Operation, evalLOp,
                                            evalOp, showLOp, showOp)
import           Types                     as T (LEither, LFun, LT (..), Scal,
                                                 Copower, Type, Vect, dFoldr, dIt,
                                                 dtFoldr, dtIt, eqTy, lApp,
                                                 lCoPair, lComp, lCopowFold, lEval,
                                                 lFst, lId, lInl, lInr, lIt,
                                                 lMap, lPair, lRec, lSnd, lSwap,
                                                 lUnit, lZip, lZipWith,
                                                 singleton)

-- | Terms of the target language
data TTerm t where
  -- Terms from source language
  Var :: String -> Type a -> TTerm a
  Lambda :: String -> Type a -> TTerm b -> TTerm (a -> b)
  App :: (LT a, LT b) => TTerm (a -> b) -> TTerm a -> TTerm b
  Unit :: TTerm ()
  Pair :: TTerm a -> TTerm b -> TTerm (a, b)
  Fst :: TTerm (a, b) -> TTerm a
  Snd :: TTerm (a, b) -> TTerm b
  Inl :: (LT a, LT b) => TTerm a -> TTerm (Either a b)
  Inr :: (LT a, LT b) => TTerm b -> TTerm (Either a b)
  Case
    :: (LT a, LT b, LT c)
    => TTerm (Either a b)
    -> TTerm (a -> c)
    -> TTerm (b -> c)
    -> TTerm c
  It :: TTerm ((a, b) -> Either c b) -> TTerm ((a, b) -> c)
  Rec :: TTerm ((a, b) -> b) -> TTerm (a -> b) -- Should we work with a representation that is variable binding instead?
  Sign :: TTerm Scal -> TTerm (Either () ())
  Lift :: a -> Type a -> TTerm a
  -- | Operators
  Op :: Operation a b -> TTerm a -> TTerm b
  Map :: TTerm (Scal -> Scal) -> TTerm (Vect n) -> TTerm (Vect n)
  Foldr :: (LT a, KnownNat n) => TTerm ((((Scal, a) -> a, a), Vect n) -> a)
  -- Target language extension
  -- | Linear operation
  LOp :: LT b => LinearOperation a b c -> TTerm (a -> LFun b c)
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
  LUnit :: TTerm (LFun a ())
  LFst :: TTerm (LFun (a, b) a)
  LSnd :: TTerm (LFun (a, b) b)
  LPair
    :: (LT a, LT b, LT c)
    => TTerm (LFun a b)
    -> TTerm (LFun a c)
    -> TTerm (LFun a (b, c))
  -- Variants
  LInl :: TTerm (LFun a (LEither a b))
  LInr :: TTerm (LFun b (LEither a b))
  LCoPair
    :: LT c
    => TTerm (LFun a c)
    -> TTerm (LFun b c)
    -> TTerm (LFun (LEither a b) c)
  -- | Singleton
  Singleton :: TTerm b -> TTerm (LFun c (Copower b c))
  -- Zero
  Zero :: LT a => TTerm a
  -- Plus
  Plus :: LT a => TTerm a -> TTerm a -> TTerm a
  -- Swap
  LSwap
    :: (LT b, LT c, LT d) => TTerm (b -> LFun c d) -> TTerm (LFun c (b -> d))
  -- | Copower-elimination
  LCopowFold
    :: (LT b, LT c, LT d) => TTerm (b -> LFun c d) -> TTerm (LFun (Copower b c) d)
  -- Map derivatives
  DMap
    :: KnownNat n
    => TTerm (Scal -> (Scal, LFun Scal Scal), Vect n)
    -> TTerm (LFun (Scal -> Scal, Vect n) (Vect n))
  DtMap
    :: KnownNat n
    => TTerm (Scal -> (Scal, LFun Scal Scal), Vect n)
    -> TTerm (LFun (Vect n) (Copower Scal Scal, Vect n))
  DFoldr
    :: (KnownNat n, V.Unbox a, V.Unbox b, LT b)
    => TTerm ((((Scal, a) -> (a, LFun (Scal, b) b), a), Vect n) -> LFun ( ( ( Scal
                                                                            , a) -> b
                                                                          , b)
                                                                        , Vect n) b)
  DtFoldr
    :: (KnownNat n, V.Unbox a, V.Unbox b, LT b)
    => TTerm ((((Scal, a) -> (a, LFun b (Scal, b)), a), Vect n) -> LFun b ( ( Copower ( Scal
                                                                                   , a) b
                                                                            , b)
                                                                          , Vect n))
  DIt
    :: (LT d2a, LT d2b, LT d2c)
    => TTerm ((d1a, d1b) -> Either d1c d1b)
    -> TTerm ((d1a, d1b) -> LFun (d2a, d2b) (LEither d2c d2b))
    -> TTerm ((d1a, d1b) -> LFun (d2a, d2b) d2c)
  DtIt
    :: (LT d2a, LT d2b, LT d2c)
    => TTerm ((d1a, d1b) -> Either d1c d1b)
    -> TTerm ((d1a, d1b) -> LFun (LEither d2c d2b) (d2a, d2b))
    -> TTerm ((d1a, d1b) -> LFun d2c (d2a, d2b))
  LRec :: TTerm (LFun (a, b) b) -> TTerm (LFun a b)
  LIt :: (LT a, LT b) => TTerm (LFun b (a, b)) -> TTerm (LFun b a)

-- | Substitute variable for a TTerm
substTt :: String -> TTerm u -> Type u -> TTerm t -> TTerm t
substTt x v u (Var y t)
  | x == y =
    case eqTy u t of
      Just Refl -> v
      Nothing ->
        error
          ("Ill-typed substitution. Tried to match type " ++
           show u ++ " with " ++ show t)
  | otherwise = Var y t
substTt x v u (Lambda y t e)
  -- Substituting for variable x under λx. E does nothing
  | x == y = Lambda y t e
  -- When substituting F under λx. E where x occurs in F, we first need to
  -- alpha-rename x to something unused in both E and F, and only afterwards
  -- substitute normally.
  | usesOf y v >= 1 =
      let y' = freshVariable (allVars v ++ allVars e)
      in Lambda y' t (substTt x v u (substTt y (Var y' t) t e))
  -- Otherwise, we can substitute normally.
  | otherwise = Lambda y t (substTt x v u e)
substTt x v u (App f a) = App (substTt x v u f) (substTt x v u a)
substTt _ _ _ Unit = Unit
substTt x v u (Pair a b) = Pair (substTt x v u a) (substTt x v u b)
substTt x v u (Fst p) = Fst (substTt x v u p)
substTt x v u (Snd p) = Snd (substTt x v u p)
substTt x v u (Inl t) = Inl (substTt x v u t)
substTt x v u (Inr t) = Inr (substTt x v u t)
substTt x v u (Case t l r) =
  Case (substTt x v u t) (substTt x v u l) (substTt x v u r)
substTt _ _ _ (Lift x t) = Lift x t
substTt x v u (Op op y) = Op op (substTt x v u y)
substTt x v u (Map f y) = Map (substTt x v u f) (substTt x v u y)
substTt _ _ _ Foldr = Foldr
substTt x v u (Rec t) = Rec (substTt x v u t)
substTt x v u (It t) = It (substTt x v u t)
substTt x v u (Sign t) = Sign (substTt x v u t)
-- Target language extension
substTt _ _ _ LId = LId
substTt x v u (LComp f g) = LComp (substTt x v u f) (substTt x v u g)
substTt x v u (LApp f a) = LApp (substTt x v u f) (substTt x v u a)
substTt x v u (LEval t) = LEval (substTt x v u t)
substTt _ _ _ LUnit = LUnit
substTt _ _ _ LFst = LFst
substTt _ _ _ LSnd = LSnd
substTt x v u (LPair a b) = LPair (substTt x v u a) (substTt x v u b)
substTt _ _ _ LInl = LInl
substTt _ _ _ LInr = LInr
substTt x v u (LCoPair a b) = LCoPair (substTt x v u a) (substTt x v u b)
substTt x v u (Singleton t) = Singleton (substTt x v u t)
substTt _ _ _ Zero = Zero
substTt x v u (Plus a b) = Plus (substTt x v u a) (substTt x v u b)
substTt x v u (LSwap t) = LSwap (substTt x v u t)
substTt x v u (LCopowFold t) = LCopowFold (substTt x v u t)
substTt _ _ _ (LOp lop) = LOp lop
substTt x v u (DMap t) = DMap (substTt x v u t)
substTt x v u (DtMap t) = DtMap (substTt x v u t)
substTt _ _ _ DFoldr = DFoldr
substTt _ _ _ DtFoldr = DtFoldr
substTt x v u (DIt d1t d2t) = DIt (substTt x v u d1t) (substTt x v u d2t)
substTt x v u (DtIt d1t d2t) = DtIt (substTt x v u d1t) (substTt x v u d2t)
substTt x v u (LRec t) = LRec (substTt x v u t)
substTt x v u (LIt t) = LIt (substTt x v u t)

-- | Evaluate the target language
evalTt :: TTerm t -> t
-- Source language extension
evalTt (Var _ _) = error "Free variable has no value"
evalTt (Lambda x t e) = \v -> evalTt $ substTt x (Lift v t) t e
evalTt (App f a) = evalTt f (evalTt a)
evalTt Unit = ()
evalTt (Pair a b) = (evalTt a, evalTt b)
evalTt (Fst p) = fst $ evalTt p
evalTt (Snd p) = snd $ evalTt p
evalTt (Inl p) = Left $ evalTt p
evalTt (Inr p) = Right $ evalTt p
evalTt (Case p l r) =
  case evalTt p of
    Left q  -> evalTt l q
    Right q -> evalTt r q
evalTt (Lift x _) = x
evalTt (Op op a) = evalOp op (evalTt a)
evalTt (Map f x) = V.map (evalTt f) (evalTt x)
evalTt Foldr = \((f, v), xs) -> V.foldr (\r a -> f (r, a)) v xs
evalTt (Rec t) = fix (evalTt t)
  where
    fix f a = f (a, fix f a)
evalTt (It t) = fix (evalTt t)
  where
    fix f (a, b) =
      case f (a, b) of
        Left c   -> c
        Right b' -> fix f (a, b')
evalTt (Sign t) =
  let r = evalTt t
   in if r < 0
        then Left ()
        else if r > 0
               then Right ()
               else error "Tried to call real conditional at 0"
-- Target language extension
evalTt (LOp lop) = evalLOp lop
evalTt LId = lId
evalTt (LComp f g) = lComp (evalTt f) (evalTt g)
evalTt (LEval t) = lEval (evalTt t)
evalTt (LApp f a) = lApp (evalTt f) (evalTt a)
evalTt LUnit = lUnit
evalTt LFst = lFst
evalTt LSnd = lSnd
evalTt (LPair a b) = lPair (evalTt a) (evalTt b)
evalTt LInl = lInl
evalTt LInr = lInr
evalTt (LCoPair a b) = lCoPair (evalTt a) (evalTt b)
evalTt (Singleton t) = T.singleton (evalTt t)
evalTt Zero = zero
evalTt (Plus a b) = plus (evalTt a) (evalTt b)
evalTt (LSwap t) = lSwap (evalTt t)
evalTt (LCopowFold t) = lCopowFold (evalTt t)
evalTt (DMap t) = plus (lComp lFst (lMap v)) (lComp lSnd (lZipWith (snd . f) v))
  where
    (f, v) = evalTt t
evalTt (DtMap t) = lPair (lZip v) (lZipWith (snd . f) v)
  where
    (f, v) = evalTt t
evalTt DFoldr = dFoldr
evalTt DtFoldr = dtFoldr
evalTt (DIt d1t d2t) = dIt (evalTt d1t) (evalTt d2t)
evalTt (DtIt d1t d2t) = dtIt (evalTt d1t) (evalTt d2t)
evalTt (LRec t) = lRec (evalTt t)
evalTt (LIt t) = lIt (evalTt t)

-- | Pretty print the target language
--
-- Precedences used are as follows:
-- - application is 10
-- - plus is 6
-- - linear composition (;;) is 1
printTt :: Int -> TTerm t -> ShowS
-- Source language extension
printTt _ (Var x _) = showString x
printTt d (Lambda x _ e) = showParen (d > 0) $ showString ("\\" ++ x) . showString " -> " . printTt 0 e
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
printTt _ Foldr = showString "foldr"
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
printTt d (DMap t) = showFunction d "DMap" [Some t]
printTt d (DtMap t) = showFunction d "DtMap" [Some t]
printTt _ DFoldr = showString "DFoldr"
printTt _ DtFoldr = showString "DtFoldr"
printTt d (DIt d1t d2t) = showFunction d "DIt" [Some d1t, Some d2t]
printTt d (DtIt d1t d2t) = showFunction d "DtIt" [Some d1t, Some d2t]
printTt d (LRec t) = showFunction d "lrec" [Some t]
printTt d (LIt t) = showFunction d "lit" [Some t]

data Some f = forall a. Some (f a)

withSome :: (forall a. f a -> b) -> Some f -> b
withSome f (Some x) = f x

showFunction :: Int -> String -> [Some TTerm] -> ShowS
showFunction d funcname args =
  showParen (d > 10) $
    showString funcname
      . foldr (.) id (map (withSome (\t -> showString " " . printTt 11 t)) args)

instance Show (TTerm a) where
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
truncateLayoutWithExpr :: Monoid s => Layout s -> TTerm a -> Layout s
truncateLayoutWithExpr l@(LyLeaf _) _ = l
truncateLayoutWithExpr (LyPair l1 l2) (Pair e1 e2) =
    LyPair (truncateLayoutWithExpr l1 e1) (truncateLayoutWithExpr l2 e2)
truncateLayoutWithExpr l@(LyPair _ _) _ = LyLeaf (fold l)

-- | Count the uses of a variable in an expression
usesOf :: String -> TTerm a -> Integer
usesOf x t = getSum (fold (usesOf' x t))

-- | Count the uses of the components of a variable in an expression
usesOf' :: (Num s, Monoid s) => String -> TTerm a -> Layout s
usesOf' x (Var y _)
  | x == y = LyLeaf 1
  | otherwise = mempty
usesOf' x (Lambda y _ e)
  | x == y = mempty
  | otherwise = usesOf' x e
usesOf' x (App f a) = usesOf' x f <> usesOf' x a
usesOf' _ Unit = mempty
usesOf' x (Pair a b) = usesOf' x a <> usesOf' x b
usesOf' x p@(Fst p') = fromMaybe (usesOf' x p') (usesOfPick x p)
usesOf' x p@(Snd p') = fromMaybe (usesOf' x p') (usesOfPick x p)
usesOf' x (Inl p) = usesOf' x p
usesOf' x (Inr p) = usesOf' x p
usesOf' x (Case p f g) = usesOf' x p <> usesOf' x f <> usesOf' x g
usesOf' _ (Lift _ _) = mempty
usesOf' x (Op _ a) = usesOf' x a
usesOf' x (Map f y) = usesOf' x f <> usesOf' x y
usesOf' _ Foldr = mempty
usesOf' x (Rec s) = usesOf' x s
usesOf' x (It s) = usesOf' x s
usesOf' x (Sign s) = usesOf' x s
usesOf' _ LId = mempty
usesOf' x (LComp f g) = usesOf' x f <> usesOf' x g
usesOf' x (LApp f a) = usesOf' x f <> usesOf' x a
usesOf' x (LEval e) = usesOf' x e
usesOf' _ LUnit = mempty
usesOf' _ LFst = mempty
usesOf' _ LSnd = mempty
usesOf' x (LPair a b) = usesOf' x a <> usesOf' x b
usesOf' _ LInl = mempty
usesOf' _ LInr = mempty
usesOf' x (LCoPair a b) = usesOf' x a <> usesOf' x b
usesOf' x (Singleton s) = usesOf' x s
usesOf' _ Zero = mempty
usesOf' x (Plus a b) = usesOf' x a <> usesOf' x b
usesOf' x (LSwap s) = usesOf' x s
usesOf' x (LCopowFold s) = usesOf' x s
usesOf' _ (LOp _) = mempty
usesOf' x (DMap s) = usesOf' x s
usesOf' x (DtMap s) = usesOf' x s
usesOf' _ DFoldr = mempty
usesOf' _ DtFoldr = mempty
usesOf' x (DIt d1t d2t) = usesOf' x d1t <> usesOf' x d2t
usesOf' x (DtIt d1t d2t) = usesOf' x d1t <> usesOf' x d2t
usesOf' x (LRec s) = usesOf' x s
usesOf' x (LIt s) = usesOf' x s

usesOfPick :: (Num s, Monoid s) => String -> TTerm a -> Maybe (Layout s)
usesOfPick x term = do
    path <- getPath term
    return (increment (reverse path))
  where
    getPath :: TTerm a -> Maybe [Pick]
    getPath (Fst p) = (PickFst :) <$> getPath p
    getPath (Snd p) = (PickSnd :) <$> getPath p
    getPath (Var y _)
      | x == y = Just []
    getPath _ = Nothing

    increment :: (Num s, Monoid s) => [Pick] -> Layout s
    increment [] = LyLeaf 1
    increment (PickFst : picks) = LyPair (increment picks) mempty
    increment (PickSnd : picks) = LyPair mempty (increment picks)

data Pick = PickFst | PickSnd

allVars :: TTerm a -> [String]
allVars (Var x _) = [x]
allVars (Lambda x _ e) = x : allVars e
allVars (App e1 e2) = allVars e1 ++ allVars e2
allVars Unit = []
allVars (Pair e1 e2) = allVars e1 ++ allVars e2
allVars (Fst e) = allVars e
allVars (Snd e) = allVars e
allVars (Inl e) = allVars e
allVars (Inr e) = allVars e
allVars (Case e1 e2 e3) = allVars e1 ++ allVars e2 ++ allVars e3
allVars (It e) = allVars e
allVars (Rec e) = allVars e
allVars (Sign e) = allVars e
allVars (Lift  _ _) = []
allVars (Op  _ e) = allVars e
allVars (Map e1 e2) = allVars e1 ++ allVars e2
allVars Foldr = []
allVars (LOp _) = []
allVars LId = []
allVars (LComp e1 e2) = allVars e1 ++ allVars e2
allVars (LApp e1 e2) = allVars e1 ++ allVars e2
allVars (LEval e) = allVars e
allVars LUnit = []
allVars LFst = []
allVars LSnd = []
allVars (LPair e1 e2) = allVars e1 ++ allVars e2
allVars LInl = []
allVars LInr = []
allVars (LCoPair e1 e2) = allVars e1 ++ allVars e2
allVars (Singleton e) = allVars e
allVars Zero = []
allVars (Plus e1 e2) = allVars e1 ++ allVars e2
allVars (LSwap e) = allVars e
allVars (LCopowFold e) = allVars e
allVars (DMap e) = allVars e
allVars (DtMap e) = allVars e
allVars DFoldr = []
allVars DtFoldr = []
allVars (DIt e1 e2) = allVars e1 ++ allVars e2
allVars (DtIt e1 e2) = allVars e1 ++ allVars e2
allVars (LRec e) = allVars e
allVars (LIt e) = allVars e

freshVariable :: [String] -> String
freshVariable taken =
    head [name
         | name <- map (('y' :) . show) [1::Int ..]
         , name `Set.notMember` Set.fromList taken]
