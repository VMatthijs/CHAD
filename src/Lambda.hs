{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeOperators             #-}

-- | Definition of a lambda calculus. Conflicts heavily with TargetLanguage;
-- don't use the two in the same module unqualified.
module Lambda where

import Data.Foldable      (fold)
import Data.GADT.Compare  (geq)
import Data.Maybe         (fromMaybe)
import Data.Monoid        (Sum (..))
import Data.Some
import GHC.TypeLits

import Data.Type.Equality ((:~:) (Refl))
import Operation          (Operation(..), evalOp, showOp)
import TargetLanguage.Env
import Types (Scal, Copower, Vect)

data Type t where
  TScal :: Type Scal
  TNil :: Type ()
  TPair :: Type a -> Type b -> Type (a, b)
  TEither :: Type a -> Type b -> Type (Either a b)
  TFun :: Type a -> Type b -> Type (a -> b)
  TCopow :: Type a -> Type b -> Type (Copower a b)
  TVect :: KnownNat n => Type (Vect n)

data Lambda env t where
  Var :: Type a -> Idx env a -> Lambda env a
  Lambda :: Type a -> Lambda (a ': env) b -> Lambda env (a -> b)
  App :: Lambda env (a -> b) -> Lambda env a -> Lambda env b
  Unit :: Lambda env ()
  Pair :: Lambda env a -> Lambda env b -> Lambda env (a, b)
  Fst :: Lambda env (a, b) -> Lambda env a
  Snd :: Lambda env (a, b) -> Lambda env b
  Inl :: Type b -> Lambda env a -> Lambda env (Either a b)
  Inr :: Type a -> Lambda env b -> Lambda env (Either a b)
  Case
    :: Lambda env (Either a b)
    -> Lambda env (a -> c)
    -> Lambda env (b -> c)
    -> Lambda env c
  It :: Lambda env ((a, b) -> Either c b) -> Lambda env ((a, b) -> c)
  Op :: Operation a b -> Lambda env a -> Lambda env b

  CopowFold :: Lambda env (a -> b -> c)
            -> Lambda env (Copower a b)
            -> Lambda env c
  Singleton :: Lambda env a -> Lambda env b -> Lambda env (Copower a b)
  AdjPlus :: Lambda env a -> Lambda env a -> Lambda env a

typeof :: Lambda env t -> Type t
typeof (Var t _) = t
typeof (Lambda t e) = TFun t (typeof e)
typeof (App a _) = let TFun _ t = typeof a in t
typeof Unit = TNil
typeof (Pair a b) = TPair (typeof a) (typeof b)
typeof (Fst e) = let TPair t _ = typeof e in t
typeof (Snd e) = let TPair _ t = typeof e in t
typeof (Inl t e) = TEither (typeof e) t
typeof (Inr t e) = TEither t (typeof e)
typeof (Case _ a _) = let TFun _ t = typeof a in t
typeof (It f) = let TFun t1 (TEither t2 _) = typeof f in TFun t1 t2
typeof (Op op _) = typeofOp2 op
typeof (CopowFold f _) = let TFun _ (TFun _ t) = typeof f in t
typeof (Singleton a b) = TCopow (typeof a) (typeof b)
typeof (AdjPlus e _) = typeof e

typeofOp2 :: Operation a b -> Type b
typeofOp2 = \case
  Constant _ -> error "typeof Constant"
  EAdd -> TVect
  EProd -> TVect
  EScalAdd -> TScal
  EScalSubt -> TScal
  EScalProd -> TScal
  Operation.Sum -> TScal

-- | Substitute variable with De Bruijn index zero in a 'TTerm'
substLam :: Lambda env u -> Lambda (u ': env) t -> Lambda env t
substLam v =
  substLam'
    Z
    v
    (Weaken $ \case
       Z -> error "substLam: replaced variable should've been replaced"
       S i -> i)

-- | Substitute given variable with the given environment weakening action in a
-- 'Lambda'
substLam' ::
     Idx env u -> Lambda env' u -> env :> env' -> Lambda env t -> Lambda env' t
substLam' i v w (Var ty i')
  | Just Refl <- geq i i' = v
  | otherwise = Var ty (w >:> i')
substLam' i v w (Lambda ty e) =
  Lambda ty (substLam' (S i) (sinkLam (wSucc wId) v) (wSink w) e)
substLam' i v w (App f a) = App (substLam' i v w f) (substLam' i v w a)
substLam' _ _ _ Unit = Unit
substLam' i v w (Pair a b) = Pair (substLam' i v w a) (substLam' i v w b)
substLam' i v w (Fst p) = Fst (substLam' i v w p)
substLam' i v w (Snd p) = Snd (substLam' i v w p)
substLam' i v w (Inl ty t) = Inl ty (substLam' i v w t)
substLam' i v w (Inr ty t) = Inr ty (substLam' i v w t)
substLam' i v w (Case t l r) =
  Case (substLam' i v w t) (substLam' i v w l) (substLam' i v w r)
substLam' i v w (It t) = It (substLam' i v w t)
substLam' i v w (Op op y) = Op op (substLam' i v w y)
substLam' i v w (CopowFold a b) = CopowFold (substLam' i v w a) (substLam' i v w b)
substLam' i v w (Singleton a b) = Singleton (substLam' i v w a) (substLam' i v w b)
substLam' i v w (AdjPlus a b) = AdjPlus (substLam' i v w a) (substLam' i v w b)

-- | Evaluate the target language
evalLam :: Lambda '[] t -> t
evalLam = evalLam' VZ

-- | Evaluate the target language in the given environment
evalLam' :: Val env -> Lambda env t -> t
-- Source language extension
evalLam' env (Var _ i) = valProject env i
evalLam' env (Lambda _ e) = \v -> evalLam' (VS v env) e
evalLam' env (App f a) = evalLam' env f (evalLam' env a)
evalLam' _ Unit = ()
evalLam' env (Pair a b) = (evalLam' env a, evalLam' env b)
evalLam' env (Fst p) = fst $ evalLam' env p
evalLam' env (Snd p) = snd $ evalLam' env p
evalLam' env (Inl _ p) = Left $ evalLam' env p
evalLam' env (Inr _ p) = Right $ evalLam' env p
evalLam' env (Case p l r) =
  case evalLam' env p of
    Left q  -> evalLam' env l q
    Right q -> evalLam' env r q
evalLam' env (Op op a) = evalOp op (evalLam' env a)
evalLam' env (It t) = fix (evalLam' env t)
  where
    fix f (a, b) =
      case f (a, b) of
        Left c   -> c
        Right b' -> fix f (a, b')

sinkLam :: env :> env' -> Lambda env t -> Lambda env' t
sinkLam w (Var t i)       = Var t (w >:> i)
sinkLam w (Lambda ty e)   = Lambda ty (sinkLam (wSink w) e)
sinkLam w (App e1 e2)     = App (sinkLam w e1) (sinkLam w e2)
sinkLam _ Unit            = Unit
sinkLam w (Pair a b)      = Pair (sinkLam w a) (sinkLam w b)
sinkLam w (Fst p)         = Fst (sinkLam w p)
sinkLam w (Snd p)         = Snd (sinkLam w p)
sinkLam w (Inl ty p)      = Inl ty (sinkLam w p)
sinkLam w (Inr ty p)      = Inr ty (sinkLam w p)
sinkLam w (Case p g h)    = Case (sinkLam w p) (sinkLam w g) (sinkLam w h)
sinkLam w (Op op a)       = Op op (sinkLam w a)
sinkLam w (It s)          = It (sinkLam w s)
sinkLam w (CopowFold a b) = CopowFold (sinkLam w a) (sinkLam w b)
sinkLam w (Singleton a b) = Singleton (sinkLam w a) (sinkLam w b)
sinkLam w (AdjPlus a b)   = AdjPlus (sinkLam w a) (sinkLam w b)

data PrintEnv =
  PrintEnv Int [String]

-- | Pretty print the target language
--
-- Precedences used are as follows:
-- - application is 10
-- - plus is 6
-- - linear composition (;;) is 1
printLam :: Int -> PrintEnv -> Lambda env t -> ShowS
-- Source language extension
printLam _ (PrintEnv _ stack) (Var _ i) =
  case drop (idxToInt i) stack of
    []  -> showString ("ctxtVar" ++ show (idxToInt i - length stack + 1))
    x:_ -> showString x
printLam d (PrintEnv depth stack) (Lambda _ e) =
  let name = 'x' : show (depth + 1)
   in showParen (d > 0) $
      showString ("\\" ++ name ++ " -> ") .
      printLam 0 (PrintEnv (depth + 1) (name : stack)) e
printLam d env (App f a) =
  showParen (d > 10) $ printLam 10 env f . showString " " . printLam 11 env a
printLam _ _ Unit = showString "()"
printLam _ env (Pair a b) =
  showString "(" .
  printLam 0 env a . showString ", " . printLam 0 env b . showString ")"
printLam d env (Fst p) = showFunction d env "Fst" [Some p]
printLam d env (Snd p) = showFunction d env "Snd" [Some p]
printLam d env (Inl _ p) = showFunction d env "Inl" [Some p]
printLam d env (Inr _ p) = showFunction d env "Inr" [Some p]
printLam d env (Case p l r) =
  showParen (d > 0) $
  showString "Case " .
  printLam 0 env p .
  showString " in {" .
  printLam 0 env l . showString " } { " . printLam 0 env r . showString "}"
printLam d env (Op op a) = showFunction d env ("evalOp " ++ showOp op) [Some a]
printLam d env (It t) = showFunction d env "it" [Some t]
printLam d env (CopowFold a b) = showFunction d env "copowfold" [Some a, Some b]
printLam d env (Singleton a b) = showFunction d env "singleton" [Some a, Some b]
printLam d env (AdjPlus a b) = showFunction d env "adjplus" [Some a, Some b]

data SomeTTerm =
  forall env t. SomeTTerm (Lambda env t)

showFunction :: Int -> PrintEnv -> String -> [Some (Lambda env)] -> ShowS
showFunction d env funcname args =
  showParen (d > 10) $
  showString funcname .
  foldr (\(Some t) -> (.) (showString " " . printLam 11 env t)) id args

instance Show (Lambda env a) where
  showsPrec p = printLam p (PrintEnv 0 [])

data Layout a
  = LyLeaf a
  | LyPair (Layout a) (Layout a)
  deriving (Show)

instance Functor Layout where
  fmap f (LyLeaf x)     = LyLeaf (f x)
  fmap f (LyPair l1 l2) = LyPair (fmap f l1) (fmap f l2)

instance Foldable Layout where
  foldMap f (LyLeaf x)     = f x
  foldMap f (LyPair l1 l2) = foldMap f l1 <> foldMap f l2

instance Semigroup a => Semigroup (Layout a) where
  LyLeaf a <> LyLeaf b = LyLeaf (a <> b)
  l@(LyLeaf _) <> LyPair l1 l2 = LyPair (l <> l1) (l <> l2)
  LyPair l1 l2 <> l@(LyLeaf _) = LyPair (l1 <> l) (l2 <> l)
  LyPair l1 l2 <> LyPair l3 l4 = LyPair (l1 <> l3) (l2 <> l4)

instance Monoid a => Monoid (Layout a) where
  mempty = LyLeaf mempty

-- Monoid is strictly speaking not necessary here with a more careful implementation
truncateLayoutWithExpr :: Monoid s => Layout s -> Lambda env a -> Layout s
truncateLayoutWithExpr l@(LyLeaf _) _ = l
truncateLayoutWithExpr (LyPair l1 l2) (Pair e1 e2) =
  LyPair (truncateLayoutWithExpr l1 e1) (truncateLayoutWithExpr l2 e2)
truncateLayoutWithExpr l@(LyPair _ _) _ = LyLeaf (fold l)

-- | Count the uses of a variable in an expression
usesOf :: Idx env t -> Lambda env a -> Integer
usesOf x t = getSum (fold (usesOf' x t))

-- | Count the uses of the components of a variable in an expression
usesOf' :: (Num s, Monoid s) => Idx env t -> Lambda env a -> Layout s
usesOf' i (Var _ i')
  | Just Refl <- geq i i' = LyLeaf 1
  | otherwise = mempty
usesOf' i (Lambda _ e) = usesOf' (S i) e
usesOf' i (App f a) = usesOf' i f <> usesOf' i a
usesOf' _ Unit = mempty
usesOf' i (Pair a b) = usesOf' i a <> usesOf' i b
usesOf' i p@(Fst p') = fromMaybe (usesOf' i p') (usesOfPick i p)
usesOf' i p@(Snd p') = fromMaybe (usesOf' i p') (usesOfPick i p)
usesOf' i (Inl _ p) = usesOf' i p
usesOf' i (Inr _ p) = usesOf' i p
usesOf' i (Case p f g) = usesOf' i p <> usesOf' i f <> usesOf' i g
usesOf' i (Op _ a) = usesOf' i a
usesOf' i (It s) = usesOf' i s
usesOf' i (CopowFold a b) = usesOf' i a <> usesOf' i b
usesOf' i (Singleton a b) = usesOf' i a <> usesOf' i b
usesOf' i (AdjPlus a b) = usesOf' i a <> usesOf' i b

usesOfPick :: (Num s, Monoid s) => Idx env t -> Lambda env a -> Maybe (Layout s)
usesOfPick i term = do
  path <- getPath i term
  return (increment (reverse path))
  where
    getPath :: Idx env t -> Lambda env a -> Maybe [Pick]
    getPath j (Fst p) = (PickFst :) <$> getPath j p
    getPath j (Snd p) = (PickSnd :) <$> getPath j p
    getPath j (Var _ j')
      | Just Refl <- geq j j' = Just []
    getPath _ _ = Nothing
    increment :: (Num s, Monoid s) => [Pick] -> Layout s
    increment []              = LyLeaf 1
    increment (PickFst:picks) = LyPair (increment picks) mempty
    increment (PickSnd:picks) = LyPair mempty (increment picks)

data Pick
  = PickFst
  | PickSnd
