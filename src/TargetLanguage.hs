{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeOperators      #-}

-- | Definition of the target language
module TargetLanguage where

import           Control.Monad.State.Strict
import           Data.Foldable             (fold)
import           Data.GADT.Compare         (GEq (..))
import           Data.List                 (intersperse)
import           Data.Monoid               (getSum)
import           Data.Type.Equality        ((:~:) (Refl))
import qualified Data.Vector.Unboxed.Sized as V (map)
import           GHC.TypeNats              (KnownNat)

import           Env
import           Operation
import           Types

-- | Terms of the target language
data TTerm env t where
  Var :: Idx env a -> TTerm env a
  Lambda :: TTerm (a ': env) b -> TTerm env (a -> b)
  Let :: TTerm env a -> TTerm (a ': env) b -> TTerm env b
  App :: TTerm env (a -> b) -> TTerm env a -> TTerm env b
  Unit :: TTerm env ()
  Pair :: TTerm env a -> TTerm env b -> TTerm env (a, b)
  Fst :: TTerm env (a, b) -> TTerm env a
  Snd :: TTerm env (a, b) -> TTerm env b
  Op :: Operation a b -> TTerm env a -> TTerm env b

  Map :: KnownNat n => TTerm env (Scal -> Scal) -> TTerm env (Vect n) -> TTerm env (Vect n)

  AdjPlus :: LT a => TTerm env a -> TTerm env a -> TTerm env a
  Zero :: LT a => TTerm env a

  LinFun :: LinTTerm env a b -> TTerm env (LFun a b)

  -- DMap
  --   :: KnownNat n
  --   => TTerm env (Scal -> (Scal, LFun Scal Scal))
  --   -> TTerm env (Vect n)
  --   -> TTerm env (LFun (Scal -> Scal, Vect n) (Vect n))
  -- DtMap
  --   :: KnownNat n
  --   => TTerm env (Scal -> (Scal, LFun Scal Scal))
  --   -> TTerm env (Vect n)
  --   -> TTerm env (LFun (Vect n) (Copower Scal Scal, Vect n))
  -- DFoldr
  --   :: (KnownNat n, V.Unbox a, V.Unbox b, LT b)
  --   => TTerm env ((Scal, a) -> (a, LFun (Scal, b) b))
  --   -> TTerm env a
  --   -> TTerm env (Vect n)
  --   -> TTerm env (LFun (((Scal, a) -> b, b), Vect n) b)
  -- DtFoldr
  --   :: (KnownNat n, V.Unbox a, V.Unbox b, LT b)
  --   => TTerm env ((Scal, a) -> (a, LFun b (Scal, b)))
  --   -> TTerm env a
  --   -> TTerm env (Vect n)
  --   -> TTerm env (LFun b ((Copower (Scal, a) b, b), Vect n))

deriving instance Show (TTerm env a)

-- | A sort-of pointful language that encodes a linear function, in the sense
-- of a commutative monoid homomorphism. Compile this to linear combinators
-- using 'makeLFunTerm'.
data LinTTerm env a t where
  LinApp :: (LT a, LT s, LT t) => TTerm env (LFun s t) -> LinTTerm env a s -> LinTTerm env a t
  LinLet :: (LT a, LT s, LT t) => LinTTerm env a s -> LinTTerm env s t -> LinTTerm env a t
  LinVar :: LT a => LinTTerm env a a
  LinPair :: (LT a, LT s, LT t) => LinTTerm env a s -> LinTTerm env a t -> LinTTerm env a (s, t)
  LinFst :: (LT a, LT s, LT t) => LinTTerm env a (s, t) -> LinTTerm env a s
  LinSnd :: (LT a, LT s, LT t) => LinTTerm env a (s, t) -> LinTTerm env a t
  LinLOp :: (LT a, LT b, LT t) => LinearOperation' s b t -> TTerm env s -> LinTTerm env a b -> LinTTerm env a t
  LinZero :: (LT a, LT t) => LinTTerm env a t
  LinPlus :: (LT a, LT t) => LinTTerm env a t -> LinTTerm env a t -> LinTTerm env a t
  LinSingleton :: (LT a, LT t) => TTerm env s -> LinTTerm env a t -> LinTTerm env a (Copower s t)
  LinCopowFold :: (LT a, LT c, LT d) => TTerm env (b -> LFun c d) -> LinTTerm env a (Copower b c) -> LinTTerm env a d

deriving instance Show (LinTTerm env a b)

-- | Substitute variable with De Bruijn index zero in a 'TTerm'
substTt :: env :> env' -> TTerm env' u -> TTerm (u ': env) t -> TTerm env' t
substTt w v =
  substTt'
    Z
    v
    (Weaken $ \case
       Z -> error "substTt: replaced variable should've been replaced"
       S i -> w >:> i)

-- | Substitute given variable with the given environment weakening action in a
-- 'TTerm'
substTt' :: Idx env u -> TTerm env' u -> env :> env' -> TTerm env t -> TTerm env' t
substTt' i v w (Var i')
  | Just Refl <- geq i i' = v
  | otherwise = Var (w >:> i')
substTt' i v w (Lambda e) =
  Lambda (substTt' (S i) (sinkTt (wSucc wId) v) (wSink w) e)
substTt' i v w (Let rhs e) =
  Let (substTt' i v w rhs)
      (substTt' (S i) (sinkTt (wSucc wId) v) (wSink w) e)
substTt' i v w (App f a) = App (substTt' i v w f) (substTt' i v w a)
substTt' _ _ _ Unit = Unit
substTt' i v w (Pair a b) = Pair (substTt' i v w a) (substTt' i v w b)
substTt' i v w (Fst p) = Fst (substTt' i v w p)
substTt' i v w (Snd p) = Snd (substTt' i v w p)
substTt' i v w (Op op y) = Op op (substTt' i v w y)
substTt' i v w (Map a b) = Map (substTt' i v w a) (substTt' i v w b)
substTt' i v w (AdjPlus a b) = AdjPlus (substTt' i v w a) (substTt' i v w b)
substTt' _ _ _ Zero = Zero
substTt' i v w (LinFun f) = LinFun (substLTt' i v w f)

-- | Substitute given variable with the given environment weakening action in a
-- 'LinTTerm'
substLTt' :: Idx env u -> TTerm env' u -> env :> env' -> LinTTerm env a b -> LinTTerm env' a b
substLTt' i v w (LinApp term f) = LinApp (substTt' i v w term) (substLTt' i v w f)
substLTt' i v w (LinLet f g) = LinLet (substLTt' i v w f) (substLTt' i v w g)
substLTt' _ _ _ LinVar = LinVar
substLTt' i v w (LinPair f g) = LinPair (substLTt' i v w f) (substLTt' i v w g)
substLTt' i v w (LinFst f) = LinFst (substLTt' i v w f)
substLTt' i v w (LinSnd f) = LinSnd (substLTt' i v w f)
substLTt' i v w (LinLOp op term arg) = LinLOp op (substTt' i v w term) (substLTt' i v w arg)
substLTt' _ _ _ LinZero = LinZero
substLTt' i v w (LinPlus f g) = LinPlus (substLTt' i v w f) (substLTt' i v w g)
substLTt' i v w (LinSingleton term f) = LinSingleton (substTt' i v w term) (substLTt' i v w f)
substLTt' i v w (LinCopowFold term f) = LinCopowFold (substTt' i v w term) (substLTt' i v w f)

substLinVar :: (LT a, LT s, LT t) => LinTTerm env a s -> LinTTerm env s t -> LinTTerm env a t
substLinVar r (LinApp term f) = LinApp term (substLinVar r f)
substLinVar r (LinLet f g) = LinLet (substLinVar r f) g
substLinVar r LinVar = r
substLinVar r (LinPair f g) = LinPair (substLinVar r f) (substLinVar r g)
substLinVar r (LinFst f) = LinFst (substLinVar r f)
substLinVar r (LinSnd f) = LinSnd (substLinVar r f)
substLinVar r (LinLOp op term arg) = LinLOp op term (substLinVar r arg)
substLinVar _ LinZero = LinZero
substLinVar r (LinPlus f g) = LinPlus (substLinVar r f) (substLinVar r g)
substLinVar r (LinSingleton term f) = LinSingleton term (substLinVar r f)
substLinVar r (LinCopowFold term f) = LinCopowFold term (substLinVar r f)

-- | Evaluate the target language
evalTt :: TTerm '[] t -> t
evalTt = evalTt' VZ

-- | Evaluate the target language in the given environment
evalTt' :: Val env -> TTerm env t -> t
evalTt' env (Var i) = valProject env i
evalTt' env (Lambda e) = \v -> evalTt' (VS v env) e
evalTt' env (Let rhs e) = evalTt' (VS (evalTt' env rhs) env) e
evalTt' env (App f a) = evalTt' env f (evalTt' env a)
evalTt' _   Unit = ()
evalTt' env (Pair a b) = (evalTt' env a, evalTt' env b)
evalTt' env (Fst p) = fst $ evalTt' env p
evalTt' env (Snd p) = snd $ evalTt' env p
evalTt' env (Op op a) = evalOp op (evalTt' env a)
evalTt' env (Map a b) = V.map (evalTt' env a) (evalTt' env b)
evalTt' env (AdjPlus a b) = plus (evalTt' env a) (evalTt' env b)
evalTt' _   Zero = zero
evalTt' env (LinFun f) = evalLTt' env f

-- | Evaluate the linear sublanguage of the target language in the given environment
evalLTt' :: Val env -> LinTTerm env a b -> LFun a b
evalLTt' env (LinApp fun arg) = lComp (evalLTt' env arg) (evalTt' env fun)
evalLTt' env (LinLet rhs body) = lComp (evalLTt' env rhs) (evalLTt' env body)
evalLTt' _   LinVar = lId
evalLTt' env (LinPair e1 e2) = lPair (evalLTt' env e1) (evalLTt' env e2)
evalLTt' env (LinFst e) = lComp (evalLTt' env e) lFst
evalLTt' env (LinSnd e) = lComp (evalLTt' env e) lSnd
evalLTt' env (LinLOp lop term arg) = evalLTt' env arg `lComp` evalLOp' lop (evalTt' env term)
evalLTt' _   LinZero = zero
evalLTt' env (LinPlus e1 e2) = plus (evalLTt' env e1) (evalLTt' env e2)
evalLTt' env (LinSingleton e1 e2) = lComp (evalLTt' env e2) (singleton (evalTt' env e1))
evalLTt' env (LinCopowFold fun cp) = lComp (evalLTt' env cp) (lCopowFold (evalTt' env fun))

sinkTt :: env :> env' -> TTerm env t -> TTerm env' t
sinkTt w (Var i)       = Var (w >:> i)
sinkTt w (Lambda e)    = Lambda (sinkTt (wSink w) e)
sinkTt w (Let rhs e)   = Let (sinkTt w rhs) (sinkTt (wSink w) e)
sinkTt w (App e1 e2)   = App (sinkTt w e1) (sinkTt w e2)
sinkTt _ Unit          = Unit
sinkTt w (Pair a b)    = Pair (sinkTt w a) (sinkTt w b)
sinkTt w (Fst p)       = Fst (sinkTt w p)
sinkTt w (Snd p)       = Snd (sinkTt w p)
sinkTt w (Op op a)     = Op op (sinkTt w a)
sinkTt w (Map a b)     = Map (sinkTt w a) (sinkTt w b)
sinkTt w (AdjPlus a b) = AdjPlus (sinkTt w a) (sinkTt w b)
sinkTt _ Zero          = Zero
sinkTt w (LinFun f)    = LinFun (sinkLTt w f)

sinkLTt :: env :> env' -> LinTTerm env a b -> LinTTerm env' a b
sinkLTt w (LinApp term f) = LinApp (sinkTt w term) (sinkLTt w f)
sinkLTt w (LinLet f g) = LinLet (sinkLTt w f) (sinkLTt w g)
sinkLTt _ LinVar = LinVar
sinkLTt w (LinPair f g) = LinPair (sinkLTt w f) (sinkLTt w g)
sinkLTt w (LinFst f) = LinFst (sinkLTt w f)
sinkLTt w (LinSnd f) = LinSnd (sinkLTt w f)
sinkLTt w (LinLOp op term arg) = LinLOp op (sinkTt w term) (sinkLTt w arg)
sinkLTt _ LinZero = LinZero
sinkLTt w (LinPlus f g) = LinPlus (sinkLTt w f) (sinkLTt w g)
sinkLTt w (LinSingleton term f) = LinSingleton (sinkTt w term) (sinkLTt w f)
sinkLTt w (LinCopowFold term f) = LinCopowFold (sinkTt w term) (sinkLTt w f)

-- | Pretty print the augmented lambda calculus in 'TTerm'
--
-- Precedences used are as in Haskell.
printTt :: Int -> [String] -> TTerm env t -> State Int ShowS
printTt _ env (Var i) =
  pure $
    case drop (idxToInt i) env of
      []  -> showString ("ctxtVar" ++ show (idxToInt i - length env + 1))
      x:_ -> showString x
printTt d env (Lambda e) = do
  name <- ('x' :) . show <$> get
  modify (+1)
  r <- printTt 0 (name : env) e
  pure $ showParen (d > 0) $ showString ("\\" ++ name ++ " -> ") . r
printTt d env topexpr@Let{} = do
  let collect :: [String] -> TTerm env a -> State Int ([(String, ShowS)], ShowS)
      collect env' (Let rhs e) = do
        name <- ('x' :) . show <$> get
        modify (+1)
        r1 <- printTt 0 env' rhs
        (rest, core) <- collect (name : env') e
        return ((name, r1) : rest, core)
      collect env' e = ([],) <$> printTt 0 env' e
  (pairs, core) <- collect env topexpr
  pure $ showParen (d > 0) $
    showString "let "
    . foldr (.) id (intersperse (showString " ; ")
                        [showString (lhs ++ " = ") . rhs | (lhs, rhs) <- pairs])
    . showString " in " . core
printTt d env (App f a) = do
  r1 <- printTt 10 env f
  r2 <- printTt 11 env a
  pure $ showParen (d > 10) $ r1 . showString " " . r2
printTt _ _ Unit = pure (showString "()")
printTt _ env (Pair a b) = do
  r1 <- printTt 0 env a
  r2 <- printTt 0 env b
  pure $ showString "(" . r1 . showString ", " . r2 . showString ")"
printTt d env (Fst p) = showFunction d env "fst" [SomeTTerm p]
printTt d env (Snd p) = showFunction d env "snd" [SomeTTerm p]
printTt d env (Op op a) = case (op, a) of
  (Constant x, Unit) -> pure $ showString (show x)
  (EAdd, Pair a1 a2) -> showFunction d env "vecadd" [SomeTTerm a1, SomeTTerm a2]
  (EProd, Pair a1 a2) -> showFunction d env "vecprod" [SomeTTerm a1, SomeTTerm a2]
  (EScalAdd, Pair a1 a2) -> binary a1 (6, " + ") a2
  (EScalSubt, Pair a1 a2) -> binary a1 (6, " - ") a2
  (EScalProd, Pair a1 a2) -> binary a1 (7, " * ") a2
  (EScalSin, _) -> showFunction d env "sin" [SomeTTerm a]
  (EScalCos, _) -> showFunction d env "cos" [SomeTTerm a]
  (Sum, _) -> showFunction d env "vecsum" [SomeTTerm a]
  (_, _) -> showFunction d env ("evalOp " ++ showOp op) [SomeTTerm a]
  where
    binary :: TTerm env a -> (Int, String) -> TTerm env b -> State Int ShowS
    binary left (prec, opstr) right = do
      r1 <- printTt (prec + 1) env left
      r2 <- printTt (prec + 1) env right
      pure $ showParen (d > prec) $ r1 . showString opstr . r2
printTt d env (Map a b) = showFunction d env "map" [SomeTTerm a, SomeTTerm b]
printTt d env (AdjPlus a b) = showFunction d env "plus" [SomeTTerm a, SomeTTerm b]
printTt _ _ Zero = pure $ showString "zero"
printTt d env (LinFun f) = do
    r1 <- printLTt d env f
    pure $ showParen (d > 0) $ showString "\\v -> " . r1

-- | Pretty print the linear sublanguage of the 'TTerm' augmented lambda
-- calculus. This assumes that the linear variable in scope is called 'v'.
--
-- This recursively calles 'printTt' on the 'TTerm' subterms, and hence
-- inherits precedences from 'printTt'.
printLTt :: Int -> [String] -> LinTTerm env a b -> State Int ShowS
printLTt d env (LinApp f a) = do
  r1 <- printTt 10 env f
  r2 <- printLTt 11 env a
  pure $ showParen (d > 10) $ r1 . showString " " . r2
printLTt d env (LinLet rhs e) = do
  r1 <- printLTt 0 env rhs
  r2 <- printLTt 0 env e
  pure $ showParen (d > 0) $
    showString "let v = " . r1 . showString " in " . r2
printLTt _ _ LinVar = pure $ showString "v"
printLTt _ env (LinPair f g) = do
  r1 <- printLTt 0 env f
  r2 <- printLTt 0 env g
  pure $ showString "(" . r1 . showString ", " . r2 . showString ")"
printLTt d env (LinFst f) = showFunction d env "fst" [SomeLinTTerm f]
printLTt d env (LinSnd f) = showFunction d env "snd" [SomeLinTTerm f]
printLTt d env (LinLOp op term arg) = do
  r1 <- printTt 11 env term
  r2 <- printLTt 11 env arg
  pure $ showParen (d > 10) $
    showString (showLOp' op ++ " ") . r1 . showString " " . r2
printLTt _ _ LinZero = pure $ showString "zero"
printLTt d env (LinPlus f g) = showFunction d env "plus" [SomeLinTTerm f, SomeLinTTerm g]
printLTt d env (LinSingleton term f) = showFunction d env "singleton" [SomeTTerm term, SomeLinTTerm f]
printLTt d env (LinCopowFold term f) = showFunction d env "copowfold" [SomeTTerm term, SomeLinTTerm f]

data SomeLinTTerm env =
  forall a b. SomeLinTTerm (LinTTerm env a b)
  | forall a. SomeTTerm (TTerm env a)

showFunction :: Int -> [String] -> String -> [SomeLinTTerm env] -> State Int ShowS
showFunction d env funcname args = do
  rs <- mapM (\case SomeLinTTerm t -> (showString " " .) <$> printLTt 11 env t
                    SomeTTerm t -> (showString " " .) <$> printTt 11 env t)
             args
  pure $
    showParen (d > 10) $
      showString funcname .
      foldr (.) id rs

prettyTt :: TTerm env a -> String
prettyTt term = evalState (printTt 0 [] term) 1 ""

prettyLTt :: LinTTerm env a b -> String
prettyLTt t = evalState (printLTt 0 [] t) 1 ""

-- instance Show (TTerm env a) where
--   showsPrec p term = evalState (printLam p [] term) 1

data Layout t a where
  LyLeaf :: a -> Layout t a
  LyPair :: Layout t1 a -> Layout t2 a -> Layout (t1, t2) a
deriving instance Show a => Show (Layout t a)

instance Functor (Layout t) where
  fmap f (LyLeaf x)     = LyLeaf (f x)
  fmap f (LyPair l1 l2) = LyPair (fmap f l1) (fmap f l2)

instance Foldable (Layout t) where
  foldMap f (LyLeaf x)     = f x
  foldMap f (LyPair l1 l2) = foldMap f l1 <> foldMap f l2

instance Semigroup a => Semigroup (Layout t a) where
  LyLeaf a <> LyLeaf b = LyLeaf (a <> b)
  LyLeaf n <> LyPair l1 l2 = LyPair (fmap (n <>) l1) (fmap (n <>) l2)
  LyPair l1 l2 <> LyLeaf n = LyPair (fmap (<> n) l1) (fmap (<> n) l2)
  LyPair l1 l2 <> LyPair l3 l4 = LyPair (l1 <> l3) (l2 <> l4)

instance Monoid a => Monoid (Layout t a) where
  mempty = LyLeaf mempty

-- | Count the uses of a variable in an expression
usesOf :: Idx env t -> TTerm env a -> Integer
usesOf x t = getSum (fold (usesOf' x t))

-- | Count the uses of the components of a variable in an expression
usesOf' :: (Num s, Monoid s) => Idx env t -> TTerm env a -> Layout t s
usesOf' i (Var i')
  | Just Refl <- geq i i' = LyLeaf 1
  | otherwise = mempty
usesOf' i (Lambda e) = usesOf' (S i) e
usesOf' i (Let rhs e) = usesOf' i rhs <> usesOf' (S i) e
usesOf' i (App f a) = usesOf' i f <> usesOf' i a
usesOf' _ Unit = mempty
usesOf' i (Pair a b) = usesOf' i a <> usesOf' i b
usesOf' i p@(Fst p') = maybe (usesOf' i p') layoutFromPick (getPick i p)
usesOf' i p@(Snd p') = maybe (usesOf' i p') layoutFromPick (getPick i p)
usesOf' i (Op _ a) = usesOf' i a
usesOf' i (Map a b) = usesOf' i a <> usesOf' i b
usesOf' i (AdjPlus a b) = usesOf' i a <> usesOf' i b
usesOf' _ Zero = mempty
usesOf' i (LinFun f) = usesOfL i f

-- | Count the uses of the components of a variable in an expression in the linear sublanguage of the target language
usesOfL :: (Num s, Monoid s) => Idx env t -> LinTTerm env a b -> Layout t s
usesOfL i (LinApp term f) = usesOf' i term <> usesOfL i f
usesOfL i (LinLet f g) = usesOfL i f <> usesOfL i g
usesOfL _ LinVar = mempty
usesOfL i (LinPair f g) = usesOfL i f <> usesOfL i g
usesOfL i (LinFst f) = usesOfL i f
usesOfL i (LinSnd f) = usesOfL i f
usesOfL i (LinLOp _ term arg) = usesOf' i term <> usesOfL i arg
usesOfL _ LinZero = mempty
usesOfL i (LinPlus f g) = usesOfL i f <> usesOfL i g
usesOfL i (LinSingleton term f) = usesOf' i term <> usesOfL i f
usesOfL i (LinCopowFold term f) = usesOf' i term <> usesOfL i f

data TupPick large small where
  TPHere :: TupPick t t
  TPFst :: TupPick t (a, b) -> TupPick t a
  TPSnd :: TupPick t (a, b) -> TupPick t b

getPick :: Idx env t -> TTerm env a -> Maybe (TupPick t a)
getPick i (Var j) | Just Refl <- geq i j = Just TPHere
getPick i (Fst e) = TPFst <$> getPick i e
getPick i (Snd e) = TPSnd <$> getPick i e
getPick _ _ = Nothing

getPickLin :: LinTTerm env a b -> Maybe (TupPick a b)
getPickLin LinVar = Just TPHere
getPickLin (LinFst e) = TPFst <$> getPickLin e
getPickLin (LinSnd e) = TPSnd <$> getPickLin e
getPickLin _ = Nothing

layoutFromPick :: (Num s, Monoid s) => TupPick t t' -> Layout t s
layoutFromPick = go (LyLeaf 1)
  where
    go :: (Num s, Monoid s) => Layout t' s -> TupPick t t' -> Layout t s
    go l TPHere = l
    go l (TPFst p) = go (LyPair l mempty) p
    go l (TPSnd p) = go (LyPair mempty l) p

usesOfLinVar :: (Num s, Monoid s) => LinTTerm env a b -> Layout a s
usesOfLinVar (LinApp _ f) = usesOfLinVar f
usesOfLinVar (LinLet f _) = usesOfLinVar f
usesOfLinVar LinVar = LyLeaf 1
usesOfLinVar (LinPair f g) = usesOfLinVar f <> usesOfLinVar g
usesOfLinVar f@(LinFst g) = maybe (usesOfLinVar g) layoutFromPick (getPickLin f)
usesOfLinVar f@(LinSnd g) = maybe (usesOfLinVar g) layoutFromPick (getPickLin f)
usesOfLinVar (LinLOp _ _ arg) = usesOfLinVar arg
usesOfLinVar LinZero = mempty
usesOfLinVar (LinPlus f g) = usesOfLinVar f <> usesOfLinVar g
usesOfLinVar (LinSingleton _ f) = usesOfLinVar f
usesOfLinVar (LinCopowFold _ f) = usesOfLinVar f
