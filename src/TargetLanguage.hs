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
import           Data.Maybe                (fromMaybe)
import           Data.Monoid               (getSum)
import           Data.Some
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

  LId :: LT a => TTerm env (LFun a a)
  LPair :: (LT a, LT b, LT c)
        => TTerm env (LFun a b)
        -> TTerm env (LFun a c)
        -> TTerm env (LFun a (b, c))
  LFst :: (LT a, LT b) => TTerm env (LFun (a, b) a)
  LSnd :: (LT a, LT b) => TTerm env (LFun (a, b) b)
  LComp :: (LT a, LT b, LT c)
        => TTerm env (LFun a b)
        -> TTerm env (LFun b c)
        -> TTerm env (LFun a c)
  LSingleton :: LT b => TTerm env a -> TTerm env (LFun b (Copower a b))
  LCopowFold :: (LT b, LT c) => TTerm env (a -> LFun b c) -> TTerm env (LFun (Copower a b) c)
  LOp :: LinearOperation' a b c -> TTerm env (a -> LFun b c)

  -- Map derivatives
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
  LinLet :: (LT a, LT s, LT t) => LinTTerm env a s -> LinTTerm env (a, s) t -> LinTTerm env a t
  LinLet' :: (LT a, LT s, LT t) => LinTTerm env a s -> LinTTerm env s t -> LinTTerm env a t
  LinVar :: LT a => LinTTerm env a a
  LinPair :: (LT a, LT s, LT t) => LinTTerm env a s -> LinTTerm env a t -> LinTTerm env a (s, t)
  LinFst :: (LT a, LT s, LT t) => LinTTerm env a (s, t) -> LinTTerm env a s
  LinSnd :: (LT a, LT s, LT t) => LinTTerm env a (s, t) -> LinTTerm env a t
  LinLOp :: LinearOperation' s a t -> TTerm env s -> LinTTerm env a t
  LinZero :: (LT a, LT t) => LinTTerm env a t
  LinPlus :: (LT a, LT t) => LinTTerm env a t -> LinTTerm env a t -> LinTTerm env a t
  LinSingleton :: (LT a, LT t) => TTerm env s -> LinTTerm env a t -> LinTTerm env a (Copower s t)
  LinCopowFold :: (LT a, LT c, LT d) => TTerm env (b -> LFun c d) -> LinTTerm env a (Copower b c) -> LinTTerm env a d

deriving instance Show (LinTTerm env a b)

makeLFunTerm :: LinTTerm env a b -> TTerm env (LFun a b)
makeLFunTerm = \case
  LinApp fun arg -> LComp (makeLFunTerm arg) fun
  LinLet rhs body ->
    LComp (LPair LId (makeLFunTerm rhs)) (makeLFunTerm body)
  LinLet' rhs body ->
    LComp (makeLFunTerm rhs) (makeLFunTerm body)
  LinVar -> LId
  LinPair e1 e2 -> LPair (makeLFunTerm e1) (makeLFunTerm e2)
  LinFst e ->
    LComp (makeLFunTerm e) LFst
  LinSnd e ->
    LComp (makeLFunTerm e) LSnd
  LinLOp lop arg -> LOp lop `App` arg
  LinZero -> Zero
  LinPlus e1 e2 -> AdjPlus (makeLFunTerm e1) (makeLFunTerm e2)
  LinSingleton e1 e2 ->
    LComp (makeLFunTerm e2) (LSingleton e1)
  LinCopowFold fun cp -> LComp (makeLFunTerm cp) (LCopowFold fun)

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
substTt' _ _ _ LId = LId
substTt' i v w (LPair a b) = LPair (substTt' i v w a) (substTt' i v w b)
substTt' _ _ _ LFst = LFst
substTt' _ _ _ LSnd = LSnd
substTt' i v w (LComp a b) = LComp (substTt' i v w a) (substTt' i v w b)
substTt' i v w (LSingleton e) = LSingleton (substTt' i v w e)
substTt' i v w (LCopowFold e) = LCopowFold (substTt' i v w e)
substTt' _ _ _ (LOp lop) = LOp lop

-- | Evaluate the target language
evalTt :: TTerm '[] t -> t
evalTt = evalTt' VZ

-- | Evaluate the target language in the given environment
evalTt' :: Val env -> TTerm env t -> t
evalTt' env (Var i) = valProject env i
evalTt' env (Lambda e) = \v -> evalTt' (VS v env) e
evalTt' env (Let rhs e) = evalTt' (VS (evalTt' env rhs) env) e
evalTt' env (App f a) = evalTt' env f (evalTt' env a)
evalTt' _ Unit = ()
evalTt' env (Pair a b) = (evalTt' env a, evalTt' env b)
evalTt' env (Fst p) = fst $ evalTt' env p
evalTt' env (Snd p) = snd $ evalTt' env p
evalTt' env (Op op a) = evalOp op (evalTt' env a)
evalTt' env (Map a b) = V.map (evalTt' env a) (evalTt' env b)
evalTt' env (AdjPlus a b) = plus (evalTt' env a) (evalTt' env b)
evalTt' _ Zero = zero
evalTt' _ LId = lId
evalTt' env (LPair a b) = lPair (evalTt' env a) (evalTt' env b)
evalTt' _ LFst = lFst
evalTt' _ LSnd = lSnd
evalTt' env (LComp a b) = lComp (evalTt' env a) (evalTt' env b)
evalTt' env (LSingleton e) = singleton (evalTt' env e)
evalTt' env (LCopowFold e) = lCopowFold (evalTt' env e)
evalTt' _ (LOp lop) = evalLOp' lop

sinkTt :: env :> env' -> TTerm env t -> TTerm env' t
sinkTt w (Var i)        = Var (w >:> i)
sinkTt w (Lambda e)    = Lambda (sinkTt (wSink w) e)
sinkTt w (Let rhs e)      = Let (sinkTt w rhs) (sinkTt (wSink w) e)
sinkTt w (App e1 e2)      = App (sinkTt w e1) (sinkTt w e2)
sinkTt _ Unit             = Unit
sinkTt w (Pair a b)       = Pair (sinkTt w a) (sinkTt w b)
sinkTt w (Fst p)          = Fst (sinkTt w p)
sinkTt w (Snd p)          = Snd (sinkTt w p)
sinkTt w (Op op a)      = Op op (sinkTt w a)
sinkTt w (Map a b)        = Map (sinkTt w a) (sinkTt w b)
sinkTt w (AdjPlus a b)    = AdjPlus (sinkTt w a) (sinkTt w b)
sinkTt _ Zero         = Zero
sinkTt _ LId          = LId
sinkTt w (LPair a b)      = LPair (sinkTt w a) (sinkTt w b)
sinkTt _ LFst       = LFst
sinkTt _ LSnd       = LSnd
sinkTt w (LComp a b)      = LComp (sinkTt w a) (sinkTt w b)
sinkTt w (LSingleton e) = LSingleton (sinkTt w e)
sinkTt w (LCopowFold e)   = LCopowFold (sinkTt w e)
sinkTt _ (LOp lop)        = LOp lop

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
printTt d env (Fst p) = showFunction d env "fst" [Some p]
printTt d env (Snd p) = showFunction d env "snd" [Some p]
printTt d env (Op op a) = case (op, a) of
  (Constant x, Unit) -> pure $ showString (show x)
  (EAdd, Pair a1 a2) -> showFunction d env "vecadd" [Some a1, Some a2]
  (EProd, Pair a1 a2) -> showFunction d env "vecprod" [Some a1, Some a2]
  (EScalAdd, Pair a1 a2) -> binary a1 (6, " + ") a2
  (EScalSubt, Pair a1 a2) -> binary a1 (6, " - ") a2
  (EScalProd, Pair a1 a2) -> binary a1 (7, " * ") a2
  (EScalSin, _) -> showFunction d env "sin" [Some a]
  (EScalCos, _) -> showFunction d env "cos" [Some a]
  (Sum, _) -> showFunction d env "vecsum" [Some a]
  (_, _) -> showFunction d env ("evalOp " ++ showOp op) [Some a]
  where
    binary :: TTerm env a -> (Int, String) -> TTerm env b -> State Int ShowS
    binary left (prec, opstr) right = do
      r1 <- printTt (prec + 1) env left
      r2 <- printTt (prec + 1) env right
      pure $ showParen (d > prec) $ r1 . showString opstr . r2
printTt d env (Map a b) = showFunction d env "map" [Some a, Some b]
printTt d env (AdjPlus a b) = showFunction d env "plus" [Some a, Some b]
printTt _ _ Zero = pure $ showString "zero"
printTt _ _ LId = pure $ showString "lid"
printTt d env (LPair a b) = showFunction d env "lpair" [Some a, Some b]
printTt _ _ LFst = pure $ showString "lfst"
printTt _ _ LSnd = pure $ showString "lsnd"
printTt d env (LComp a b) = showFunction d env "lcomp" [Some a, Some b]
printTt d env (LSingleton e) = showFunction d env "lsingleton" [Some e]
printTt d env (LCopowFold e) = showFunction d env "lcopowfold" [Some e]
printTt _ _ (LOp lop) = pure $ showString (showLOp' lop)

showFunction :: Int -> [String] -> String -> [Some (TTerm env)] -> State Int ShowS
showFunction d env funcname args = do
  rs <- mapM (\(Some t) -> (showString " " .) <$> printTt 11 env t) args
  pure $
    showParen (d > 10) $
      showString funcname .
      foldr (.) id rs

prettyTt :: TTerm env a -> String
prettyTt term = evalState (printTt 0 [] term) 1 ""

-- instance Show (TTerm env a) where
--   showsPrec p term = evalState (printLam p [] term) 1

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

-- | Count the uses of a variable in an expression
usesOf :: Idx env t -> TTerm env a -> Integer
usesOf x t = getSum (fold (usesOf' x t))

-- | Count the uses of the components of a variable in an expression
usesOf' :: (Num s, Monoid s) => Idx env t -> TTerm env a -> Layout s
usesOf' i (Var i')
  | Just Refl <- geq i i' = LyLeaf 1
  | otherwise = mempty
usesOf' i (Lambda e) = usesOf' (S i) e
usesOf' i (Let rhs e) = usesOf' i rhs <> usesOf' (S i) e
usesOf' i (App f a) = usesOf' i f <> usesOf' i a
usesOf' _ Unit = mempty
usesOf' i (Pair a b) = usesOf' i a <> usesOf' i b
usesOf' i p@(Fst p') = fromMaybe (usesOf' i p') (usesOfPick i p)
usesOf' i p@(Snd p') = fromMaybe (usesOf' i p') (usesOfPick i p)
usesOf' i (Op _ a) = usesOf' i a
usesOf' i (Map a b) = usesOf' i a <> usesOf' i b
usesOf' i (AdjPlus a b) = usesOf' i a <> usesOf' i b
usesOf' _ Zero = mempty
usesOf' _ LId = mempty
usesOf' i (LPair a b) = usesOf' i a <> usesOf' i b
usesOf' _ LFst = mempty
usesOf' _ LSnd = mempty
usesOf' i (LComp a b) = usesOf' i a <> usesOf' i b
usesOf' i (LSingleton e) = usesOf' i e
usesOf' i (LCopowFold e) = usesOf' i e
usesOf' _ (LOp _) = mempty

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
    increment []              = LyLeaf 1
    increment (PickFst:picks) = LyPair (increment picks) mempty
    increment (PickSnd:picks) = LyPair mempty (increment picks)

data Pick
  = PickFst
  | PickSnd
