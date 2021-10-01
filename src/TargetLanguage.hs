{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeFamilies       #-}
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

  LinFun :: (LT a, LT b) => LinTTerm env '[a] b -> TTerm env (LFun a b)

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
-- of a commutative monoid homomorphism. The domain is the linear environment
-- @lenv@; the codomain is @t@. The linear function also has access to
-- unrestricted variables in the environment @env@ inherited from the
-- surrounding non-linear computation.
data LinTTerm env lenv t where
  LinApp :: (LTenv lenv, LT s, LT t) => TTerm env (LFun s t) -> LinTTerm env lenv s -> LinTTerm env lenv t
  LinLet :: (LTenv lenv, LT s, LT t) => LinTTerm env lenv s -> LinTTerm env (s ': lenv) t -> LinTTerm env lenv t
  LinVar :: LT t => Idx lenv t -> LinTTerm env lenv t
  LinPair :: (LTenv lenv, LT s, LT t) => LinTTerm env lenv s -> LinTTerm env lenv t -> LinTTerm env lenv (s, t)
  LinFst :: (LTenv lenv, LT s, LT t) => LinTTerm env lenv (s, t) -> LinTTerm env lenv s
  LinSnd :: (LTenv lenv, LT s, LT t) => LinTTerm env lenv (s, t) -> LinTTerm env lenv t
  LinLOp :: (LTenv lenv, LT b, LT t) => LinearOperation' s b t -> TTerm env s -> LinTTerm env lenv b -> LinTTerm env lenv t
  LinZero :: (LTenv lenv, LT t) => LinTTerm env lenv t
  LinPlus :: (LTenv lenv, LT t) => LinTTerm env lenv t -> LinTTerm env lenv t -> LinTTerm env lenv t
  LinSingleton :: (LTenv lenv, LT t) => TTerm env s -> LinTTerm env lenv t -> LinTTerm env lenv (Copower s t)
  LinCopowFold :: (LTenv lenv, LT c, LT d) => TTerm env (b -> LFun c d) -> LinTTerm env lenv (Copower b c) -> LinTTerm env lenv d

deriving instance Show (LinTTerm env a b)

type family LTenv lenv where
  LTenv (t ': lenv) = (LT t, LTenv lenv)
  LTenv '[] = ()

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
substLTt' :: Idx env u -> TTerm env' u -> env :> env' -> LinTTerm env lenv b -> LinTTerm env' lenv b
substLTt' i v w (LinApp term f) = LinApp (substTt' i v w term) (substLTt' i v w f)
substLTt' i v w (LinLet f g) = LinLet (substLTt' i v w f) (substLTt' i v w g)
substLTt' _ _ _ (LinVar j) = LinVar j
substLTt' i v w (LinPair f g) = LinPair (substLTt' i v w f) (substLTt' i v w g)
substLTt' i v w (LinFst f) = LinFst (substLTt' i v w f)
substLTt' i v w (LinSnd f) = LinSnd (substLTt' i v w f)
substLTt' i v w (LinLOp op term arg) = LinLOp op (substTt' i v w term) (substLTt' i v w arg)
substLTt' _ _ _ LinZero = LinZero
substLTt' i v w (LinPlus f g) = LinPlus (substLTt' i v w f) (substLTt' i v w g)
substLTt' i v w (LinSingleton term f) = LinSingleton (substTt' i v w term) (substLTt' i v w f)
substLTt' i v w (LinCopowFold term f) = LinCopowFold (substTt' i v w term) (substLTt' i v w f)

-- | Substitute variable with De Bruijn index zero in a 'LinTTerm'
substLinTt :: LTenv lenv' => lenv :> lenv' -> LinTTerm env lenv' u -> LinTTerm env (u ': lenv) t -> LinTTerm env lenv' t
substLinTt w v =
  substLinTt'
    Z
    v
    (Weaken $ \case
       Z -> error "substLinTt: replaced variable should've been replaced"
       S i -> w >:> i)

-- | Substitute given variable with the given environment weakening action in a
-- 'LinTTerm'
substLinTt' :: LTenv lenv' => Idx lenv u -> LinTTerm env lenv' u -> lenv :> lenv' -> LinTTerm env lenv t -> LinTTerm env lenv' t
substLinTt' i v w (LinApp f a) = LinApp f (substLinTt' i v w a)
substLinTt' i v w (LinLet rhs e) =
  LinLet (substLinTt' i v w rhs)
         (substLinTt' (S i) (sinkLinTt (wSucc wId) v) (wSink w) e)
substLinTt' i v w (LinVar i')
  | Just Refl <- geq i i' = v
  | otherwise = LinVar (w >:> i')
substLinTt' i v w (LinPair a b) = LinPair (substLinTt' i v w a) (substLinTt' i v w b)
substLinTt' i v w (LinFst p) = LinFst (substLinTt' i v w p)
substLinTt' i v w (LinSnd p) = LinSnd (substLinTt' i v w p)
substLinTt' i v w (LinLOp op term arg) = LinLOp op term (substLinTt' i v w arg)
substLinTt' _ _ _ LinZero = LinZero
substLinTt' i v w (LinPlus a b) = LinPlus (substLinTt' i v w a) (substLinTt' i v w b)
substLinTt' i v w (LinSingleton term f) = LinSingleton term (substLinTt' i v w f)
substLinTt' i v w (LinCopowFold term f) = LinCopowFold term (substLinTt' i v w f)

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
evalTt' env (LinFun f) = lPair lUnit lId `lComp` evalLTt' env f

type family LinEnvType lenv where
  LinEnvType '[] = ()
  LinEnvType (t ': lenv) = (LinEnvType lenv, t)

-- | Evaluate the linear sublanguage of the target language in the given environment
evalLTt' :: LT (LinEnvType lenv) => Val env -> LinTTerm env lenv b -> LFun (LinEnvType lenv) b
evalLTt' env (LinApp fun arg) = lComp (evalLTt' env arg) (evalTt' env fun)
evalLTt' env (LinLet rhs body) = lComp (lPair lId (evalLTt' env rhs)) (evalLTt' env body)
evalLTt' _   (LinVar j) = makeProj j
  where makeProj :: (LT (LinEnvType lenv), LT t) => Idx lenv t -> LFun (LinEnvType lenv) t
        makeProj Z = lSnd
        makeProj (S i) = lFst `lComp` makeProj i
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
sinkTt w (LinFun f)    = LinFun (sinkTtL w f)

sinkTtL :: env :> env' -> LinTTerm env lenv b -> LinTTerm env' lenv b
sinkTtL w (LinApp term f) = LinApp (sinkTt w term) (sinkTtL w f)
sinkTtL w (LinLet f g) = LinLet (sinkTtL w f) (sinkTtL w g)
sinkTtL _ (LinVar i) = LinVar i
sinkTtL w (LinPair f g) = LinPair (sinkTtL w f) (sinkTtL w g)
sinkTtL w (LinFst f) = LinFst (sinkTtL w f)
sinkTtL w (LinSnd f) = LinSnd (sinkTtL w f)
sinkTtL w (LinLOp op term arg) = LinLOp op (sinkTt w term) (sinkTtL w arg)
sinkTtL _ LinZero = LinZero
sinkTtL w (LinPlus f g) = LinPlus (sinkTtL w f) (sinkTtL w g)
sinkTtL w (LinSingleton term f) = LinSingleton (sinkTt w term) (sinkTtL w f)
sinkTtL w (LinCopowFold term f) = LinCopowFold (sinkTt w term) (sinkTtL w f)

sinkLinTt :: LTenv lenv' =>lenv :> lenv' -> LinTTerm env lenv b -> LinTTerm env lenv' b
sinkLinTt w (LinApp term f) = LinApp term (sinkLinTt w f)
sinkLinTt w (LinLet f g) = LinLet (sinkLinTt w f) (sinkLinTt (wSink w) g)
sinkLinTt w (LinVar i) = LinVar (w >:> i)
sinkLinTt w (LinPair f g) = LinPair (sinkLinTt w f) (sinkLinTt w g)
sinkLinTt w (LinFst f) = LinFst (sinkLinTt w f)
sinkLinTt w (LinSnd f) = LinSnd (sinkLinTt w f)
sinkLinTt w (LinLOp op term arg) = LinLOp op term (sinkLinTt w arg)
sinkLinTt _ LinZero = LinZero
sinkLinTt w (LinPlus f g) = LinPlus (sinkLinTt w f) (sinkLinTt w g)
sinkLinTt w (LinSingleton term f) = LinSingleton term (sinkLinTt w f)
sinkLinTt w (LinCopowFold term f) = LinCopowFold term (sinkLinTt w f)

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
printTt d env (Fst p) = showFunction d env [] "fst" [SomeTTerm p]
printTt d env (Snd p) = showFunction d env [] "snd" [SomeTTerm p]
printTt d env (Op op a) = case (op, a) of
  (Constant x, Unit) -> pure $ showString (show x)
  (EAdd, Pair a1 a2) -> showFunction d env [] "vecadd" [SomeTTerm a1, SomeTTerm a2]
  (EProd, Pair a1 a2) -> showFunction d env [] "vecprod" [SomeTTerm a1, SomeTTerm a2]
  (EScalAdd, Pair a1 a2) -> binary a1 (6, " + ") a2
  (EScalSubt, Pair a1 a2) -> binary a1 (6, " - ") a2
  (EScalProd, Pair a1 a2) -> binary a1 (7, " * ") a2
  (EScalSin, _) -> showFunction d env [] "sin" [SomeTTerm a]
  (EScalCos, _) -> showFunction d env [] "cos" [SomeTTerm a]
  (Sum, _) -> showFunction d env [] "vecsum" [SomeTTerm a]
  (_, _) -> showFunction d env [] ("evalOp " ++ showOp op) [SomeTTerm a]
  where
    binary :: TTerm env a -> (Int, String) -> TTerm env b -> State Int ShowS
    binary left (prec, opstr) right = do
      r1 <- printTt (prec + 1) env left
      r2 <- printTt (prec + 1) env right
      pure $ showParen (d > prec) $ r1 . showString opstr . r2
printTt d env (Map a b) = showFunction d env [] "map" [SomeTTerm a, SomeTTerm b]
printTt d env (AdjPlus a b) = showFunction d env [] "plus" [SomeTTerm a, SomeTTerm b]
printTt _ _ Zero = pure $ showString "zero"
printTt d env (LinFun f) = do
    r1 <- printLTt d env ["v"] f
    pure $ showParen (d > 0) $ showString "\\v -> " . r1

-- | Pretty print the linear sublanguage of the 'TTerm' augmented lambda
-- calculus.
--
-- This recursively calles 'printTt' on the 'TTerm' subterms, and hence
-- inherits precedences from 'printTt'.
printLTt :: Int -> [String] -> [String] -> LinTTerm env lenv b -> State Int ShowS
printLTt d env lenv (LinApp f a) = do
  r1 <- printTt 10 env f
  r2 <- printLTt 11 env lenv a
  pure $ showParen (d > 10) $ r1 . showString " " . r2
printLTt d env lenv (LinLet rhs e) = do
  name <- ('v' :) . show <$> get
  modify (+1)
  r1 <- printLTt 0 env lenv rhs
  r2 <- printLTt 0 env (name : lenv) e
  pure $ showParen (d > 0) $
    showString ("let " ++ name ++ " = ") . r1 . showString " in " . r2
printLTt _ _ lenv (LinVar i) =
  pure $
    case drop (idxToInt i) lenv of
      []  -> showString ("linCtxtVar" ++ show (idxToInt i - length lenv + 1))
      x:_ -> showString x
printLTt _ env lenv (LinPair f g) = do
  r1 <- printLTt 0 env lenv f
  r2 <- printLTt 0 env lenv g
  pure $ showString "(" . r1 . showString ", " . r2 . showString ")"
printLTt d env lenv (LinFst f) = showFunction d env lenv "fst" [SomeLinTTerm f]
printLTt d env lenv (LinSnd f) = showFunction d env lenv "snd" [SomeLinTTerm f]
printLTt d env lenv (LinLOp op term arg) = do
  r1 <- printTt 11 env term
  r2 <- printLTt 11 env lenv arg
  pure $ showParen (d > 10) $
    showString (showLOp' op ++ " ") . r1 . showString " " . r2
printLTt _ _ _ LinZero = pure $ showString "zero"
printLTt d env lenv (LinPlus f g) = showFunction d env lenv "plus" [SomeLinTTerm f, SomeLinTTerm g]
printLTt d env lenv (LinSingleton term f) = showFunction d env lenv "singleton" [SomeTTerm term, SomeLinTTerm f]
printLTt d env lenv (LinCopowFold term f) = showFunction d env lenv "copowfold" [SomeTTerm term, SomeLinTTerm f]

data SomeLinTTerm env =
  forall a b. SomeLinTTerm (LinTTerm env a b)
  | forall a. SomeTTerm (TTerm env a)

showFunction :: Int -> [String] -> [String] -> String -> [SomeLinTTerm env] -> State Int ShowS
showFunction d env lenv funcname args = do
  rs <- mapM (\case SomeLinTTerm t -> (showString " " .) <$> printLTt 11 env lenv t
                    SomeTTerm t -> (showString " " .) <$> printTt 11 env t)
             args
  pure $
    showParen (d > 10) $
      showString funcname .
      foldr (.) id rs

prettyTt :: TTerm env a -> String
prettyTt term = evalState (printTt 0 [] term) 1 ""

prettyLTt :: LinTTerm env lenv b -> String
prettyLTt t = evalState (printLTt 0 [] [] t) 1 ""

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
usesOfL :: (Num s, Monoid s) => Idx env t -> LinTTerm env lenv b -> Layout t s
usesOfL i (LinApp term f) = usesOf' i term <> usesOfL i f
usesOfL i (LinLet f g) = usesOfL i f <> usesOfL i g
usesOfL _ (LinVar _) = mempty
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

getPickLin :: Idx lenv t -> LinTTerm env lenv b -> Maybe (TupPick t b)
getPickLin i (LinVar j) | Just Refl <- geq i j = Just TPHere
getPickLin i (LinFst e) = TPFst <$> getPickLin i e
getPickLin i (LinSnd e) = TPSnd <$> getPickLin i e
getPickLin _ _ = Nothing

layoutFromPick :: (Num s, Monoid s) => TupPick t t' -> Layout t s
layoutFromPick = go (LyLeaf 1)
  where
    go :: (Num s, Monoid s) => Layout t' s -> TupPick t t' -> Layout t s
    go l TPHere = l
    go l (TPFst p) = go (LyPair l mempty) p
    go l (TPSnd p) = go (LyPair mempty l) p

usesOfLinVar :: (Num s, Monoid s) => Idx lenv t -> LinTTerm env lenv b -> Layout t s
usesOfLinVar i (LinApp _ f) = usesOfLinVar i f
usesOfLinVar i (LinLet f g) = usesOfLinVar i f <> usesOfLinVar (S i) g
usesOfLinVar i (LinVar j)
  | Just Refl <- geq i j = LyLeaf 1
  | otherwise = mempty
usesOfLinVar i (LinPair f g) = usesOfLinVar i f <> usesOfLinVar i g
usesOfLinVar i f@(LinFst g) = maybe (usesOfLinVar i g) layoutFromPick (getPickLin i f)
usesOfLinVar i f@(LinSnd g) = maybe (usesOfLinVar i g) layoutFromPick (getPickLin i f)
usesOfLinVar i (LinLOp _ _ arg) = usesOfLinVar i arg
usesOfLinVar _ LinZero = mempty
usesOfLinVar i (LinPlus f g) = usesOfLinVar i f <> usesOfLinVar i g
usesOfLinVar i (LinSingleton _ f) = usesOfLinVar i f
usesOfLinVar i (LinCopowFold _ f) = usesOfLinVar i f
