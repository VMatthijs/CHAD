{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

-- | Definition of a lambda calculus. Conflicts heavily with TargetLanguage;
-- don't use the two in the same module unqualified.
module Lambda where

import Control.Monad.State.Strict
import Data.Foldable      (fold)
import Data.GADT.Compare  (GEq(..))
import Data.Maybe         (fromMaybe)
import Data.Monoid        (Sum (..))
import Data.Proxy
import Data.Some
import GHC.TypeLits

import Data.Type.Equality ((:~:) (Refl))
import Operation          (Operation(..), LinearOperation'(..), evalOp, showOp, showLOp', evalLOp')
import TargetLanguage.Env
import Types

data Type t where
  TScal :: Type Scal
  TNil :: Type ()
  TPair :: Type a -> Type b -> Type (a, b)
  TFun :: Type a -> Type b -> Type (a -> b)
  TLFun :: Type a -> Type b -> Type (LFun a b)
  TCopow :: Type a -> Type b -> Type (Copower a b)
  TVect :: KnownNat n => Type (Vect n)

deriving instance Show (Type t)

data Lambda env t where
  Var :: Type a -> Idx env a -> Lambda env a
  Lambda :: Type a -> Lambda (a ': env) b -> Lambda env (a -> b)
  Let :: Lambda env a -> Lambda (a ': env) b -> Lambda env b
  App :: Lambda env (a -> b) -> Lambda env a -> Lambda env b
  Unit :: Lambda env ()
  Pair :: Lambda env a -> Lambda env b -> Lambda env (a, b)
  Fst :: Lambda env (a, b) -> Lambda env a
  Snd :: Lambda env (a, b) -> Lambda env b
  Op :: Type b -> Operation a b -> Lambda env a -> Lambda env b

  AdjPlus :: Lambda env a -> Lambda env a -> Lambda env a
  Zero :: Type a -> Lambda env a

  LId :: Type a -> Lambda env (LFun a a)
  LPair :: Lambda env (LFun a b)
        -> Lambda env (LFun a c)
        -> Lambda env (LFun a (b, c))
  LFst :: Type a -> Type b -> Lambda env (LFun (a, b) a)
  LSnd :: Type a -> Type b -> Lambda env (LFun (a, b) b)
  LComp :: Lambda env (LFun a b)
        -> Lambda env (LFun b c)
        -> Lambda env (LFun a c)
  LSingleton :: Type b -> Lambda env a -> Lambda env (LFun b (Copower a b))
  LCopowFold :: Lambda env (a -> LFun b c) -> Lambda env (LFun (Copower a b) c)
  LOp :: LinearOperation' a b c -> Lambda env (a -> LFun b c)

deriving instance Show (Lambda env t)

-- | A sort-of pointful language that encodes a linear function, in the sense
-- of a commutative monoid homomorphism. Compile this to linear combinators
-- using 'makeLFunTerm'.
data LinLambda env a t where
  LinApp :: Lambda env (LFun s t) -> LinLambda env a s -> LinLambda env a t
  LinLet :: Type s -> LinLambda env a s -> LinLambda env (a, s) t -> LinLambda env a t
  LinLet' :: Type s -> LinLambda env a s -> LinLambda env s t -> LinLambda env a t
  LinVar :: LinLambda env a a
  LinPair :: LinLambda env a s -> LinLambda env a t -> LinLambda env a (s, t)
  LinFst :: LinLambda env a (s, t) -> LinLambda env a s
  LinSnd :: LinLambda env a (s, t) -> LinLambda env a t
  LinLOp :: LinearOperation' s a t -> Lambda env s -> LinLambda env a t
  LinZero :: Type t -> LinLambda env a t
  LinPlus :: LinLambda env a t -> LinLambda env a t -> LinLambda env a t
  LinSingleton :: Lambda env s -> LinLambda env a t -> LinLambda env a (Copower s t)
  LinCopowFold :: Lambda env (b -> LFun c d) -> LinLambda env a (Copower b c) -> LinLambda env a d

makeLFunTerm :: Type a -> LinLambda env a b -> Lambda env (LFun a b)
makeLFunTerm t = \case
  LinApp fun arg -> LComp (makeLFunTerm t arg) fun
  LinLet s rhs body ->
    LComp (LPair (LId t) (makeLFunTerm t rhs)) (makeLFunTerm (TPair t s) body)
  LinLet' s rhs body ->
    LComp (makeLFunTerm t rhs) (makeLFunTerm s body)
  LinVar -> LId t
  LinPair e1 e2 -> LPair (makeLFunTerm t e1) (makeLFunTerm t e2)
  LinFst e ->
    let (term, TPair t1 t2) = withRT t e
    in LComp term (LFst t1 t2)
  LinSnd e ->
    let (term, TPair t1 t2) = withRT t e
    in LComp term (LSnd t1 t2)
  LinLOp lop arg -> LOp lop `App` arg
  LinZero t' -> Zero (TLFun t t')
  LinPlus e1 e2 -> AdjPlus (makeLFunTerm t e1) (makeLFunTerm t e2)
  LinSingleton e1 e2 ->
    let (term, t') = withRT t e2
    in LComp term (LSingleton t' e1)
  LinCopowFold fun cp -> LComp (makeLFunTerm t cp) (LCopowFold fun)
  where
    withRT :: Type a -> LinLambda env a b -> (Lambda env (LFun a b), Type b)
    withRT t1 term = let term' = makeLFunTerm t1 term
                         TLFun _ t' = typeof term'
                     in (term', t')

typeof :: Lambda env t -> Type t
typeof (Var t _) = t
typeof (Lambda t e) = TFun t (typeof e)
typeof (Let _ e) = typeof e
typeof (App a _) = let TFun _ t = typeof a in t
typeof Unit = TNil
typeof (Pair a b) = TPair (typeof a) (typeof b)
typeof (Fst e) = let TPair t _ = typeof e in t
typeof (Snd e) = let TPair _ t = typeof e in t
typeof (Op t _ _) = t
typeof (AdjPlus e _) = typeof e
typeof (Zero t) = t
typeof (LId t) = TLFun t t
typeof (LPair a b) = let TLFun t1 t2 = typeof a ; TLFun _ t3 = typeof b in TLFun t1 (TPair t2 t3)
typeof (LFst a b) = TLFun (TPair a b) a
typeof (LSnd a b) = TLFun (TPair a b) b
typeof (LComp a b) = let TLFun t1 _ = typeof a ; TLFun _ t2 = typeof b in TLFun t1 t2
typeof (LSingleton t e) = TLFun t (TCopow (typeof e) t)
typeof (LCopowFold e) = let TFun t1 (TLFun t2 t3) = typeof e in TLFun (TCopow t1 t2) t3
typeof (LOp lop) = let (t1, t2, t3) = typeofLOp lop in TFun t1 (TLFun t2 t3)

typeofLOp :: LinearOperation' a b c -> (Type a, Type b, Type c)
typeofLOp LProd = (TVect, TVect, TVect)
typeofLOp LReplicate = (TNil, TScal, TVect)
typeofLOp LScalNeg = (TNil, TScal, TScal)
typeofLOp LScalProd = (TScal, TScal, TScal)

data Dict c t where
  Dict :: c t => Dict c t

typeHasLT :: Type t -> Dict LT t
typeHasLT TScal = Dict
typeHasLT TNil = Dict
typeHasLT (TPair a b) | Dict <- typeHasLT a, Dict <- typeHasLT b = Dict
typeHasLT (TFun a b) | Dict <- typeHasLT a, Dict <- typeHasLT b = Dict
typeHasLT (TLFun a b) | Dict <- typeHasLT a, Dict <- typeHasLT b = Dict
typeHasLT (TCopow a b) | Dict <- typeHasLT a, Dict <- typeHasLT b = Dict
typeHasLT TVect = Dict

typeofOp2 :: Operation a b -> Type b
typeofOp2 = \case
  Constant _ -> error "typeof Constant"
  EAdd -> TVect
  EProd -> TVect
  EScalAdd -> TScal
  EScalSubt -> TScal
  EScalProd -> TScal
  EScalSin -> TScal
  EScalCos -> TScal
  Operation.Sum -> TScal

-- | Substitute variable with De Bruijn index zero in a 'TTerm'
substLam :: env :> env' -> Lambda env' u -> Lambda (u ': env) t -> Lambda env' t
substLam w v =
  substLam'
    Z
    v
    (Weaken $ \case
       Z -> error "substLam: replaced variable should've been replaced"
       S i -> w >:> i)

-- | Substitute given variable with the given environment weakening action in a
-- 'Lambda'
substLam' :: Idx env u -> Lambda env' u -> env :> env' -> Lambda env t -> Lambda env' t
substLam' i v w (Var ty i')
  | Just Refl <- geq i i' = v
  | otherwise = Var ty (w >:> i')
substLam' i v w (Lambda ty e) =
  Lambda ty (substLam' (S i) (sinkLam (wSucc wId) v) (wSink w) e)
substLam' i v w (Let rhs e) =
  Let (substLam' i v w rhs)
      (substLam' (S i) (sinkLam (wSucc wId) v) (wSink w) e)
substLam' i v w (App f a) = App (substLam' i v w f) (substLam' i v w a)
substLam' _ _ _ Unit = Unit
substLam' i v w (Pair a b) = Pair (substLam' i v w a) (substLam' i v w b)
substLam' i v w (Fst p) = Fst (substLam' i v w p)
substLam' i v w (Snd p) = Snd (substLam' i v w p)
substLam' i v w (Op t op y) = Op t op (substLam' i v w y)
substLam' i v w (AdjPlus a b) = AdjPlus (substLam' i v w a) (substLam' i v w b)
substLam' _ _ _ (Zero t) = Zero t
substLam' _ _ _ (LId t) = LId t
substLam' i v w (LPair a b) = LPair (substLam' i v w a) (substLam' i v w b)
substLam' _ _ _ (LFst s t) = LFst s t
substLam' _ _ _ (LSnd s t) = LSnd s t
substLam' i v w (LComp a b) = LComp (substLam' i v w a) (substLam' i v w b)
substLam' i v w (LSingleton t e) = LSingleton t (substLam' i v w e)
substLam' i v w (LCopowFold e) = LCopowFold (substLam' i v w e)
substLam' _ _ _ (LOp lop) = LOp lop

-- | Evaluate the target language
evalLam :: Lambda '[] t -> t
evalLam = evalLam' VZ

-- | Evaluate the target language in the given environment
evalLam' :: Val env -> Lambda env t -> t
evalLam' env (Var _ i) = valProject env i
evalLam' env (Lambda _ e) = \v -> evalLam' (VS v env) e
evalLam' env (Let rhs e) = evalLam' (VS (evalLam' env rhs) env) e
evalLam' env (App f a) = evalLam' env f (evalLam' env a)
evalLam' _ Unit = ()
evalLam' env (Pair a b) = (evalLam' env a, evalLam' env b)
evalLam' env (Fst p) = fst $ evalLam' env p
evalLam' env (Snd p) = snd $ evalLam' env p
evalLam' env (Op _ op a) = evalOp op (evalLam' env a)
evalLam' env (AdjPlus a b)
  | Dict <- typeHasLT (typeof a)
  = plus (evalLam' env a) (evalLam' env b)
evalLam' _ (Zero t)
  | Dict <- typeHasLT t
  = zero
evalLam' _ (LId t)
  | Dict <- typeHasLT t
  = lId
evalLam' env (LPair a b)
  | let TLFun t1 t2 = typeof a
        TLFun _ t3 = typeof b
  , Dict <- typeHasLT t1
  , Dict <- typeHasLT t2
  , Dict <- typeHasLT t3
  = lPair (evalLam' env a) (evalLam' env b)
evalLam' _ (LFst s t)
  | Dict <- typeHasLT s
  , Dict <- typeHasLT t
  = lFst
evalLam' _ (LSnd s t)
  | Dict <- typeHasLT s
  , Dict <- typeHasLT t
  = lSnd
evalLam' env (LComp a b)
  | let TLFun t1 t2 = typeof a
        TLFun _ t3 = typeof b
  , Dict <- typeHasLT t1
  , Dict <- typeHasLT t2
  , Dict <- typeHasLT t3
  = lComp (evalLam' env a) (evalLam' env b)
evalLam' env (LSingleton t e)
  | Dict <- typeHasLT t
  = singleton (evalLam' env e)
evalLam' env (LCopowFold e)
  | let TFun _ (TLFun t1 t2) = typeof e
  , Dict <- typeHasLT t1
  , Dict <- typeHasLT t2
  = lCopowFold (evalLam' env e)
evalLam' _ (LOp lop) = evalLOp' lop

sinkLam :: env :> env' -> Lambda env t -> Lambda env' t
sinkLam w (Var t i)        = Var t (w >:> i)
sinkLam w (Lambda ty e)    = Lambda ty (sinkLam (wSink w) e)
sinkLam w (Let rhs e)      = Let (sinkLam w rhs) (sinkLam (wSink w) e)
sinkLam w (App e1 e2)      = App (sinkLam w e1) (sinkLam w e2)
sinkLam _ Unit             = Unit
sinkLam w (Pair a b)       = Pair (sinkLam w a) (sinkLam w b)
sinkLam w (Fst p)          = Fst (sinkLam w p)
sinkLam w (Snd p)          = Snd (sinkLam w p)
sinkLam w (Op t op a)      = Op t op (sinkLam w a)
sinkLam w (AdjPlus a b)    = AdjPlus (sinkLam w a) (sinkLam w b)
sinkLam _ (Zero t)         = Zero t
sinkLam _ (LId t)          = LId t
sinkLam w (LPair a b)      = LPair (sinkLam w a) (sinkLam w b)
sinkLam _ (LFst s t)       = LFst s t
sinkLam _ (LSnd s t)       = LSnd s t
sinkLam w (LComp a b)      = LComp (sinkLam w a) (sinkLam w b)
sinkLam w (LSingleton t e) = LSingleton t (sinkLam w e)
sinkLam w (LCopowFold e)   = LCopowFold (sinkLam w e)
sinkLam _ (LOp lop)        = LOp lop

-- | Pretty print the augmented lambda calculus in 'Lambda'
--
-- Precedences used are as follows:
-- - application is 10
-- - plus is 6
printLam :: Int -> [String] -> Lambda env t -> State Int ShowS
printLam _ env (Var _ i) =
  pure $
    case drop (idxToInt i) env of
      []  -> showString ("ctxtVar" ++ show (idxToInt i - length env + 1))
      x:_ -> showString x
printLam d env (Lambda _ e) = do
  name <- ('x' :) . show <$> get
  modify (+1)
  r <- printLam 0 (name : env) e
  pure $ showParen (d > 0) $ showString ("\\" ++ name ++ " -> ") . r
printLam d env (Let rhs e) = do
  name <- ('x' :) . show <$> get
  modify (+1)
  r1 <- printLam 0 env rhs
  r2 <- printLam 0 (name : env) e
  pure $ showParen (d > 0) $
    showString ("let " ++ name ++ " = ") . r1 . showString " in " . r2
printLam d env (App f a) = do
  r1 <- printLam 10 env f
  r2 <- printLam 11 env a
  pure $ showParen (d > 10) $ r1 . showString " " . r2
printLam _ _ Unit = pure (showString "()")
printLam _ env (Pair a b) = do
  r1 <- printLam 0 env a
  r2 <- printLam 0 env b
  pure $ showString "(" . r1 . showString ", " . r2 . showString ")"
printLam d env (Fst p) = showFunction d env "fst" [Some p]
printLam d env (Snd p) = showFunction d env "snd" [Some p]
printLam d env (Op _ op a) = showFunction d env ("evalOp " ++ showOp op) [Some a]
printLam d env (AdjPlus a b) = do
  r1 <- printLam 6 env a
  r2 <- printLam 6 env b
  pure $ showParen (d > 6) $ r1 . showString " + " . r2
printLam _ _ (Zero _) = pure $ showString "zero"
printLam _ _ (LId _) = pure $ showString "lid"
printLam d env (LPair a b) = showFunction d env "lpair" [Some a, Some b]
printLam _ _ (LFst _ _) = pure $ showString "lfst"
printLam _ _ (LSnd _ _) = pure $ showString "lsnd"
printLam d env (LComp a b) = showFunction d env "lcomp" [Some a, Some b]
printLam d env (LSingleton _ e) = showFunction d env "lsingleton" [Some e]
printLam d env (LCopowFold e) = showFunction d env "lcopowfold" [Some e]
printLam _ _ (LOp lop) = pure $ showString (showLOp' lop)

showFunction :: Int -> [String] -> String -> [Some (Lambda env)] -> State Int ShowS
showFunction d env funcname args = do
  rs <- mapM (\(Some t) -> (showString " " .) <$> printLam 11 env t) args
  pure $
    showParen (d > 10) $
      showString funcname .
      foldr (.) id rs

prettyLam :: Lambda env a -> String
prettyLam term = evalState (printLam 0 [] term) 1 ""

-- instance Show (Lambda env a) where
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
usesOf :: Idx env t -> Lambda env a -> Integer
usesOf x t = getSum (fold (usesOf' x t))

-- | Count the uses of the components of a variable in an expression
usesOf' :: (Num s, Monoid s) => Idx env t -> Lambda env a -> Layout s
usesOf' i (Var _ i')
  | Just Refl <- geq i i' = LyLeaf 1
  | otherwise = mempty
usesOf' i (Lambda _ e) = usesOf' (S i) e
usesOf' i (Let rhs e) = usesOf' i rhs <> usesOf' (S i) e
usesOf' i (App f a) = usesOf' i f <> usesOf' i a
usesOf' _ Unit = mempty
usesOf' i (Pair a b) = usesOf' i a <> usesOf' i b
usesOf' i p@(Fst p') = fromMaybe (usesOf' i p') (usesOfPick i p)
usesOf' i p@(Snd p') = fromMaybe (usesOf' i p') (usesOfPick i p)
usesOf' i (Op _ _ a) = usesOf' i a
usesOf' i (AdjPlus a b) = usesOf' i a <> usesOf' i b
usesOf' _ (Zero _) = mempty
usesOf' _ (LId _) = mempty
usesOf' i (LPair a b) = usesOf' i a <> usesOf' i b
usesOf' _ (LFst _ _) = mempty
usesOf' _ (LSnd _ _) = mempty
usesOf' i (LComp a b) = usesOf' i a <> usesOf' i b
usesOf' i (LSingleton _ e) = usesOf' i e
usesOf' i (LCopowFold e) = usesOf' i e
usesOf' _ (LOp _) = mempty

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


instance GEq Type where
  geq TScal TScal = Just Refl
  geq TScal _ = Nothing
  geq TNil TNil = Just Refl
  geq TNil _ = Nothing
  geq (TPair a b) (TPair a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq TPair{} _ = Nothing
  geq (TFun a b) (TFun a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq TFun{} _ = Nothing
  geq (TLFun a b) (TLFun a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq TLFun{} _ = Nothing
  geq (TCopow a b) (TCopow a' b')
    | Just Refl <- geq a a'
    , Just Refl <- geq b b'
    = Just Refl
  geq TCopow{} _ = Nothing
  geq a@TVect b@TVect
    | Just Refl <- check a b
    = Just Refl
    where -- TODO: Why don't pattern signatures work here?
          check :: forall n m. (KnownNat n, KnownNat m)
                => Type (Vect n) -> Type (Vect m) -> Maybe (n :~: m)
          check _ _ | Just Refl <- sameNat (Proxy @n) (Proxy @m) = Just Refl
                    | otherwise = Nothing
  geq TVect _ = Nothing
