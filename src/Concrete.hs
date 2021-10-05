{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

-- | Example of a concrete language that a compiler may use as target for a
-- compilation (phase). Converting the @TargetLanguage@ of AD to this language
-- entails giving an interpretation of the abstract copower operations in terms
-- of operations that the concrete language understands. Furthermore, this
-- concrete language contains no linear functions any more.
module Concrete where

import           Control.Monad.State.Strict
import           Data.Foldable             (fold)
import           Data.GADT.Compare         (GEq (..))
import           Data.List                 (intersperse)
import           Data.Monoid               (getSum)
import           Data.Some
import           Data.Type.Equality        ((:~:) (Refl))
import qualified Data.Vector.Unboxed.Sized as V (map, zipWith, replicate, sum, toList)
import           GHC.TypeNats              (KnownNat)

import           Env
import           Operation
import           Types

-- | Terms of the target language
data CTerm env t where
  CVar :: Idx env a -> CTerm env a
  CLambda :: CTerm (a ': env) b -> CTerm env (a -> b)
  CLet :: CTerm env a -> CTerm (a ': env) b -> CTerm env b
  CApp :: CTerm env (a -> b) -> CTerm env a -> CTerm env b
  CUnit :: CTerm env ()
  CPair :: CTerm env a -> CTerm env b -> CTerm env (a, b)
  CFst :: CTerm env (a, b) -> CTerm env a
  CSnd :: CTerm env (a, b) -> CTerm env b
  COp :: Operation a b -> CTerm env a -> CTerm env b

  CMap :: KnownNat n => CTerm env (Scal -> Scal) -> CTerm env (Vect n) -> CTerm env (Vect n)
  CZipWith :: KnownNat n => CTerm env (Scal -> Scal -> Scal) -> CTerm env (Vect n) -> CTerm env (Vect n) -> CTerm env (Vect n)
  CReplicate :: KnownNat n => CTerm env Scal -> CTerm env (Vect n)
  CSum :: KnownNat n => CTerm env (Vect n) -> CTerm env Scal
  CToList :: KnownNat n => CTerm env (Vect n) -> CTerm env [Scal]

  CLNil :: CTerm env [a]
  CLCons :: CTerm env a -> CTerm env [a] -> CTerm env [a]
  CLMap :: CTerm env (a -> b) -> CTerm env [a] -> CTerm env [b]
  CLFoldr :: CTerm env (a -> b -> b) -> CTerm env b -> CTerm env [a] -> CTerm env b
  CLSum :: LT a => CTerm env [a] -> CTerm env a
  CLZip :: CTerm env [a] -> CTerm env [b] -> CTerm env [(a, b)]

  CZero :: LT a => CTerm env a
  CPlus :: LT a => CTerm env a -> CTerm env a -> CTerm env a

deriving instance Show (CTerm env a)

-- | Substitute variable with De Bruijn index zero in a 'CTerm'
substCt :: env :> env' -> CTerm env' u -> CTerm (u ': env) t -> CTerm env' t
substCt w v =
  substCt'
    Z
    v
    (Weaken $ \case
       Z -> error "substCt: replaced variable should've been replaced"
       S i -> w >:> i)

-- | Substitute given variable with the given environment weakening action in a
-- 'CTerm'
substCt' :: Idx env u -> CTerm env' u -> env :> env' -> CTerm env t -> CTerm env' t
substCt' i v w (CVar i')
  | Just Refl <- geq i i' = v
  | otherwise = CVar (w >:> i')
substCt' i v w (CLambda e) =
  CLambda (substCt' (S i) (sinkCt1 v) (wSink w) e)
substCt' i v w (CLet rhs e) =
  CLet (substCt' i v w rhs)
       (substCt' (S i) (sinkCt1 v) (wSink w) e)
substCt' i v w (CApp f a) = CApp (substCt' i v w f) (substCt' i v w a)
substCt' _ _ _ CUnit = CUnit
substCt' i v w (CPair a b) = CPair (substCt' i v w a) (substCt' i v w b)
substCt' i v w (CFst p) = CFst (substCt' i v w p)
substCt' i v w (CSnd p) = CSnd (substCt' i v w p)
substCt' i v w (COp op y) = COp op (substCt' i v w y)
substCt' i v w (CMap a b) = CMap (substCt' i v w a) (substCt' i v w b)
substCt' i v w (CZipWith a b c) = CZipWith (substCt' i v w a) (substCt' i v w b) (substCt' i v w c)
substCt' i v w (CReplicate x) = CReplicate (substCt' i v w x)
substCt' i v w (CSum x) = CSum (substCt' i v w x)
substCt' i v w (CToList p) = CToList (substCt' i v w p)
substCt' _ _ _ CLNil = CLNil
substCt' i v w (CLCons a b) = CLCons (substCt' i v w a) (substCt' i v w b)
substCt' i v w (CLZip a b) = CLZip (substCt' i v w a) (substCt' i v w b)
substCt' i v w (CLMap a b) = CLMap (substCt' i v w a) (substCt' i v w b)
substCt' i v w (CLFoldr a b c) = CLFoldr (substCt' i v w a) (substCt' i v w b) (substCt' i v w c)
substCt' i v w (CLSum a) = CLSum (substCt' i v w a)
substCt' _ _ _ CZero = CZero
substCt' i v w (CPlus a b) = CPlus (substCt' i v w a) (substCt' i v w b)

-- | Evaluate the target language
evalCt :: CTerm '[] t -> t
evalCt = evalCt' VZ

-- | Evaluate the target language in the given environment
evalCt' :: Val env -> CTerm env t -> t
evalCt' env (CVar i) = valProject env i
evalCt' env (CLambda e) = \v -> evalCt' (VS v env) e
evalCt' env (CLet rhs e) = evalCt' (VS (evalCt' env rhs) env) e
evalCt' env (CApp f a) = evalCt' env f (evalCt' env a)
evalCt' _   CUnit = ()
evalCt' env (CPair a b) = (evalCt' env a, evalCt' env b)
evalCt' env (CFst p) = fst $ evalCt' env p
evalCt' env (CSnd p) = snd $ evalCt' env p
evalCt' env (COp op a) = evalOp op (evalCt' env a)
evalCt' env (CMap a b) = V.map (evalCt' env a) (evalCt' env b)
evalCt' env (CZipWith a b c) = V.zipWith (evalCt' env a) (evalCt' env b) (evalCt' env c)
evalCt' env (CReplicate x) = V.replicate (evalCt' env x)
evalCt' env (CSum x) = V.sum (evalCt' env x)
evalCt' env (CToList x) = V.toList (evalCt' env x)
evalCt' _   CLNil = []
evalCt' env (CLCons a b) = evalCt' env a : evalCt' env b
evalCt' env (CLMap a b) = map (evalCt' env a) (evalCt' env b)
evalCt' env (CLFoldr a b c) = foldr (evalCt' env a) (evalCt' env b) (evalCt' env c)
evalCt' env (CLSum x) = foldr plus zero (evalCt' env x)
evalCt' env (CLZip a b) = zip (evalCt' env a) (evalCt' env b)
evalCt' _   CZero = zero
evalCt' env (CPlus a b) = plus (evalCt' env a) (evalCt' env b)

sinkCt :: env :> env' -> CTerm env t -> CTerm env' t
sinkCt w (CVar i)       = CVar (w >:> i)
sinkCt w (CLambda e)    = CLambda (sinkCt (wSink w) e)
sinkCt w (CLet rhs e)   = CLet (sinkCt w rhs) (sinkCt (wSink w) e)
sinkCt w (CApp e1 e2)   = CApp (sinkCt w e1) (sinkCt w e2)
sinkCt _ CUnit          = CUnit
sinkCt w (CPair a b)    = CPair (sinkCt w a) (sinkCt w b)
sinkCt w (CFst p)       = CFst (sinkCt w p)
sinkCt w (CSnd p)       = CSnd (sinkCt w p)
sinkCt w (COp op a)     = COp op (sinkCt w a)
sinkCt w (CMap a b)     = CMap (sinkCt w a) (sinkCt w b)
sinkCt w (CZipWith a b c) = CZipWith (sinkCt w a) (sinkCt w b) (sinkCt w c)
sinkCt w (CReplicate x) = CReplicate (sinkCt w x)
sinkCt w (CSum x)       = CSum (sinkCt w x)
sinkCt w (CToList x)    = CToList (sinkCt w x)
sinkCt _ CLNil          = CLNil
sinkCt w (CLCons a b)   = CLCons (sinkCt w a) (sinkCt w b)
sinkCt w (CLMap a b)    = CLMap (sinkCt w a) (sinkCt w b)
sinkCt w (CLFoldr a b c) = CLFoldr (sinkCt w a) (sinkCt w b) (sinkCt w c)
sinkCt w (CLSum x)      = CLSum (sinkCt w x)
sinkCt w (CLZip a b)    = CLZip (sinkCt w a) (sinkCt w b)
sinkCt _ CZero          = CZero
sinkCt w (CPlus a b)    = CPlus (sinkCt w a) (sinkCt w b)

sinkCt1 :: CTerm env t -> CTerm (a ': env) t
sinkCt1 = sinkCt (wSucc wId)

-- | Pretty print the augmented lambda calculus in 'CTerm'
--
-- Precedences used are as in Haskell.
printCt :: Int -> [String] -> CTerm env t -> State Int ShowS
printCt _ env (CVar i) =
  pure $
    case drop (idxToInt i) env of
      []  -> showString ("ctxtVar" ++ show (idxToInt i - length env + 1))
      x:_ -> showString x
printCt d env (CLambda e) = do
  name <- ('x' :) . show <$> get
  modify (+1)
  r <- printCt 0 (name : env) e
  pure $ showParen (d > 0) $ showString ("\\" ++ name ++ " -> ") . r
printCt d env topexpr@CLet{} = do
  let collect :: [String] -> CTerm env a -> State Int ([(String, ShowS)], ShowS)
      collect env' (CLet rhs e) = do
        name <- ('x' :) . show <$> get
        modify (+1)
        r1 <- printCt 0 env' rhs
        (rest, core) <- collect (name : env') e
        return ((name, r1) : rest, core)
      collect env' e = ([],) <$> printCt 0 env' e
  (pairs, core) <- collect env topexpr
  pure $ showParen (d > 0) $
    showString "let "
    . foldr (.) id (intersperse (showString " ; ")
                        [showString (lhs ++ " = ") . rhs | (lhs, rhs) <- pairs])
    . showString " in " . core
printCt d env (CApp f a) = do
  r1 <- printCt 10 env f
  r2 <- printCt 11 env a
  pure $ showParen (d > 10) $ r1 . showString " " . r2
printCt _ _ CUnit = pure (showString "()")
printCt _ env (CPair a b) = do
  r1 <- printCt 0 env a
  r2 <- printCt 0 env b
  pure $ showString "(" . r1 . showString ", " . r2 . showString ")"
printCt d env (CFst p) = showFunction d env "fst" [Some p]
printCt d env (CSnd p) = showFunction d env "snd" [Some p]
printCt d env (COp op a) = case (op, a) of
  (Constant x, CUnit) -> pure $ showString (show x)
  (EAdd, CPair a1 a2) -> showFunction d env "vecadd" [Some a1, Some a2]
  (EProd, CPair a1 a2) -> showFunction d env "vecprod" [Some a1, Some a2]
  (EScalAdd, CPair a1 a2) -> binary a1 (6, " + ") a2
  (EScalSubt, CPair a1 a2) -> binary a1 (6, " - ") a2
  (EScalProd, CPair a1 a2) -> binary a1 (7, " * ") a2
  (EScalSin, _) -> showFunction d env "sin" [Some a]
  (EScalCos, _) -> showFunction d env "cos" [Some a]
  (_, _) -> showFunction d env ("evalOp " ++ showOp op) [Some a]
  where
    binary :: CTerm env a -> (Int, String) -> CTerm env b -> State Int ShowS
    binary left (prec, opstr) right = do
      r1 <- printCt (prec + 1) env left
      r2 <- printCt (prec + 1) env right
      pure $ showParen (d > prec) $ r1 . showString opstr . r2
printCt d env (CMap a b) = showFunction d env "vmap" [Some a, Some b]
printCt d env (CZipWith a b c) = showFunction d env "vzipWith" [Some a, Some b, Some c]
printCt d env (CReplicate x) = showFunction d env "vreplicate" [Some x]
printCt d env (CSum x) = showFunction d env "vsum" [Some x]
printCt d env (CToList x) = showFunction d env "toList" [Some x]
printCt _ _ CLNil = pure $ showString "[]"
printCt d env (CLCons a b) = do
  r1 <- printCt 6 env a
  r2 <- printCt 5 env b
  pure $ showParen (d > 5) $ r1 . showString " : " . r2
printCt d env (CLMap f a) = showFunction d env "map" [Some f, Some a]
printCt d env (CLFoldr a b c) = showFunction d env "foldr" [Some a, Some b, Some c]
printCt d env (CLSum x) = showFunction d env "sum" [Some x]
printCt d env (CLZip a b) = showFunction d env "zip" [Some a, Some b]
printCt _ _ CZero = pure $ showString "zero"
printCt d env (CPlus a b) = showFunction d env "plus" [Some a, Some b]

showFunction :: Int -> [String] -> String -> [Some (CTerm env)] -> State Int ShowS
showFunction d env funcname args = do
  rs <- mapM (\(Some t) -> (showString " " .) <$> printCt 11 env t) args
  pure $
    showParen (d > 10) $
      showString funcname .
      foldr (.) id rs

prettyCt :: CTerm env a -> String
prettyCt term = evalState (printCt 0 [] term) 1 ""

-- instance Show (CTerm env a) where
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
usesOf :: Idx env t -> CTerm env a -> Integer
usesOf x t = getSum (fold (usesOf' x t))

-- | Count the uses of the components of a variable in an expression
usesOf' :: (Num s, Monoid s) => Idx env t -> CTerm env a -> Layout t s
usesOf' i (CVar i')
  | Just Refl <- geq i i' = LyLeaf 1
  | otherwise = mempty
usesOf' i (CLambda e) = usesOf' (S i) e
usesOf' i (CLet rhs e) = usesOf' i rhs <> usesOf' (S i) e
usesOf' i (CApp f a) = usesOf' i f <> usesOf' i a
usesOf' _ CUnit = mempty
usesOf' i (CPair a b) = usesOf' i a <> usesOf' i b
usesOf' i p@(CFst p') = maybe (usesOf' i p') layoutFromPick (getPick i p)
usesOf' i p@(CSnd p') = maybe (usesOf' i p') layoutFromPick (getPick i p)
usesOf' i (COp _ a) = usesOf' i a
usesOf' i (CMap a b) = usesOf' i a <> usesOf' i b
usesOf' i (CZipWith a b c) = usesOf' i a <> usesOf' i b <> usesOf' i c
usesOf' i (CReplicate x) = usesOf' i x
usesOf' i (CSum x) = usesOf' i x
usesOf' i (CToList x) = usesOf' i x
usesOf' _ CLNil = mempty
usesOf' i (CLCons a b) = usesOf' i a <> usesOf' i b
usesOf' i (CLMap a b) = usesOf' i a <> usesOf' i b
usesOf' i (CLFoldr a b c) = usesOf' i a <> usesOf' i b <> usesOf' i c
usesOf' i (CLSum x) = usesOf' i x
usesOf' i (CLZip a b) = usesOf' i a <> usesOf' i b
usesOf' _ CZero = mempty
usesOf' i (CPlus a b) = usesOf' i a <> usesOf' i b

data TupPick large small where
  TPHere :: TupPick t t
  TPFst :: TupPick t (a, b) -> TupPick t a
  TPSnd :: TupPick t (a, b) -> TupPick t b

getPick :: Idx env t -> CTerm env a -> Maybe (TupPick t a)
getPick i (CVar j) | Just Refl <- geq i j = Just TPHere
getPick i (CFst e) = TPFst <$> getPick i e
getPick i (CSnd e) = TPSnd <$> getPick i e
getPick _ _ = Nothing

layoutFromPick :: (Num s, Monoid s) => TupPick t t' -> Layout t s
layoutFromPick = go (LyLeaf 1)
  where
    go :: (Num s, Monoid s) => Layout t' s -> TupPick t t' -> Layout t s
    go l TPHere = l
    go l (TPFst p) = go (LyPair l mempty) p
    go l (TPSnd p) = go (LyPair mempty l) p
