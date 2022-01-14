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
import           Data.Some
import           Data.Type.Equality        ((:~:) (Refl))
import qualified Data.Vector.Unboxed.Sized as V (map, zipWith, replicate, sum, toList)
import           GHC.TypeNats              (KnownNat)

import           Count
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
  CInl :: CTerm env a -> CTerm env (Either a b)
  CInr :: CTerm env b -> CTerm env (Either a b)
  CCase :: CTerm env (Either a b) -> CTerm (a ': env) c -> CTerm (b ': env) c -> CTerm env c
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

  CError :: CTerm env a

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
substCt' i v w (CInl p) = CInl (substCt' i v w p)
substCt' i v w (CInr p) = CInr (substCt' i v w p)
substCt' i v w (CCase e a b) =
  CCase (substCt' i v w e)
        (substCt' (S i) (sinkCt1 v) (wSink w) a)
        (substCt' (S i) (sinkCt1 v) (wSink w) b)
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
substCt' _ _ _ CError = CError

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
evalCt' env (CInl p) = Left $ evalCt' env p
evalCt' env (CInr p) = Right $ evalCt' env p
evalCt' env (CCase e a b) =
  case evalCt' env e of Left x  -> evalCt' (VS x env) a
                        Right x -> evalCt' (VS x env) b
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
evalCt' _   CError = error "error term in CTerm"

sinkCt :: env :> env' -> CTerm env t -> CTerm env' t
sinkCt w (CVar i)       = CVar (w >:> i)
sinkCt w (CLambda e)    = CLambda (sinkCt (wSink w) e)
sinkCt w (CLet rhs e)   = CLet (sinkCt w rhs) (sinkCt (wSink w) e)
sinkCt w (CApp e1 e2)   = CApp (sinkCt w e1) (sinkCt w e2)
sinkCt _ CUnit          = CUnit
sinkCt w (CPair a b)    = CPair (sinkCt w a) (sinkCt w b)
sinkCt w (CFst p)       = CFst (sinkCt w p)
sinkCt w (CSnd p)       = CSnd (sinkCt w p)
sinkCt w (CInl p)       = CInl (sinkCt w p)
sinkCt w (CInr p)       = CInr (sinkCt w p)
sinkCt w (CCase e a b)  = CCase (sinkCt w e) (sinkCt (wSink w) a) (sinkCt (wSink w) b)
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
sinkCt _ CError         = CError

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
printCt d env (CFst p) = showFunctionCt d env "fst" [Some p]
printCt d env (CSnd p) = showFunctionCt d env "snd" [Some p]
printCt d env (CInl p) = showFunctionCt d env "inl" [Some p]
printCt d env (CInr p) = showFunctionCt d env "inr" [Some p]
printCt d env (CCase e a b) = do
  e' <- printCt 0 env e
  name1 <- ('x' :) . show <$> get
  modify (+1)
  name2 <- ('x' :) . show <$> get
  modify (+1)
  a' <- printCt 0 (name1 : env) a
  b' <- printCt 0 (name2 : env) b
  pure $ showParen (d > 0) $
    showString "case " . e' . showString (" of { Inl " ++ name1 ++ " -> ")
    . a' . showString (" ; Inr " ++ name2 ++ " -> ") . b' . showString " }"
printCt d env (COp op a) = case (op, a) of
  (Constant x, CUnit) -> pure $ showString (show x)
  (EAdd, CPair a1 a2) -> showFunctionCt d env "vecadd" [Some a1, Some a2]
  (EProd, CPair a1 a2) -> showFunctionCt d env "vecprod" [Some a1, Some a2]
  (EScalAdd, CPair a1 a2) -> binary a1 (6, " + ") a2
  (EScalSubt, CPair a1 a2) -> binary a1 (6, " - ") a2
  (EScalProd, CPair a1 a2) -> binary a1 (7, " * ") a2
  (EScalSin, _) -> showFunctionCt d env "sin" [Some a]
  (EScalCos, _) -> showFunctionCt d env "cos" [Some a]
  (_, _) -> showFunctionCt d env ("evalOp " ++ showOp op) [Some a]
  where
    binary :: CTerm env a -> (Int, String) -> CTerm env b -> State Int ShowS
    binary left (prec, opstr) right = do
      r1 <- printCt (prec + 1) env left
      r2 <- printCt (prec + 1) env right
      pure $ showParen (d > prec) $ r1 . showString opstr . r2
printCt d env (CMap a b) = showFunctionCt d env "vmap" [Some a, Some b]
printCt d env (CZipWith a b c) = showFunctionCt d env "vzipWith" [Some a, Some b, Some c]
printCt d env (CReplicate x) = showFunctionCt d env "vreplicate" [Some x]
printCt d env (CSum x) = showFunctionCt d env "vsum" [Some x]
printCt d env (CToList x) = showFunctionCt d env "toList" [Some x]
printCt _ _ CLNil = pure $ showString "[]"
printCt d env (CLCons a b) = do
  r1 <- printCt 6 env a
  r2 <- printCt 5 env b
  pure $ showParen (d > 5) $ r1 . showString " : " . r2
printCt d env (CLMap f a) = showFunctionCt d env "map" [Some f, Some a]
printCt d env (CLFoldr a b c) = showFunctionCt d env "foldr" [Some a, Some b, Some c]
printCt d env (CLSum x) = showFunctionCt d env "sum" [Some x]
printCt d env (CLZip a b) = showFunctionCt d env "zip" [Some a, Some b]
printCt _ _ CZero = pure $ showString "zero"
printCt d env (CPlus a b) = showFunctionCt d env "plus" [Some a, Some b]
printCt _ _ CError = pure $ showString "error"

showFunctionCt :: Int -> [String] -> String -> [Some (CTerm env)] -> State Int ShowS
showFunctionCt d env funcname args = do
  rs <- mapM (\(Some t) -> (showString " " .) <$> printCt 11 env t) args
  pure $
    showParen (d > 10) $
      showString funcname .
      foldr (.) id rs

prettyCt :: CTerm env a -> String
prettyCt term = evalState (printCt 0 [] term) 1 ""

-- instance Show (CTerm env a) where
--   showsPrec p term = evalState (printLam p [] term) 1

-- | Count the uses of a variable in an expression
usesOfCt :: Idx env t -> CTerm env a -> OccCount
usesOfCt x t = fold (usesOfCt' x t)

-- | Count the uses of the components of a variable in an expression
usesOfCt' :: Idx env t -> CTerm env a -> Layout t OccCount
usesOfCt' i = \case
  CVar i'
    | Just Refl <- geq i i' -> LyLeaf (OccCount 1 1)
    | otherwise -> mempty
  CLambda e -> occRepeatRuntime <$> usesOfCt' (S i) e  -- the lambda may be invoked many times!
  CLet rhs e -> usesOfCt' i rhs <> usesOfCt' (S i) e
  CApp f a -> usesOfCt' i f <> usesOfCt' i a
  CUnit -> mempty
  CPair a b -> usesOfCt' i a <> usesOfCt' i b
  p@(CFst p') -> maybe (usesOfCt' i p') (layoutFromPick (OccCount 1 1)) (getPick i p)
  p@(CSnd p') -> maybe (usesOfCt' i p') (layoutFromPick (OccCount 1 1)) (getPick i p)
  CInl e -> usesOfCt' i e
  CInr e -> usesOfCt' i e
  CCase e a b -> usesOfCt' i e <> (occEither <$> usesOfCt' (S i) a <*> usesOfCt' (S i) b)  -- branching
  COp _ a -> usesOfCt' i a
  CMap a b -> usesOfCt' i a <> usesOfCt' i b
  CZipWith a b c -> usesOfCt' i a <> usesOfCt' i b <> usesOfCt' i c
  CReplicate x -> usesOfCt' i x
  CSum x -> usesOfCt' i x
  CToList x -> usesOfCt' i x
  CLNil -> mempty
  CLCons a b -> usesOfCt' i a <> usesOfCt' i b
  CLMap a b -> usesOfCt' i a <> usesOfCt' i b
  CLFoldr a b c -> usesOfCt' i a <> usesOfCt' i b <> usesOfCt' i c
  CLSum x -> usesOfCt' i x
  CLZip a b -> usesOfCt' i a <> usesOfCt' i b
  CZero -> mempty
  CPlus a b -> usesOfCt' i a <> usesOfCt' i b
  CError -> mempty
  where
    getPick :: Idx env t -> CTerm env a -> Maybe (TupPick t a)
    getPick j (CVar j') | Just Refl <- geq j j' = Just TPHere
    getPick j (CFst e) = TPFst <$> getPick j e
    getPick j (CSnd e) = TPSnd <$> getPick j e
    getPick _ _ = Nothing
