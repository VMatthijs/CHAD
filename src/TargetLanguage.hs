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
import qualified Data.Vector.Unboxed.Sized as V (map, replicate, sum)
import           GHC.TypeNats              (KnownNat)

import           Count
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
  Op :: (a ~ UnLin a, b ~ UnLin b) => Operation a b -> TTerm env a -> TTerm env b

  Map :: KnownNat n => TTerm env (Scal -> Scal) -> TTerm env (Vect n) -> TTerm env (Vect n)
  Replicate :: KnownNat n => TTerm env Scal -> TTerm env (Vect n)
  Sum :: KnownNat n => TTerm env (Vect n) -> TTerm env Scal

  -- AdjPlus :: LT a => TTerm env a -> TTerm env a -> TTerm env a
  Zero :: LTU a => TTerm env a

  LinFun :: (LT a, LT b) => LinTTerm env '[a] b -> TTerm env (LFun a b)

deriving instance Show (TTerm env a)

-- | A sort-of pointful language that encodes a linear function, in the sense
-- of a commutative monoid homomorphism. The domain is the linear environment
-- @lenv@; the codomain is @t@. The linear function also has access to
-- unrestricted variables in the environment @env@ inherited from the
-- surrounding non-linear computation.
data LinTTerm env lenv t where
  LinApp :: (LTenv lenv, LT s, LT t) => TTerm env (LFun s t) -> LinTTerm env lenv s -> LinTTerm env lenv t
  LinApp' :: LT t => LinTTerm env lenv (s -> t) -> TTerm env s -> LinTTerm env lenv t
  LinLam :: LT t => LinTTerm (a ': env) lenv t -> LinTTerm env lenv (a -> t)
  LinLet :: (LTenv lenv, LT s, LT t) => LinTTerm env lenv s -> LinTTerm env (s ': lenv) t -> LinTTerm env lenv t
  LinVar :: LT t => Idx lenv t -> LinTTerm env lenv t
  LinPair :: (LTenv lenv, LT s, LT t) => LinTTerm env lenv s -> LinTTerm env lenv t -> LinTTerm env lenv (s, t)
  LinFst :: (LTenv lenv, LT s, LT t) => LinTTerm env lenv (s, t) -> LinTTerm env lenv s
  LinSnd :: (LTenv lenv, LT s, LT t) => LinTTerm env lenv (s, t) -> LinTTerm env lenv t
  LinLOp :: (LTenv lenv, LT b, LT t, s ~ UnLin s, b ~ UnLin b, t ~ UnLin t) => LinearOperation s b t -> TTerm env s -> LinTTerm env lenv b -> LinTTerm env lenv t
  LinZero :: (LTenv lenv, LTU t) => LinTTerm env lenv t
  LinPlus :: (LTenv lenv, LTU t) => LinTTerm env lenv t -> LinTTerm env lenv t -> LinTTerm env lenv t
  LinSingleton :: (LTenv lenv, LT t) => TTerm env s -> LinTTerm env lenv t -> LinTTerm env lenv (Copower s t)
  LinCopowFold :: (LTenv lenv, LT b, LTU c) => TTerm env (a -> LFun b c) -> LinTTerm env lenv (Copower a b) -> LinTTerm env lenv c

  LinZip :: KnownNat n
         => TTerm env (Vect n)
         -> LinTTerm env lenv (Vect n)
         -> LinTTerm env lenv (Copower Scal Scal)
  LinMap :: KnownNat n
         => LinTTerm env lenv (Scal -> Scal)
         -> TTerm env (Vect n)
         -> LinTTerm env lenv (Vect n)
  LinZipWith :: KnownNat n
             => TTerm env (Scal -> LFun Scal Scal)
             -> TTerm env (Vect n)
             -> LinTTerm env lenv (Vect n)
             -> LinTTerm env lenv (Vect n)
  LinReplicate :: KnownNat n => LinTTerm env lenv Scal -> LinTTerm env lenv (Vect n)
  LinSum :: KnownNat n => LinTTerm env lenv (Vect n) -> LinTTerm env lenv Scal

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
  Lambda (substTt' (S i) (sinkTt1 v) (wSink w) e)
substTt' i v w (Let rhs e) =
  Let (substTt' i v w rhs)
      (substTt' (S i) (sinkTt1 v) (wSink w) e)
substTt' i v w (App f a) = App (substTt' i v w f) (substTt' i v w a)
substTt' _ _ _ Unit = Unit
substTt' i v w (Pair a b) = Pair (substTt' i v w a) (substTt' i v w b)
substTt' i v w (Fst p) = Fst (substTt' i v w p)
substTt' i v w (Snd p) = Snd (substTt' i v w p)
substTt' i v w (Op op y) = Op op (substTt' i v w y)
substTt' i v w (Map a b) = Map (substTt' i v w a) (substTt' i v w b)
substTt' i v w (Replicate x) = Replicate (substTt' i v w x)
substTt' i v w (Sum a) = Sum (substTt' i v w a)
-- substTt' i v w (AdjPlus a b) = AdjPlus (substTt' i v w a) (substTt' i v w b)
substTt' _ _ _ Zero = Zero
substTt' i v w (LinFun f) = LinFun (substLTt' i v w f)

-- | Substitute given variable with the given environment weakening action in a
-- 'LinTTerm'
substLTt' :: Idx env u -> TTerm env' u -> env :> env' -> LinTTerm env lenv b -> LinTTerm env' lenv b
substLTt' i v w (LinApp term f) = LinApp (substTt' i v w term) (substLTt' i v w f)
substLTt' i v w (LinApp' f term) = LinApp' (substLTt' i v w f) (substTt' i v w term)
substLTt' i v w (LinLam f) = LinLam (substLTt' (S i) (sinkTt1 v) (wSink w) f)
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
substLTt' i v w (LinZip term f) = LinZip (substTt' i v w term) (substLTt' i v w f)
substLTt' i v w (LinMap f arg) = LinMap (substLTt' i v w f) (substTt' i v w arg)
substLTt' i v w (LinZipWith fun term f) = LinZipWith (substTt' i v w fun) (substTt' i v w term) (substLTt' i v w f)
substLTt' i v w (LinReplicate f) = LinReplicate (substLTt' i v w f)
substLTt' i v w (LinSum f) = LinSum (substLTt' i v w f)

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
substLinTt' i v w (LinApp' a term) = LinApp' (substLinTt' i v w a) term
substLinTt' i v w (LinLam f) = LinLam (substLinTt' i (sinkTtL (wSucc wId) v) w f)
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
substLinTt' i v w (LinZip term f) = LinZip term (substLinTt' i v w f)
substLinTt' i v w (LinMap f arg) = LinMap (substLinTt' i v w f) arg
substLinTt' i v w (LinZipWith fun term f) = LinZipWith fun term (substLinTt' i v w f)
substLinTt' i v w (LinReplicate f) = LinReplicate (substLinTt' i v w f)
substLinTt' i v w (LinSum f) = LinSum (substLinTt' i v w f)

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
evalTt' env (Replicate x) = V.replicate (evalTt' env x)
evalTt' env (Sum a) = V.sum (evalTt' env a)
-- evalTt' env (AdjPlus a b) = plus (evalTt' env a) (evalTt' env b)
evalTt' _   Zero = zero
evalTt' env (LinFun f) = lPair lUnit lId `lComp` evalLTt' env f

type family LinEnvType lenv where
  LinEnvType '[] = ()
  LinEnvType (t ': lenv) = (LinEnvType lenv, t)

-- | Evaluate the linear sublanguage of the target language in the given environment
evalLTt' :: LT (LinEnvType lenv) => Val env -> LinTTerm env lenv b -> LFun (LinEnvType lenv) b
evalLTt' env (LinApp fun arg) = lComp (evalLTt' env arg) (evalTt' env fun)
evalLTt' env (LinApp' fun arg) = evalLTt' env fun `lComp` lEval (evalTt' env arg)
evalLTt' env (LinLam e) = lSwap (\x -> evalLTt' (VS x env) e)
evalLTt' env (LinLet rhs body) = lComp (lPair lId (evalLTt' env rhs)) (evalLTt' env body)
evalLTt' _   (LinVar j) = makeProj j
  where makeProj :: (LT (LinEnvType lenv), LT t) => Idx lenv t -> LFun (LinEnvType lenv) t
        makeProj Z = lSnd
        makeProj (S i) = lFst `lComp` makeProj i
evalLTt' env (LinPair e1 e2) = lPair (evalLTt' env e1) (evalLTt' env e2)
evalLTt' env (LinFst e) = lComp (evalLTt' env e) lFst
evalLTt' env (LinSnd e) = lComp (evalLTt' env e) lSnd
evalLTt' env (LinLOp lop term arg) = evalLTt' env arg `lComp` evalLOp lop (evalTt' env term)
evalLTt' _   LinZero = zero
evalLTt' env (LinPlus e1 e2) = plus (evalLTt' env e1) (evalLTt' env e2)
evalLTt' env (LinSingleton e1 e2) = lComp (evalLTt' env e2) (singleton (evalTt' env e1))
evalLTt' env (LinCopowFold fun cp) = lComp (evalLTt' env cp) (lCopowFold (evalTt' env fun))
evalLTt' env (LinZip p d) = evalLTt' env d `lComp` lZip (evalTt' env p)
evalLTt' env (LinMap a f) = evalLTt' env a `lComp` lMap (evalTt' env f)
evalLTt' env (LinZipWith f p d) = evalLTt' env d `lComp` lZipWith (evalTt' env f) (evalTt' env p)
evalLTt' env (LinReplicate e) = evalLTt' env e `lComp` lExpand
evalLTt' env (LinSum e) = evalLTt' env e `lComp` lSum

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
sinkTt w (Replicate x) = Replicate (sinkTt w x)
sinkTt w (Sum a)       = Sum (sinkTt w a)
-- sinkTt w (AdjPlus a b) = AdjPlus (sinkTt w a) (sinkTt w b)
sinkTt _ Zero          = Zero
sinkTt w (LinFun f)    = LinFun (sinkTtL w f)

sinkTt1 :: TTerm env t -> TTerm (a ': env) t
sinkTt1 = sinkTt (wSucc wId)

sinkTtL :: env :> env' -> LinTTerm env lenv b -> LinTTerm env' lenv b
sinkTtL w (LinApp term f) = LinApp (sinkTt w term) (sinkTtL w f)
sinkTtL w (LinApp' f term) = LinApp' (sinkTtL w f) (sinkTt w term)
sinkTtL w (LinLam f) = LinLam (sinkTtL (wSink w) f)
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
sinkTtL w (LinZip term f) = LinZip (sinkTt w term) (sinkTtL w f)
sinkTtL w (LinMap f arg) = LinMap (sinkTtL w f) (sinkTt w arg)
sinkTtL w (LinZipWith fun term f) = LinZipWith (sinkTt w fun) (sinkTt w term) (sinkTtL w f)
sinkTtL w (LinReplicate f) = LinReplicate (sinkTtL w f)
sinkTtL w (LinSum f) = LinSum (sinkTtL w f)

sinkLinTt :: LTenv lenv' => lenv :> lenv' -> LinTTerm env lenv b -> LinTTerm env lenv' b
sinkLinTt w (LinApp term f) = LinApp term (sinkLinTt w f)
sinkLinTt w (LinApp' f term) = LinApp' (sinkLinTt w f) term
sinkLinTt w (LinLam f) = LinLam (sinkLinTt w f)
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
sinkLinTt w (LinZip term f) = LinZip term (sinkLinTt w f)
sinkLinTt w (LinMap f arg) = LinMap (sinkLinTt w f) arg
sinkLinTt w (LinZipWith fun term f) = LinZipWith fun term (sinkLinTt w f)
sinkLinTt w (LinReplicate f) = LinReplicate (sinkLinTt w f)
sinkLinTt w (LinSum f) = LinSum (sinkLinTt w f)

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
  (_, _) -> showFunction d env [] ("evalOp " ++ showOp op) [SomeTTerm a]
  where
    binary :: TTerm env a -> (Int, String) -> TTerm env b -> State Int ShowS
    binary left (prec, opstr) right = do
      r1 <- printTt (prec + 1) env left
      r2 <- printTt (prec + 1) env right
      pure $ showParen (d > prec) $ r1 . showString opstr . r2
printTt d env (Map a b) = showFunction d env [] "map" [SomeTTerm a, SomeTTerm b]
printTt d env (Replicate x) = showFunction d env [] "replicate" [SomeTTerm x]
printTt d env (Sum a) = showFunction d env [] "sum" [SomeTTerm a]
-- printTt d env (AdjPlus a b) = showFunction d env [] "plus" [SomeTTerm a, SomeTTerm b]
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
printLTt d env lenv (LinApp' f a) = do
  r1 <- printLTt 10 env lenv f
  r2 <- printTt 11 env a
  pure $ showParen (d > 10) $ r1 . showString " " . r2
printLTt d env lenv (LinLam e) = do
  name <- ('v' :) . show <$> get
  modify (+1)
  r <- printLTt 0 (name : env) lenv e
  pure $ showParen (d > 0) $ showString ("\\" ++ name ++ " -> ") . r
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
    showString (showLOp op ++ " ") . r1 . showString " " . r2
printLTt _ _ _ LinZero = pure $ showString "zero"
printLTt d env lenv (LinPlus f g) = showFunction d env lenv "plus" [SomeLinTTerm f, SomeLinTTerm g]
printLTt d env lenv (LinSingleton term f) = showFunction d env lenv "singleton" [SomeTTerm term, SomeLinTTerm f]
printLTt d env lenv (LinCopowFold term f) = showFunction d env lenv "copowfold" [SomeTTerm term, SomeLinTTerm f]
printLTt d env lenv (LinZip term f) = showFunction d env lenv "lzip" [SomeTTerm term, SomeLinTTerm f]
printLTt d env lenv (LinMap f arg) = showFunction d env lenv "lmap" [SomeLinTTerm f, SomeTTerm arg]
printLTt d env lenv (LinZipWith fun term f) = showFunction d env lenv "lzipWith" [SomeTTerm fun, SomeTTerm term, SomeLinTTerm f]
printLTt d env lenv (LinReplicate f) = showFunction d env lenv "lreplicate" [SomeLinTTerm f]
printLTt d env lenv (LinSum f) = showFunction d env lenv "lsum" [SomeLinTTerm f]

data SomeLinTTerm env
  = forall a b. SomeLinTTerm (LinTTerm env a b)
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

-- | Count the uses of a variable in an expression
usesOfTt :: Idx env t -> TTerm env a -> Integer
usesOfTt x t = getSum (fold (usesOfTt' x t))

-- | Count the uses of the components of a variable in an expression
usesOfTt' :: (Num s, Monoid s) => Idx env t -> TTerm env a -> Layout t s
usesOfTt' i (Var i')
  | Just Refl <- geq i i' = LyLeaf 1
  | otherwise = mempty
usesOfTt' i (Lambda e) = usesOfTt' (S i) e
usesOfTt' i (Let rhs e) = usesOfTt' i rhs <> usesOfTt' (S i) e
usesOfTt' i (App f a) = usesOfTt' i f <> usesOfTt' i a
usesOfTt' _ Unit = mempty
usesOfTt' i (Pair a b) = usesOfTt' i a <> usesOfTt' i b
usesOfTt' i p@(Fst p') = maybe (usesOfTt' i p') layoutFromPick (getPick i p)
usesOfTt' i p@(Snd p') = maybe (usesOfTt' i p') layoutFromPick (getPick i p)
usesOfTt' i (Op _ a) = usesOfTt' i a
usesOfTt' i (Map a b) = usesOfTt' i a <> usesOfTt' i b
usesOfTt' i (Replicate x) = usesOfTt' i x
usesOfTt' i (Sum a) = usesOfTt' i a
-- usesOfTt' i (AdjPlus a b) = usesOfTt' i a <> usesOfTt' i b
usesOfTt' _ Zero = mempty
usesOfTt' i (LinFun f) = usesOfTtL i f

-- | Count the uses of the components of a variable in an expression in the linear sublanguage of the target language
usesOfTtL :: (Num s, Monoid s) => Idx env t -> LinTTerm env lenv b -> Layout t s
usesOfTtL i (LinApp term f) = usesOfTt' i term <> usesOfTtL i f
usesOfTtL i (LinApp' f term) = usesOfTtL i f <> usesOfTt' i term
usesOfTtL i (LinLam f) = usesOfTtL (S i) f
usesOfTtL i (LinLet f g) = usesOfTtL i f <> usesOfTtL i g
usesOfTtL _ (LinVar _) = mempty
usesOfTtL i (LinPair f g) = usesOfTtL i f <> usesOfTtL i g
usesOfTtL i (LinFst f) = usesOfTtL i f
usesOfTtL i (LinSnd f) = usesOfTtL i f
usesOfTtL i (LinLOp _ term arg) = usesOfTt' i term <> usesOfTtL i arg
usesOfTtL _ LinZero = mempty
usesOfTtL i (LinPlus f g) = usesOfTtL i f <> usesOfTtL i g
usesOfTtL i (LinSingleton term f) = usesOfTt' i term <> usesOfTtL i f
usesOfTtL i (LinCopowFold term f) = usesOfTt' i term <> usesOfTtL i f
usesOfTtL i (LinZip term f) = usesOfTt' i term <> usesOfTtL i f
usesOfTtL i (LinMap f term) = usesOfTtL i f <> usesOfTt' i term
usesOfTtL i (LinZipWith term term' f) = usesOfTt' i term <> usesOfTt' i term' <> usesOfTtL i f
usesOfTtL i (LinReplicate f) = usesOfTtL i f
usesOfTtL i (LinSum f) = usesOfTtL i f

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

usesOfLinVar :: (Num s, Monoid s) => Idx lenv t -> LinTTerm env lenv b -> Layout t s
usesOfLinVar i (LinApp _ f) = usesOfLinVar i f
usesOfLinVar i (LinApp' f _) = usesOfLinVar i f
usesOfLinVar i (LinLam f) = usesOfLinVar i f
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
usesOfLinVar i (LinZip _ f) = usesOfLinVar i f
usesOfLinVar i (LinMap f _) = usesOfLinVar i f
usesOfLinVar i (LinZipWith _ _ f) = usesOfLinVar i f
usesOfLinVar i (LinReplicate f) = usesOfLinVar i f
usesOfLinVar i (LinSum f) = usesOfLinVar i f
