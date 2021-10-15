{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}

-- | Definition of the source language
module SourceLanguage where

import Data.Vector.Unboxed.Sized as V (map, replicate, sum)
import GHC.TypeNats              (KnownNat)

import Env
import Operation
import Types

-- | Terms of the source language
data STerm env a where
  SVar :: LT2 a => Idx env a -> STerm env a
  SLambda :: (LT2U a, LT2 b) => STerm (a ': env) b -> STerm env (a -> b)
  SLet :: (LT2U a, LT2 b) => STerm env a -> STerm (a ': env) b -> STerm env b
  SApp :: (LT2 a, LT2U b) => STerm env (a -> b) -> STerm env a -> STerm env b
  SUnit :: STerm env ()
  SPair :: (LT2 a, LT2 b) => STerm env a -> STerm env b -> STerm env (a, b)
  SFst :: (LT2 a, LT2U b) => STerm env (a, b) -> STerm env a
  SSnd :: (LT2U a, LT2 b) => STerm env (a, b) -> STerm env b
  SOp :: (a ~ Df1 a, b ~ Df1 b, a ~ Dr1 a, b ~ Dr1 b, a ~ UnLin a, b ~ UnLin b, LT2 a, LT2 b, LT (UnLin (Df2 b))) => Operation a b -> STerm env a -> STerm env b

  SMap :: KnownNat n => STerm env (Scal -> Scal) -> STerm env (Vect n) -> STerm env (Vect n)
  SMap1 :: KnownNat n => STerm (Scal ': env) Scal -> STerm env (Vect n) -> STerm env (Vect n)
  SReplicate :: KnownNat n => STerm env Scal -> STerm env (Vect n)
  SSum :: KnownNat n => STerm env (Vect n) -> STerm env Scal

deriving instance Show (STerm env a)

-- | Evaluate the source language
evalSt :: Val env -> STerm env t -> t
evalSt env (SVar i) = valProject env i
evalSt env (SLambda e) = \v -> evalSt (VS v env) e
evalSt env (SLet rhs e) = evalSt (VS (evalSt env rhs) env) e
evalSt env (SApp f a) = evalSt env f (evalSt env a)
evalSt _   SUnit = ()
evalSt env (SPair a b) = (evalSt env a, evalSt env b)
evalSt env (SFst p) = fst $ evalSt env p
evalSt env (SSnd p) = snd $ evalSt env p
evalSt env (SOp op a) = evalOp op (evalSt env a)
evalSt env (SMap a b) = V.map (evalSt env a) (evalSt env b)
evalSt env (SMap1 a b) = V.map (\v -> evalSt (VS v env) a) (evalSt env b)
evalSt env (SReplicate x) = V.replicate (evalSt env x)
evalSt env (SSum v) = V.sum (evalSt env v)

sinkSt :: env :> env' -> STerm env t -> STerm env' t
sinkSt w (SVar i)       = SVar (w >:> i)
sinkSt w (SLambda e)    = SLambda (sinkSt (wSink w) e)
sinkSt w (SLet rhs e)   = SLet (sinkSt w rhs) (sinkSt (wSink w) e)
sinkSt w (SApp e1 e2)   = SApp (sinkSt w e1) (sinkSt w e2)
sinkSt _ SUnit          = SUnit
sinkSt w (SPair a b)    = SPair (sinkSt w a) (sinkSt w b)
sinkSt w (SFst p)       = SFst (sinkSt w p)
sinkSt w (SSnd p)       = SSnd (sinkSt w p)
sinkSt w (SOp op a)     = SOp op (sinkSt w a)
sinkSt w (SMap a b)     = SMap (sinkSt w a) (sinkSt w b)
sinkSt w (SMap1 a b)    = SMap1 (sinkSt (wSink w) a) (sinkSt w b)
sinkSt w (SReplicate x) = SReplicate (sinkSt w x)
sinkSt w (SSum a)       = SSum (sinkSt w a)

sinkSt1 :: STerm env t -> STerm (a ': env) t
sinkSt1 = sinkSt (wSucc wId)
