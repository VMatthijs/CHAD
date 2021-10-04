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
  SLambda :: (LT2 a, LT2 b) => STerm (a ': env) b -> STerm env (a -> b)
  SLet :: (LT2 a, LT2 b) => STerm env a -> STerm (a ': env) b -> STerm env b
  SApp :: (LT2 a, LT2 b) => STerm env (a -> b) -> STerm env a -> STerm env b
  SUnit :: STerm env ()
  SPair :: (LT2 a, LT2 b) => STerm env a -> STerm env b -> STerm env (a, b)
  SFst :: (LT2 a, LT2 b) => STerm env (a, b) -> STerm env a
  SSnd :: (LT2 a, LT2 b) => STerm env (a, b) -> STerm env b
  SOp :: (a ~ Dr1 a, b ~ Dr1 b, LT2 a, LT2 b) => Operation a b -> STerm env a -> STerm env b

  SMap :: KnownNat n => STerm env (Scal -> Scal) -> STerm env (Vect n) -> STerm env (Vect n)
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
evalSt env (SReplicate x) = V.replicate (evalSt env x)
evalSt env (SSum v) = V.sum (evalSt env v)
