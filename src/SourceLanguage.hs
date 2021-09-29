{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeOperators    #-}

-- | Definition of the source language
module SourceLanguage where

import Data.Vector.Unboxed.Sized as V (map)
import GHC.TypeNats              (KnownNat)

import Env
import Operation
import Type
import Types

-- | Terms of the source language
data STerm env a where
  SVar :: Type a -> Idx env a -> STerm env a
  SLambda :: Type a -> STerm (a ': env) b -> STerm env (a -> b)
  SLet :: STerm env a -> STerm (a ': env) b -> STerm env b
  SApp :: STerm env (a -> b) -> STerm env a -> STerm env b
  SUnit :: STerm env ()
  SPair :: STerm env a -> STerm env b -> STerm env (a, b)
  SFst :: STerm env (a, b) -> STerm env a
  SSnd :: STerm env (a, b) -> STerm env b
  SOp :: Type b -> Operation a b -> STerm env a -> STerm env b

  SMap :: KnownNat n => STerm env (Scal -> Scal) -> STerm env (Vect n) -> STerm env (Vect n)

-- | Evaluate the source language
evalSt :: Val env -> STerm env t -> t
evalSt env (SVar _ i) = valProject env i
evalSt env (SLambda _ e) = \v -> evalSt (VS v env) e
evalSt env (SLet rhs e) = evalSt (VS (evalSt env rhs) env) e
evalSt env (SApp f a) = evalSt env f (evalSt env a)
evalSt _   SUnit = ()
evalSt env (SPair a b) = (evalSt env a, evalSt env b)
evalSt env (SFst p) = fst $ evalSt env p
evalSt env (SSnd p) = snd $ evalSt env p
evalSt env (SOp _ op a) = evalOp op (evalSt env a)
evalSt env (SMap a b) = V.map (evalSt env a) (evalSt env b)

typeofSt :: STerm env t -> Type t
typeofSt (SVar t _) = t
typeofSt (SLambda t e) = TFun t (typeofSt e)
typeofSt (SLet _ e) = typeofSt e
typeofSt (SApp a _) = let TFun _ t = typeofSt a in t
typeofSt SUnit = TNil
typeofSt (SPair a b) = TPair (typeofSt a) (typeofSt b)
typeofSt (SFst e) = let TPair t _ = typeofSt e in t
typeofSt (SSnd e) = let TPair _ t = typeofSt e in t
typeofSt (SOp t _ _) = t
typeofSt (SMap _ _) = TVect
