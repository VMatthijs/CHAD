{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module ToConcrete where

import Concrete
import Env
import Operation
import TargetLanguage
import Types


type family UnLinEnv env where
  UnLinEnv '[] = '[]
  UnLinEnv (t ': ts) = UnLin t ': UnLinEnv ts

type family Append as bs where
  Append '[] bs = bs
  Append (a ': as) bs = a ': Append as bs

cvtUnLinIdx :: Idx env t -> Idx (UnLinEnv env) (UnLin t)
cvtUnLinIdx Z = Z
cvtUnLinIdx (S i) = S (cvtUnLinIdx i)

subIdx :: forall env' env t. Idx env t -> Idx (Append env env') t
subIdx Z = Z
subIdx (S i) = S (subIdx @env' i)

toConcrete :: TTerm env a -> CTerm (UnLinEnv env) (UnLin a)
toConcrete = \case
  Var i -> CVar (cvtUnLinIdx i)
  Lambda t -> CLambda (toConcrete t)
  Let a b -> CLet (toConcrete a) (toConcrete b)
  App a b -> CApp (toConcrete a) (toConcrete b)
  Unit -> CUnit
  Pair a b -> CPair (toConcrete a) (toConcrete b)
  Fst t -> CFst (toConcrete t)
  Snd t -> CSnd (toConcrete t)
  Op op t -> COp op (toConcrete t)
  Map a b -> CMap (toConcrete a) (toConcrete b)
  Replicate a -> CReplicate (toConcrete a)
  Sum a -> CSum (toConcrete a)
  Zero -> CZero
  LinFun f -> toConcreteL f

toConcreteL :: LinTTerm env '[a] b -> CTerm (UnLinEnv env) (UnLin a -> UnLin b)
toConcreteL = CLambda . toConcreteL' (wSucc wId)

toConcreteL' :: forall env lenv t. env :> Append lenv env -> LinTTerm env lenv t -> CTerm (UnLinEnv (Append lenv env)) (UnLin t)
toConcreteL' w = \case
  LinVar i -> CVar (cvtUnLinIdx (subIdx @env i))
  LinLet a b -> CLet (toConcreteL' w a) (toConcreteL' (wSucc w) b)
  LinApp a b -> CApp (toConcrete (sinkTt w a)) (toConcreteL' w b)
  LinPair a b -> CPair (toConcreteL' w a) (toConcreteL' w b)
  LinFst t -> CFst (toConcreteL' w t)
  LinSnd t -> CSnd (toConcreteL' w t)
  LinLOp lop a b -> convLinOp lop (toConcrete (sinkTt w a)) (toConcreteL' w b)
  LinZero -> CZero
  LinPlus a b -> CPlus (toConcreteL' w a) (toConcreteL' w b)
  LinSingleton a b -> CLCons (CPair (toConcrete (sinkTt w a)) (toConcreteL' w b)) CLNil
  LinCopowFold f a -> CLSum (CLMap (CLambda $ sinkCt (wSucc wId) (toConcrete (sinkTt w f))
                                                `CApp` CFst (CVar Z)
                                                `CApp` CSnd (CVar Z))
                                   (toConcreteL' w a))
  LinZip a b -> CLZip (CToList (toConcrete (sinkTt w a))) (CToList (toConcreteL' w b))
  LinZipWith f a b -> CZipWith (toConcrete (sinkTt w f)) (toConcrete (sinkTt w a)) (toConcreteL' w b)
  LinReplicate a -> CReplicate (toConcreteL' w a)
  LinSum a -> CSum (toConcreteL' w a)

convLinOp :: LinearOperation a b c -> CTerm env a -> CTerm env b -> CTerm env c
convLinOp LProd = CZipWith (CLambda $ CLambda $ COp EScalProd (CPair (CVar (S Z)) (CVar Z)))
convLinOp LReplicate = \_ -> CReplicate
convLinOp LScalNeg = \_ x -> COp EScalSubt (CPair (COp (Constant 0.0) CUnit) x)
convLinOp LScalProd = \x y -> COp EScalProd (CPair x y)
