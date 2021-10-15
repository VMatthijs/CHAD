{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Interpret a target-language program in a concrete language as defined in
-- "Concrete". This chooses an interpretation of the abstract copower
-- operations and forgets linearity of arrows. The transformation on types is
-- given by 'UnLin'.
module ToConcrete (
  toConcrete,
  UnLinEnv,
) where

import Concrete
import Env
import Operation
import TargetLanguage
import Types


type family UnLinEnv env where
  UnLinEnv '[] = '[]
  UnLinEnv (t ': ts) = UnLin t ': UnLinEnv ts

cvtUnLinIdx :: Idx env t -> Idx (UnLinEnv env) (UnLin t)
cvtUnLinIdx Z = Z
cvtUnLinIdx (S i) = S (cvtUnLinIdx i)

toConcrete :: TTerm env a -> CTerm (UnLinEnv env) (UnLin a)
toConcrete = toConcrete' wId

toConcrete' :: env :> denv -> TTerm env a -> CTerm (UnLinEnv denv) (UnLin a)
toConcrete' w = \case
  Var i -> CVar (cvtUnLinIdx (w >:> i))
  Lambda t -> CLambda (toConcrete' (wSink w) t)
  Let a b -> CLet (toConcrete' w a) (toConcrete' (wSink w) b)
  App a b -> CApp (toConcrete' w a) (toConcrete' w b)
  Unit -> CUnit
  Pair a b -> CPair (toConcrete' w a) (toConcrete' w b)
  Fst t -> CFst (toConcrete' w t)
  Snd t -> CSnd (toConcrete' w t)
  Op op t -> COp op (toConcrete' w t)
  Map a b -> CMap (toConcrete' w a) (toConcrete' w b)
  Map1 a b -> CMap (CLambda (toConcrete' (wSink w) a)) (toConcrete' w b)
  Replicate a -> CReplicate (toConcrete' w a)
  Sum a -> CSum (toConcrete' w a)
  LinFun f -> CLambda $ toConcreteL' (wSucc w) wOnlyOne f
    where
      wOnlyOne :: '[a] :> (a ': env)
      wOnlyOne = Weaken $ \case Z -> Z
                                S i -> case i of {}

toConcreteL' :: env :> denv
             -> lenv :> denv
             -> LinTTerm env lenv t
             -> CTerm (UnLinEnv denv) (UnLin t)
toConcreteL' w lw = \case
  LinVar i -> CVar (cvtUnLinIdx (lw >:> i))
  LinLam t -> CLambda (toConcreteL' (wSink w) (wSucc lw) t)
  LinLet a b -> CLet (toConcreteL' w lw a) (toConcreteL' (wSucc w) (wSink lw) b)
  LinApp a b -> CApp (toConcrete' w a) (toConcreteL' w lw b)
  LinApp' a b -> CApp (toConcreteL' w lw a) (toConcrete' w b)
  LinPair a b -> CPair (toConcreteL' w lw a) (toConcreteL' w lw b)
  LinFst t -> CFst (toConcreteL' w lw t)
  LinSnd t -> CSnd (toConcreteL' w lw t)
  LinLOp lop a b -> convLinOp lop (toConcrete' w a) (toConcreteL' w lw b)
  LinZero -> CZero
  LinPlus a b -> CPlus (toConcreteL' w lw a) (toConcreteL' w lw b)
  LinSingleton a b -> CLCons (CPair (toConcrete' w a) (toConcreteL' w lw b)) CLNil
  LinCopowFold f a -> CLSum (CLMap (CLambda $ sinkCt (wSucc wId) (toConcrete (sinkTt w f))
                                                `CApp` CFst (CVar Z)
                                                `CApp` CSnd (CVar Z))
                                   (toConcreteL' w lw a))
  LinZip a b -> CLZip (CToList (toConcrete' w a)) (CToList (toConcreteL' w lw b))
  LinMap f a -> CMap (toConcreteL' w lw f) (toConcrete' w a)
  LinZipWith f a b -> CZipWith (toConcrete' w f) (toConcrete' w a) (toConcreteL' w lw b)
  LinReplicate a -> CReplicate (toConcreteL' w lw a)
  LinSum a -> CSum (toConcreteL' w lw a)

convLinOp :: LinearOperation a b c -> CTerm env a -> CTerm env b -> CTerm env c
convLinOp LProd = CZipWith (CLambda $ CLambda $ COp EScalProd (CPair (CVar (S Z)) (CVar Z)))
convLinOp LReplicate = \_ -> CReplicate
convLinOp LScalNeg = \_ x -> COp EScalSubt (CPair (COp (Constant 0.0) CUnit) x)
convLinOp LScalProd = \x y -> COp EScalProd (CPair x y)
