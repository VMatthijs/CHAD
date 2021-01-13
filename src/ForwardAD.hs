{-# LANGUAGE GADTs #-}
module ForwardAD where

import qualified SourceLanguage as SL
import qualified TargetLanguage as TL
import Types
import LanguageTypes
import Operation


d1 :: SL.STerm a b -> TL.TTerm (Df1 a -> Df1 b)
d1  SL.Id        = TL.Lambda "x" t (TL.Var "x" t)
    where t = inferType
d1 (SL.Comp f g) = TL.Lambda "x" t1 $ TL.substTt "y" d1f t2 d1g
    where t1  = inferType
          d1f = TL.App (d1 f) (TL.Var "x" t1)
          t2  = inferType
          d1g = TL.App (d1 g) (TL.Var "y" t2)
d1  SL.Unit      = TL.Lambda "_" inferType TL.Unit
d1 (SL.Pair t s) = TL.Lambda "x" varType $ TL.Pair fstPair sndPair
    where varType = inferType
          fstPair = TL.App (d1 t) (TL.Var "x" varType)
          sndPair = TL.App (d1 s) (TL.Var "x" varType)
d1  SL.Fst       = TL.Lambda "x" t $ TL.Fst (TL.Var "x" t)
    where t = inferType
d1  SL.Snd       = TL.Lambda "x" t $ TL.Snd (TL.Var "x" t)
    where t = inferType
-- \x -> fst ((fst x) (snd x))
d1  SL.Ev        = TL.Lambda "x" t $ TL.Fst (TL.App (TL.Fst x) (TL.Snd x))
    where t = inferType
          x = TL.Var "x" t
d1 (SL.Curry t)  = TL.Lambda "x" xType $ TL.Lambda "y" yType $ TL.Pair d1t sndPair
    where xType   = inferType
          yType   = inferType
          d1t     = TL.App (d1 t) (TL.Pair (TL.Var "x" xType) (TL.Var "y" yType))
          d2t     = TL.App (d2 t) (TL.Pair (TL.Var "x" xType) (TL.Var "y" yType))
          sndPair = TL.LComp (TL.LPair TL.Zero TL.LId) d2t
d1 (SL.Op op)    = TL.Lambda "x" t $ TL.Op op (TL.Var "x" t)
    where t = inferType


d2 :: SL.STerm a b -> TL.TTerm (Df1 a -> LFun (Df2 a) (Df2 b))
d2  SL.Id        = TL.Lambda "_" inferType TL.LId
d2 (SL.Comp f g) = TL.Lambda "x" xType $ TL.LComp d2f d2g
    where xType = inferType
          d1f = TL.App (d1 f) (TL.Var "x" xType)
          d2f = TL.App (d2 f) (TL.Var "x" xType)
          d2g = TL.App (d2 g) d1f
d2  SL.Unit      = TL.Zero
d2 (SL.Pair t s) = TL.Lambda "x" varType $ TL.LPair fstPair sndPair
    where varType = inferType
          fstPair = TL.App (d2 t) (TL.Var "x" varType)
          sndPair = TL.App (d2 s) (TL.Var "x" varType)
d2  SL.Fst       = TL.Lambda "_" inferType TL.LFst
d2  SL.Snd       = TL.Lambda "_" inferType TL.LSnd
d2  SL.Ev        = TL.Lambda "x" xType $ TL.Plus plusLhs plusRhs
    where xType = inferType
          y     = TL.Snd (TL.Var "x" xType)
          plusLhs = TL.LComp TL.LFst (TL.LEval y)
          -- LSnd ;; Snd ((Fst x) y)
          plusRhs = TL.LComp TL.LSnd (TL.Snd (TL.App (TL.Fst (TL.Var "x" xType)) y))
d2 (SL.Curry t)  = TL.Lambda "x" xType $ TL.LSwap $ TL.Lambda "y" yType $
                   TL.LComp (TL.LPair TL.LId TL.Zero) d2t
    where xType = inferType
          yType = inferType
          d2t   = TL.App (d2 t) (TL.Pair (TL.Var "x" xType) (TL.Var "y" yType))
-- Dop
d2 (SL.Op (Constant _)) = TL.LOp DConstant
d2 (SL.Op EAdd   )      = TL.LOp DEAdd
d2 (SL.Op EProd  )      = TL.LOp DEProd
d2 (SL.Op MProd  )      = undefined -- undefined
d2 (SL.Op Sum    )      = undefined -- [1, 1, 1, 1, ...]
d2 (SL.Op Sigmoid)      = undefined --TL.Lambda "x" inferType (TL.Op (DSigmoid))
