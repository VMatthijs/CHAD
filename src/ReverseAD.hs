{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module ReverseAD where

import qualified SourceLanguage as SL
import qualified TargetLanguage as TL
import Types
import LanguageTypes
import Operation
import GHC.TypeNats

-- TODO: Gensym oid voor genereren lambda vars

d1 :: SL.STerm a b -> TL.TTerm (Dr1 a -> Dr1 b)
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
d1 (SL.Curry t)  = TL.Lambda "x" xType $ TL.Lambda "y" yType $
                   TL.Pair d1t (TL.LComp d2t TL.LSnd)
    where xType  = inferType
          yType  = inferType
          d1t    = TL.App (d1 t) (TL.Pair (TL.Var "x" xType) (TL.Var "y" yType))
          d2t    = TL.App (d2 t) (TL.Pair (TL.Var "x" xType) (TL.Var "y" yType))
d1 (SL.Op op)    = TL.Lambda "x" t $ TL.Op op (TL.Var "x" t)
    where t = inferType
-- x := (f, v)
d1  SL.Map       = TL.Lambda "x" xType $ TL.Map f v
    where xType = inferType
          yType = inferType
          f = TL.Lambda "y" yType $ TL.Fst $ TL.App (TL.Fst (TL.Var "x" xType)) (TL.Var "y" yType)
          v = TL.Snd (TL.Var "x" xType)


d2 :: SL.STerm a b -> TL.TTerm (Dr1 a -> LFun (Dr2 b) (Dr2 a))
d2  SL.Id        = TL.Lambda "_" inferType TL.LId
d2 (SL.Comp f g) = TL.Lambda "x" t1 $ TL.LComp (TL.substTt "y" d1f t2 d2g) d2f
    where t1  = inferType
          d1f = TL.App (d1 f) (TL.Var "x" t1)
          d2f = TL.App (d2 f) (TL.Var "x" t1)
          t2  = inferType
          d2g = TL.App (d2 g) (TL.Var "y" t2)
d2  SL.Unit      = TL.Zero
d2 (SL.Pair t s) = TL.Lambda "x" varType $ TL.Plus x y
    where varType = inferType
          x       = TL.LComp TL.LFst (TL.App (d2 t) (TL.Var "x" varType))
          y       = TL.LComp TL.LSnd (TL.App (d2 s) (TL.Var "x" varType))
d2  SL.Fst       = TL.Lambda "x" inferType $ TL.LPair TL.LId  TL.Zero
d2  SL.Snd       = TL.Lambda "x" inferType $ TL.LPair TL.Zero TL.LId
d2  SL.Ev        = TL.Lambda "x" t $ TL.LPair (TL.Singleton y) z
    where t = inferType
          x = TL.Var "x" t
          y = TL.Snd x
          z = TL.Snd (TL.App (TL.Fst x) y)
d2 (SL.Curry t)  = TL.Lambda "x" xType $ TL.LComp cur TL.LFst
    where xType = inferType
          yType = inferType
          cur   = TL.LCur $ TL.Lambda "y" yType d2t
          d2t   = TL.App (d2 t) (TL.Pair (TL.Var "x" xType) (TL.Var "y" yType))
-- Map
-- x := (f, v)
-- y := w
d2  SL.Map       = TL.Lambda "x" xType $ TL.Lambda "y" yType
                 $ TL.Pair (TL.Zip v w) (TL.ZipWith f v w)
    where xType = inferType
          yType = inferType
          zType = inferType
          f     = TL.Lambda "z" zType $ TL.Snd
                $ TL.App (TL.Fst (TL.Var "x" xType)) (TL.Var "z" zType)
          v     = TL.Snd (TL.Var "x" xType)
          w     = TL.Var "y" yType
-- Dop^t
d2 (SL.Op (Constant _)) = TL.LOp DConstantT
d2 (SL.Op EAdd   )      = TL.LOp DEAddT
d2 (SL.Op EProd  )      = TL.LOp DEProdT
d2 (SL.Op MProd  )      = undefined -- undefined
d2 (SL.Op Sum    )      = TL.LOp DSumT -- [1, 1, 1, 1, ...]
d2 (SL.Op Sigmoid)      = undefined --TL.Lambda "x" inferType (TL.Op (DSigmoid))
