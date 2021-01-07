{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module ReverseAD where

import qualified SourceLanguage as SL
import qualified TargetLanguage as TL
import Types
import LanguageTypes

type family D1 a = r | r -> a where
    D1 RealN    = RealN
    D1 (a -> b) = D1 a -> (D1 b, LFun (D2 b) (D2 a))
    D1 (a, b)   = (D1 a, D1 b)
    D1 ()       = ()

type family D2 a = r | r -> a where
    D2 RealN    = RealN
    D2 (a -> b) = Tens (D1 a) (D2 b)
    D2 (a, b)   = (D2 a, D2 b)
    D2 ()       = ()

-- TODO: Gensym oid voor genereren lambda vars

d1 :: (LT a, LT b) => SL.STerm a b -> TL.TTerm (D1 a -> D1 b)
d1  SL.Id        = TL.Lambda "x" t (TL.Var "x" t)
    where t = inferType
d1 (SL.Comp f g) = TL.Lambda "x" t1 $ TL.substTt "y" d1f t2 d1g -- TL.Comp (d1 f) (d1 g)
    where t1  = inferType
          d1f = TL.App (d1 f) (TL.Var "x" t1)
          t2  = inferType
          d1g = TL.App (d1 g) (TL.Var "y" t2)
d1  SL.Unit      = TL.Lambda "_" inferType TL.Unit
d1 (SL.Pair f g) = undefined -- TL.Lambda "x" t $ TL.Pair fstPair sndPair
    -- where t = inferType
          -- fstPair = TL.App (d1 f) (TL.Var "x" t)
          -- sndPair = TL.App (d1 g) (TL.Var "x" t)
d1  SL.Fst       = TL.Lambda "x" t $ TL.Fst (TL.Var "x" t)
    where t = inferType
d1  SL.Snd       = TL.Lambda "x" t $ TL.Snd (TL.Var "x" t)
    where t = inferType
-- \x -> fst ((fst x) (snd x))
d1 SL.Ev         = TL.Lambda "x" t $ TL.Fst (TL.App (TL.Fst (TL.Var "x" t)) (TL.Snd (TL.Var "x" t)))
    where t = inferType
-- t :: STerm (a, b) c  ==> d1 t :: TTerm (d1 (a, b)) (d1 c)
-- Input:    STerm a (b -> c)
-- Expected: TTerm (D1 a) (D1 (b -> c))

-- Comp z :: TTerm (D1 b1 -> D1 c) c0 -> TTerm (D1 a) c0
-- d1 (SL.Curry t)  = TL.Comp z (TL.Pair (d1 t) (TL.LComp (d2 t) TL.LSnd))
    -- where z = TL.Curry (d1 t)
d1 (SL.Op op)    = TL.Lambda "x" inferType $ TL.Op op (TL.Var "x" inferType) -- TL.Op op ??


d2 :: (LT a, LT b) => SL.STerm a b -> TL.TTerm (D1 a -> LFun (D2 b) (D2 a))
d2  SL.Id        = TL.Lambda "_" inferType TL.LId
d2 (SL.Comp f g) = TL.LComp undefined undefined--(TL.Comp (d1 f) (d2 g)) (d2 f)
d2  SL.Unit      = TL.Zero
d2 (SL.Pair t s) = undefined -- TL.Plus (TL.LComp TL.LFst (d2 t)) (TL.LComp TL.LSnd (d2 s))
d2  SL.Fst       = TL.Lambda "x" inferType $ TL.LPair TL.LId  TL.Zero
d2  SL.Snd       = TL.Lambda "x" inferType $ TL.LPair TL.Zero TL.LId
d2  SL.Ev        = TL.Lambda "x" t $ TL.LPair (TL.Singleton y) z
    where t = inferType
          x = TL.Var "x" t
          y = TL.Snd x
          z = TL.Snd (TL.App (TL.Fst x) y)
d2 (SL.Curry t)  = undefined
d2 (SL.Op op)    = undefined
