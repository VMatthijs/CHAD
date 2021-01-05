{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module ReverseAD where

import qualified SourceLanguage as SL
import qualified TargetLanguage as TL
import Types
import LanguageTypes

type family D1 a where
    D1 RealN    = RealN
    D1 (a -> b) = D1 a -> (D1 b, LFun (D2 b) (D2 a))
    D1 (a, b)   = (D1 a, D1 b)
    D1 ()       = ()

type family D2 a where
    D2 RealN    = RealN
    D2 (a -> b) = Tens (D1 a) (D2 b)
    D2 (a, b)   = (D2 a, D2 b)
    D2 ()       = ()

-- TODO: Gensym oid voor genereren lambda vars

d1 :: (LT (D1 a)) => SL.STerm a b -> TL.TTerm (D1 a -> D1 b)
d1  SL.Id        = TL.Lambda "x" inferType (TL.Var "x" inferType)
d1 (SL.Comp f g) = undefined -- TL.Comp (d1 f) (d1 g)
d1  SL.Unit      = TL.Lambda "_" inferType TL.Unit
d1 (SL.Pair f g) = undefined -- TL.Pair (d1 f) (d1 g)
d1  SL.Fst       = undefined -- TL.Fst
d1  SL.Snd       = undefined -- TL.Snd
-- x :: (D1 a -> (D1 b, LFun (D2 b) (D2 a)), D1 a)
-- Input:    STerm (a -> b, a) b
-- Expected: TTerm (D1 (a -> b, a)) (D1 b)
d1  SL.Ev        = undefined -- TL.Comp TL.Ev TL.Fst
-- t :: STerm (a, b) c  ==> d1 t :: TTerm (d1 (a, b)) (d1 c)
-- Input:    STerm a (b -> c)
-- Expected: TTerm (D1 a) (D1 (b -> c))

-- Comp z :: TTerm (D1 b1 -> D1 c) c0 -> TTerm (D1 a) c0
-- d1 (SL.Curry t)  = TL.Comp z (TL.Pair (d1 t) (TL.LComp (d2 t) TL.LSnd))
    -- where z = TL.Curry (d1 t)
d1 (SL.Op op)    = undefined -- TL.Op op ??


d2 :: (LT (D1 a), LT (D2 a)) => SL.STerm a b -> TL.TTerm (D1 a -> LFun (D2 b) (D2 a))
d2  SL.Id        = TL.Lambda "_" inferType TL.LId
d2 (SL.Comp f g) = TL.LComp undefined undefined--(TL.Comp (d1 f) (d2 g)) (d2 f)
d2  SL.Unit      = TL.Zero
d2 (SL.Pair t s) = undefined -- TL.Plus (TL.LComp TL.LFst (d2 t)) (TL.LComp TL.LSnd (d2 s))
d2  SL.Fst       = undefined -- TL.LPair TL.LId  TL.Zero
d2  SL.Snd       = undefined -- TL.LPair TL.Zero TL.LId
d2  SL.Ev        = undefined
d2 (SL.Curry t)  = undefined
d2 (SL.Op op)    = undefined
