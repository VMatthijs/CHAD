{-# LANGUAGE GADTs #-}

-- | Forward-AD Functions
module ForwardAD where

import           Operation                (LinearOperation (..), Operation (..))
import qualified SourceLanguage           as SL
import qualified TargetLanguage           as TL
import           TargetLanguage.Env       (Idx (..))
import           Types                    (Df1, Df2, LFun)

d1 :: SL.STerm a b -> TL.TTerm env (Df1 a -> Df1 b)
d1 SL.Id = TL.Lambda $ TL.Var Z
d1 (SL.Comp f g) = TL.Lambda $ TL.App (d1 g) (TL.App (d1 f) (TL.Var Z))
d1 SL.Unit = TL.Lambda TL.Unit
d1 (SL.Pair t s) = TL.Lambda $ TL.Pair (TL.App (d1 t) (TL.Var Z)) (TL.App (d1 s) (TL.Var Z))
d1 SL.Fst = TL.Lambda $ TL.Fst (TL.Var Z)
d1 SL.Snd = TL.Lambda $ TL.Snd (TL.Var Z)
-- \x -> fst ((fst x) (snd x))
d1 SL.Ev = TL.Lambda $ TL.Fst (TL.App (TL.Fst (TL.Var Z)) (TL.Snd (TL.Var Z)))
d1 (SL.Curry t) =
  let d1tTt = TL.App (d1 t) (TL.Pair (TL.Var (S Z)) (TL.Var Z))
      d2tTt = TL.App (d2 t) (TL.Pair (TL.Var (S Z)) (TL.Var Z))
  in TL.Lambda $ TL.Lambda $ TL.Pair d1tTt (TL.LComp (TL.LPair TL.Zero TL.LId) d2tTt)
d1 SL.Inl = TL.Lambda $ TL.Inl (TL.Var Z)
d1 SL.Inr = TL.Lambda $ TL.Inr (TL.Var Z)
d1 (SL.CoPair s t) = TL.Lambda $ TL.Case (TL.Var Z) (d1 s) (d1 t)
d1 (SL.Op op) = TL.Lambda $ TL.Op op (TL.Var Z)
d1 SL.Map =
  TL.Lambda $
    TL.Map (TL.Lambda $ TL.Fst $ TL.App (TL.Fst (TL.Var (S Z))) (TL.Var Z))
           (TL.Snd (TL.Var Z))
d1 SL.Foldr =
  TL.Lambda $
    TL.Foldr (TL.Lambda $ TL.Fst $
                TL.Fst (TL.Fst (TL.Var (S Z))) `TL.App` (TL.Var Z))
             (TL.Snd (TL.Fst (TL.Var Z)))
             (TL.Snd (TL.Var Z))
d1 (SL.Rec t) = TL.Rec (d1 t)
d1 (SL.It t) = TL.It (d1 t)
d1 SL.Sign = TL.Lambda $ TL.Sign (TL.Var Z)

d2 :: SL.STerm a b -> TL.TTerm env (Df1 a -> LFun (Df2 a) (Df2 b))
d2 SL.Id = TL.Lambda TL.LId
d2 (SL.Comp f g) =
  let d1fTt = TL.App (d1 f) (TL.Var Z)
      d2fTt = TL.App (d2 f) (TL.Var Z)
      d2gTt = TL.App (d2 g) d1fTt
  in TL.Lambda $ TL.LComp d2fTt d2gTt
d2 SL.Unit = TL.Zero
d2 (SL.Pair t s) =
  TL.Lambda $ TL.LPair (TL.App (d2 t) (TL.Var Z))
                    (TL.App (d2 s) (TL.Var Z))
d2 SL.Fst = TL.Lambda TL.LFst
d2 SL.Snd = TL.Lambda TL.LSnd
d2 SL.Ev =
  let y = TL.Snd (TL.Var Z)
      plusLhs = TL.LComp TL.LFst (TL.LEval y)
      plusRhs = TL.LComp TL.LSnd (TL.Snd (TL.App (TL.Fst (TL.Var Z)) y))
  in TL.Lambda $ TL.Plus plusLhs plusRhs
d2 (SL.Curry t) =
  let d2tTt = TL.App (d2 t) (TL.Pair (TL.Var (S Z)) (TL.Var Z))
  in TL.Lambda $ TL.LSwap $ TL.Lambda $ TL.LComp (TL.LPair TL.LId TL.Zero) d2tTt
d2 SL.Inl = TL.Lambda TL.LInl
d2 SL.Inr = TL.Lambda TL.LInr
d2 (SL.CoPair f g) =
  TL.Lambda $
    TL.Case
      (TL.Var Z)
      (TL.Lambda $
         TL.LCoPair (d2 f `TL.App` TL.Var Z) TL.Zero)
      (TL.Lambda $
         TL.LCoPair TL.Zero (d2 g `TL.App` TL.Var Z))
-- Map
-- x := (f, v)
-- y := (g, w)
d2 SL.Map = TL.Lambda $ TL.DMap (TL.Fst (TL.Var Z)) (TL.Snd (TL.Var Z))
d2 SL.Foldr =
  TL.Lambda $ TL.DFoldr
             (TL.Fst (TL.Fst (TL.Var Z)))
             (TL.Snd (TL.Fst (TL.Var Z)))
             (TL.Snd (TL.Var Z))
-- Dop
d2 (SL.Op (Constant _)) = TL.LOp DConstant
d2 (SL.Op EAdd) = TL.LOp DEAdd
d2 (SL.Op EProd) = TL.LOp DEProd
d2 (SL.Op EScalAdd) = TL.LOp DEScalAdd
d2 (SL.Op EScalSubt) = TL.LOp DEScalSubt
d2 (SL.Op EScalProd) = TL.LOp DEScalProd
d2 (SL.Op Sum) = TL.LOp DSum
d2 (SL.Rec t) =
  let body =
        d2 t `TL.App`
        TL.Pair (TL.Var Z) (TL.Rec (d1 t) `TL.App` TL.Var Z)
  in TL.Lambda $ TL.LRec body
d2 (SL.It t) = TL.DIt (d1 t) (d2 t)
d2 SL.Sign = TL.Lambda TL.Zero
