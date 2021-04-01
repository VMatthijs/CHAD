{-# LANGUAGE GADTs #-}

-- | Reverse-AD functions
module ReverseAD where

import           Operation          (LinearOperation (..), Operation (..))
import qualified SourceLanguage     as SL
import qualified TargetLanguage     as TL
import           TargetLanguage.Env (Idx (..))
import           Types              (Dr1, Dr2, LFun)

-- | Primal calculation (forward pass)
d1 :: SL.STerm a b -> TL.TTerm env (Dr1 a -> Dr1 b)
d1 SL.Id = TL.Lambda $ TL.Var Z
d1 (SL.Comp f g) = TL.Lambda $ TL.App (d1 g) (TL.App (d1 f) (TL.Var Z))
d1 SL.Unit = TL.Lambda TL.Unit
d1 (SL.Pair t s) =
  TL.Lambda $ TL.Pair (TL.App (d1 t) (TL.Var Z)) (TL.App (d1 s) (TL.Var Z))
d1 SL.Fst = TL.Lambda $ TL.Fst (TL.Var Z)
d1 SL.Snd = TL.Lambda $ TL.Snd (TL.Var Z)
-- \x -> fst ((fst x) (snd x))
d1 SL.Ev = TL.Lambda $ TL.Fst (TL.App (TL.Fst (TL.Var Z)) (TL.Snd (TL.Var Z)))
d1 (SL.Curry t) =
  let d1tTt = TL.App (d1 t) (TL.Pair (TL.Var (S Z)) (TL.Var Z))
      d2tTt = TL.App (d2 t) (TL.Pair (TL.Var (S Z)) (TL.Var Z))
   in TL.Lambda $ TL.Lambda $ TL.Pair d1tTt (TL.LComp d2tTt TL.LSnd)
d1 SL.Inl = TL.Lambda $ TL.Inl (TL.Var Z)
d1 SL.Inr = TL.Lambda $ TL.Inr (TL.Var Z)
d1 (SL.CoPair s t) = TL.Lambda $ TL.Case (TL.Var Z) (d1 s) (d1 t)
d1 (SL.Op op) = TL.Lambda $ TL.Op op (TL.Var Z)
-- x := (\y -> (f(y), g(y)), v)
-- Map :: (Scal -> Scal, Vect n) -> Vect n
-- d1 :: (Scal -> (Scal, LFun Scal Scal), Vect n) -> Vect n
d1 SL.Map =
  TL.Lambda $
  TL.Map
    (TL.Lambda $ TL.Fst (TL.Fst (TL.Var (S Z)) `TL.App` TL.Var Z))
    (TL.Snd (TL.Var Z))
-- Foldr :: ((Scal, a) -> a, a, Vect n) -> a
-- d1 Foldr :: ((Scal, D1 a) -> (D1 a, LFun (D2 a) (Scal, D2 a)), D1 a, Vect n) -> D1 a
d1 SL.Foldr =
  TL.Lambda $
  TL.Foldr
    (TL.Lambda $ TL.Fst $ TL.Fst (TL.Fst (TL.Var (S Z))) `TL.App` TL.Var Z)
    (TL.Snd (TL.Fst (TL.Var Z)))
    (TL.Snd (TL.Var Z))
d1 (SL.Rec t) = TL.Rec (d1 t)
d1 (SL.It t) = TL.It (d1 t)
d1 SL.Sign = TL.Lambda $ TL.Sign (TL.Var Z)

-- | Cotangent (aka adjoint sensitivity) calculation (reverse pass)
d2 :: SL.STerm a b -> TL.TTerm env (Dr1 a -> LFun (Dr2 b) (Dr2 a))
d2 SL.Id = TL.Lambda TL.LId
d2 (SL.Comp f g) =
  let d2fTt = TL.App (d2 f) (TL.Var Z)
      d2gTt = TL.App (d2 g) (TL.App (d1 f) (TL.Var Z))
   in TL.Lambda $ TL.LComp d2gTt d2fTt
d2 SL.Unit = TL.Zero
d2 (SL.Pair t s) =
  let x = TL.LComp TL.LFst (TL.App (d2 t) (TL.Var Z))
      y = TL.LComp TL.LSnd (TL.App (d2 s) (TL.Var Z))
   in TL.Lambda $ TL.Plus x y
d2 SL.Fst = TL.Lambda $ TL.LPair TL.LId TL.Zero
d2 SL.Snd = TL.Lambda $ TL.LPair TL.Zero TL.LId
d2 SL.Ev =
  let x = TL.Var Z
      y = TL.Snd x
      z = TL.Snd (TL.App (TL.Fst x) y)
   in TL.Lambda $ TL.LPair (TL.Singleton y) z
d2 (SL.Curry t) =
  let d2tTt = TL.App (d2 t) (TL.Pair (TL.Var (S Z)) (TL.Var Z))
      cur = TL.LCopowFold $ TL.Lambda d2tTt
   in TL.Lambda $ TL.LComp cur TL.LFst
d2 SL.Inl =
  TL.Lambda $
  TL.LCoPair TL.LId (TL.Error "Incompatible primal and cotangent to coproduct.")
d2 SL.Inr =
  TL.Lambda $
  TL.LCoPair (TL.Error "Incompatible primal and cotangent to coproduct.") TL.LId
d2 (SL.CoPair f g) =
  TL.Lambda $
  TL.Case
    (TL.Var Z)
    (TL.Lambda $ (d2 f `TL.App` TL.Var Z) `TL.LComp` TL.LInl)
    (TL.Lambda $ (d2 g `TL.App` TL.Var Z) `TL.LComp` TL.LInr)
-- Map
-- Map :: (Scal -> Scal, Vect n) -> Vect n
-- d2 Map :: (Scal -> (Scal, LFun Scal Scal), Vect n) -> LFun (Vect n) (Copower Scal Scal, Vect n)
d2 SL.Map = TL.Lambda $ TL.DtMap (TL.Fst (TL.Var Z)) (TL.Snd (TL.Var Z))
-- Foldr :: ((Scal, a) -> a, a, Vect n) -> a
-- d2 Foldr :: ((Scal, D1 a) -> (D1 a, LFun (D2 a) (Scal, D2 a)), D1 a, Vect n) -> LFun (D2 a) (Copower (Scal, D1 a) (D2 a), D2 a ,Vect n)
d2 SL.Foldr =
  TL.Lambda $
  TL.DtFoldr
    (TL.Fst (TL.Fst (TL.Var Z)))
    (TL.Snd (TL.Fst (TL.Var Z)))
    (TL.Snd (TL.Var Z))
-- Dop^t
d2 (SL.Op (Constant _)) = TL.LOp DConstantT
d2 (SL.Op EAdd) = TL.LOp DEAddT
d2 (SL.Op EProd) = TL.LOp DEProdT
d2 (SL.Op EScalAdd) = TL.LOp DEScalAddT
d2 (SL.Op EScalSubt) = TL.LOp DEScalSubtT
d2 (SL.Op EScalProd) = TL.LOp DEScalProdT
d2 (SL.Op Sum) = TL.LOp DSumT -- [1, 1, 1, 1, ...]
d2 (SL.Rec t) =
  let body = d2 t `TL.App` TL.Pair (TL.Var Z) (TL.Rec (d1 t) `TL.App` TL.Var Z)
   in TL.Lambda $ TL.LIt body
d2 (SL.It t) = TL.DtIt (d1 t) (d2 t)
d2 SL.Sign = TL.Lambda TL.Zero
