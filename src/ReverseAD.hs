{-# LANGUAGE GADTs #-}

-- | Reverse-AD functions
module ReverseAD where

import           Control.Monad.State.Lazy (State)

import           Helper                   (gensym)
import           Operation                (LinearOperation (..), Operation (..))
import qualified SourceLanguage           as SL
import qualified TargetLanguage           as TL
import           Types                    (Dr1, Dr2, LFun, LT (inferType))

d1 :: SL.STerm a b -> State Integer (TL.TTerm (Dr1 a -> Dr1 b))
d1 SL.Id = do
  xVar <- gensym
  return $ TL.Lambda xVar t (TL.Var xVar t)
  where
    t = inferType
d1 (SL.Comp f g) = do
  xVar <- gensym
  yVar <- gensym
  d1f <- d1 f
  d1g <- d1 g
  let d1fTt = TL.App d1f (TL.Var xVar t1)
  let d1gTt = TL.App d1g (TL.Var yVar t2)
  return $ TL.Lambda xVar t1 $ TL.substTt yVar d1fTt t2 d1gTt
  where
    t1 = inferType
    t2 = inferType
d1 SL.Unit = return $ TL.Lambda "_" inferType TL.Unit
d1 (SL.Pair t s) = do
  xVar <- gensym
  d1t <- d1 t
  d1s <- d1 s
  let fstPair = TL.App d1t (TL.Var xVar varType)
  let sndPair = TL.App d1s (TL.Var xVar varType)
  return $ TL.Lambda xVar varType $ TL.Pair fstPair sndPair
  where
    varType = inferType
d1 SL.Fst = do
  xVar <- gensym
  return $ TL.Lambda xVar t $ TL.Fst (TL.Var xVar t)
  where
    t = inferType
d1 SL.Snd = do
  xVar <- gensym
  return $ TL.Lambda xVar t $ TL.Snd (TL.Var xVar t)
  where
    t = inferType
-- \x -> fst ((fst x) (snd x))
d1 SL.Ev = do
  xVar <- gensym
  let x = TL.Var xVar t
  return $ TL.Lambda xVar t $ TL.Fst (TL.App (TL.Fst x) (TL.Snd x))
  where
    t = inferType
d1 (SL.Curry t) = do
  xVar <- gensym
  yVar <- gensym
  d1t <- d1 t
  d2t <- d2 t
  let d1tTt = TL.App d1t (TL.Pair (TL.Var xVar xType) (TL.Var yVar yType))
  let d2tTt = TL.App d2t (TL.Pair (TL.Var xVar xType) (TL.Var yVar yType))
  return $
    TL.Lambda xVar xType $
    TL.Lambda yVar yType $ TL.Pair d1tTt (TL.LComp d2tTt TL.LSnd)
  where
    xType = inferType
    yType = inferType
d1 SL.Inl = do
  xVar <- gensym
  return $ TL.Lambda xVar t $ TL.Inl (TL.Var xVar t) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  where
    t = inferType
d1 SL.Inr = do
  xVar <- gensym
  return $ TL.Lambda xVar t $ TL.Inr (TL.Var xVar t) -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  where
    t = inferType
d1 (SL.CoPair s t) = do
  yVar <- gensym
  d1t <- d1 t
  d1s <- d1 s
  return $ TL.Lambda yVar yType $ TL.Case (TL.Var yVar yType) d1s d1t -- EXPERIMENTAL SUPPORT FOR SUM TYPES
  where
    yType = inferType
d1 (SL.Op op) = do
  xVar <- gensym
  return $ TL.Lambda xVar t $ TL.Op op (TL.Var xVar t)
  where
    t = inferType
-- x := (f, v)
d1 SL.Map = do
  xVar <- gensym
  yVar <- gensym
  let f =
        TL.Lambda yVar yType $
        TL.Fst $ TL.App (TL.Fst (TL.Var xVar xType)) (TL.Var yVar yType)
  let v = TL.Snd (TL.Var xVar xType)
  return $ TL.Lambda xVar xType $ TL.Map f v
  where
    xType = inferType
    yType = inferType
d1 SL.Foldr = do
  xVar <- gensym
  yVar <- gensym
  let xType = inferType
  let yType = inferType
  return $
    TL.Lambda
      xVar
      xType
      (TL.Foldr `TL.App`
       TL.Pair
         (TL.Pair
            (TL.Lambda yVar yType $
             TL.Fst
               (TL.Fst (TL.Fst (TL.Var xVar xType)) `TL.App` (TL.Var yVar yType)))
            (TL.Snd (TL.Fst (TL.Var xVar xType))))
         (TL.Snd (TL.Var xVar xType)))
d1 (SL.Rec t) = do
  d1t <- d1 t -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION
  return $ TL.Rec d1t
d1 (SL.It t) = do
  d1t <- d1 t -- EXPERIMENTAL SUPPORT FOR ITERATION
  return $ TL.It d1t

d2 :: SL.STerm a b -> State Integer (TL.TTerm (Dr1 a -> LFun (Dr2 b) (Dr2 a)))
d2 SL.Id = return $ TL.Lambda "_" inferType TL.LId
d2 (SL.Comp f g) = do
  xVar <- gensym
  yVar <- gensym
  d1f <- d1 f
  d2f <- d2 f
  d2g <- d2 g
  let d1fTt = TL.App d1f (TL.Var xVar t1)
  let d2fTt = TL.App d2f (TL.Var xVar t1)
  let d2gTt = TL.App d2g (TL.Var yVar t2)
  return $ TL.Lambda xVar t1 $ TL.LComp (TL.substTt yVar d1fTt t2 d2gTt) d2fTt
  where
    t1 = inferType
    t2 = inferType
d2 SL.Unit = return TL.Zero
d2 (SL.Pair t s) = do
  xVar <- gensym
  d2t <- d2 t
  d2s <- d2 s
  let x = TL.LComp TL.LFst (TL.App d2t (TL.Var xVar varType))
  let y = TL.LComp TL.LSnd (TL.App d2s (TL.Var xVar varType))
  return $ TL.Lambda xVar varType $ TL.Plus x y
  where
    varType = inferType
d2 SL.Fst = return $ TL.Lambda "_" inferType $ TL.LPair TL.LId TL.Zero
d2 SL.Snd = return $ TL.Lambda "_" inferType $ TL.LPair TL.Zero TL.LId
d2 SL.Ev = do
  xVar <- gensym
  let x = TL.Var xVar t
  let y = TL.Snd x
  let z = TL.Snd (TL.App (TL.Fst x) y)
  return $ TL.Lambda xVar t $ TL.LPair (TL.Singleton y) z
  where
    t = inferType
d2 (SL.Curry t) = do
  xVar <- gensym
  yVar <- gensym
  d2t <- d2 t
  let d2tTt = TL.App d2t (TL.Pair (TL.Var xVar xType) (TL.Var yVar yType))
  let cur = TL.LCur $ TL.Lambda yVar yType d2tTt
  return $ TL.Lambda xVar xType $ TL.LComp cur TL.LFst
  where
    xType = inferType
    yType = inferType
d2 SL.Inl = do
  xVar <- gensym
  return $ TL.Lambda xVar xType TL.LFst -- Note, we could make this more type safe by doing a dynamic check in TL.LFst to make sure the second component is 0.
  where
    xType = inferType -- EXPERIMENTAL SUPPORT FOR SUM TYPES
d2 SL.Inr = do
  xVar <- gensym
  return $ TL.Lambda xVar xType TL.LSnd -- Note, we could make this more type safe by doing a dynamic check in TL.LSnd to make sure the first component is 0.
  where
    xType = inferType -- EXPERIMENTAL SUPPORT FOR SUM TYPES
d2 (SL.CoPair f g) = do
  xVar <- gensym
  yVar <- gensym
  zVar <- gensym
  d2f <- d2 f
  d2g <- d2 g
  return $
    TL.Lambda
      xVar
      xType
      (TL.Case
         (TL.Var xVar xType)
         (TL.Lambda yVar yType $
          (d2f `TL.App` TL.Var yVar yType) `TL.LComp` (TL.LPair TL.LId TL.Zero))
         (TL.Lambda zVar zType $
          (d2g `TL.App` TL.Var zVar zType) `TL.LComp` (TL.LPair TL.Zero TL.LId)))
  where
    xType = inferType
    yType = inferType
    zType = inferType -- EXPERIMENTAL SUPPORT FOR SUM TYPES
-- Map
d2 SL.Map = do
  xVar <- gensym
  return $ TL.Lambda xVar xType $ TL.DtMap $ TL.Var xVar xType
  where
    xType = inferType
d2 SL.Foldr = return TL.DtFoldr
-- Dop^t
d2 (SL.Op (Constant _)) = return $ TL.LOp DConstantT
d2 (SL.Op EAdd) = return $ TL.LOp DEAddT
d2 (SL.Op EProd) = return $ TL.LOp DEProdT
d2 (SL.Op EScalAdd) = return $ TL.LOp DEScalAddT
d2 (SL.Op EScalProd) = return $ TL.LOp DEScalProdT
d2 (SL.Op Sum) = return $ TL.LOp DSumT -- [1, 1, 1, 1, ...]
d2 (SL.Rec _) -- EXPERIMENTAL SUPPORT FOR GENERAL RECURSION -- THIS IS WRONG: THREAD THROUGH THE CORRECT LIST OF PRIMALS
 = error "This is not yet implemented."
d2 (SL.It t) -- EXPERIMENTAL SUPPORT FOR ITERATION -- THIS IS WRONG: THREAD THROUGH THE CORRECT LIST OF PRIMALS
 = do
  d1t <- d1 t
  d2t <- d2 t
  return $ TL.DtIt d1t d2t
