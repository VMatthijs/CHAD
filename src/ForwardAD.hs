{-# LANGUAGE GADTs #-}
module ForwardAD where

import Control.Monad.State.Lazy

import qualified SourceLanguage as SL
import qualified TargetLanguage as TL
import Types
import LanguageTypes
import Operation


d1 :: SL.STerm a b -> State Integer (TL.TTerm (Df1 a -> Df1 b))
d1  SL.Id        = do val <- get; put (val + 1)
                      let xVar = "x" ++ show val
                      return $ TL.Lambda xVar t (TL.Var xVar t)
    where t = inferType
d1 (SL.Comp f g) = do val <- get
                      let xVar = "x" ++ show val
                      let yVar = "y" ++ show (val + 1)
                      let (d1f, newVal') = runState (d1 f) (val + 2)
                      let (d1g, newVal)  = runState (d1 g) newVal'
                      put newVal
                      let d1fTt = TL.App d1f (TL.Var xVar t1)
                      let d1gTt = TL.App d1g (TL.Var yVar t2)
                      return $ TL.Lambda xVar t1 $ TL.substTt yVar d1fTt t2 d1gTt
    where t1  = inferType
          t2  = inferType
d1  SL.Unit      = return $ TL.Lambda "_" inferType TL.Unit
d1 (SL.Pair t s) = do val <- get
                      let xVar = "x" ++ show val
                      let (d1t, newVal') = runState (d1 t) (val + 1)
                      let (d1s, newVal)  = runState (d1 s) newVal'
                      put newVal
                      let fstPair = TL.App d1t (TL.Var xVar varType)
                      let sndPair = TL.App d1s (TL.Var xVar varType)
                      return $ TL.Lambda xVar varType $ TL.Pair fstPair sndPair
    where varType = inferType
d1  SL.Fst       = do val <- get; put (val + 1)
                      let xVar = "x" ++ show val
                      return $ TL.Lambda xVar t $ TL.Fst (TL.Var xVar t)
    where t = inferType
d1  SL.Snd       = do val <- get; put (val + 1)
                      let xVar = "x" ++ show val
                      return $ TL.Lambda xVar t $ TL.Snd (TL.Var xVar t)
    where t = inferType
-- \x -> fst ((fst x) (snd x))
d1  SL.Ev        = do val <- get; put (val + 1)
                      let xVar = "x" ++ show val
                      let x = TL.Var xVar t
                      return $ TL.Lambda xVar t $ TL.Fst (TL.App (TL.Fst x) (TL.Snd x))
    where t = inferType
d1 (SL.Curry t)  = do val <- get
                      let xVar = "x" ++ show val
                      let yVar = "y" ++ show (val + 1)
                      let (d1t, newValue') = runState (d1 t) (val + 2)
                      let (d2t, newValue)  = runState (d2 t) newValue'
                      put newValue
                      let d1tTt   = TL.App d1t (TL.Pair (TL.Var xVar xType) (TL.Var yVar yType))
                      let d2tTt   = TL.App d2t (TL.Pair (TL.Var xVar xType) (TL.Var yVar yType))
                      let sndPair = TL.LComp (TL.LPair TL.Zero TL.LId) d2tTt
                      return $ TL.Lambda xVar xType $ TL.Lambda yVar yType $ TL.Pair d1tTt sndPair
    where xType   = inferType
          yType   = inferType
d1 (SL.Op op)    = do val <- get; put (val + 1)
                      let xVar = "x" ++ show val
                      return $ TL.Lambda xVar t $ TL.Op op (TL.Var xVar t)
    where t = inferType
d1  SL.Map       = do val <- get
                      let xVar = "x" ++ show val
                      let yVar = "y" ++ show (val + 1)
                      put (val + 2)
                      let f = TL.Lambda yVar yType $ TL.Fst
                            $ TL.App (TL.Fst (TL.Var xVar xType)) (TL.Var yVar yType)
                      let v = TL.Snd (TL.Var xVar xType)
                      return $ TL.Lambda xVar xType $ TL.Map f v
    where xType = inferType
          yType = inferType


d2 :: SL.STerm a b -> State Integer (TL.TTerm (Df1 a -> LFun (Df2 a) (Df2 b)))
d2  SL.Id        = return $ TL.Lambda "_" inferType TL.LId
d2 (SL.Comp f g) = do val <- get
                      let xVar = "x" ++ show val
                      let (d1f, newVal'') = runState (d1 f) (val + 1)
                      let (d2f, newVal')  = runState (d2 f) newVal''
                      let (d2g, newVal)   = runState (d2 g) newVal'
                      put newVal
                      let d1fTt = TL.App d1f (TL.Var xVar xType)
                      let d2fTt = TL.App d2f (TL.Var xVar xType)
                      let d2gTt = TL.App d2g d1fTt
                      return $ TL.Lambda xVar xType $ TL.LComp d2fTt d2gTt
    where xType = inferType
d2  SL.Unit      = return TL.Zero
d2 (SL.Pair t s) = do val <- get
                      let xVar = "x" ++ show val
                      let (d2t, newVal') = runState (d2 t) (val + 1)
                      let (d2s, newVal)  = runState (d2 s) newVal'
                      put newVal
                      let fstPair = TL.App d2t (TL.Var xVar varType)
                      let sndPair = TL.App d2s (TL.Var xVar varType)
                      return $ TL.Lambda xVar varType $ TL.LPair fstPair sndPair
    where varType = inferType
d2  SL.Fst       = return $ TL.Lambda "_" inferType TL.LFst
d2  SL.Snd       = return $ TL.Lambda "_" inferType TL.LSnd
d2  SL.Ev        = do val <- get; put (val + 1)
                      let xVar = "x" ++ show val
                      let y       = TL.Snd (TL.Var xVar xType)
                      let plusLhs = TL.LComp TL.LFst (TL.LEval y)
                      -- LSnd ;; Snd ((Fst x) y)
                      let plusRhs = TL.LComp TL.LSnd (TL.Snd (TL.App (TL.Fst (TL.Var xVar xType)) y))
                      return $ TL.Lambda xVar xType $ TL.Plus plusLhs plusRhs
    where xType = inferType
d2 (SL.Curry t)  = do val <- get
                      let xVar = "x" ++ show val
                      let yVar = "y" ++ show (val + 1)
                      let (d2t, newVal) = runState (d2 t) (val + 2)
                      put newVal

                      let d2tTt = TL.App d2t (TL.Pair (TL.Var xVar xType) (TL.Var yVar yType))
                      return $ TL.Lambda xVar xType $ TL.LSwap $ TL.Lambda yVar yType
                             $ TL.LComp (TL.LPair TL.LId TL.Zero) d2tTt
    where xType = inferType
          yType = inferType
-- Map
-- x := (f, v)
-- y := (g, w)
d2  SL.Map      = do val <- get
                     let xVar = "x" ++ show val
                     let yVar = "y" ++ show (val + 1)
                     let zVar = "z" ++ show (val + 2)
                     put (val + 3)

                     let f = TL.Lambda zVar zType $ TL.Snd
                           $ TL.App (TL.Fst (TL.Var xVar xType)) (TL.Var zVar zType)
                     let v = TL.Snd (TL.Var xVar xType)
                     let g = TL.Fst (TL.Var yVar yType)
                     let w = TL.Snd (TL.Var yVar yType)
                     return $ TL.Lambda xVar xType $ TL.Lambda yVar yType
                            $ TL.Plus (TL.Map g v) (TL.ZipWith f v w)
    where xType = inferType
          yType = inferType
          zType = inferType
-- Dop
d2 (SL.Op (Constant _)) = return $ TL.LOp DConstant
d2 (SL.Op EAdd   )      = return $ TL.LOp DEAdd
d2 (SL.Op EProd  )      = return $ TL.LOp DEProd
d2 (SL.Op MProd  )      = undefined -- undefined
d2 (SL.Op Sum    )      = return $ TL.LOp DSum
d2 (SL.Op Sigmoid)      = undefined --TL.Lambda "x" inferType (TL.Op (DSigmoid))
