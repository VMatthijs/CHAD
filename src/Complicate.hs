{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Complify terms in the target language
module Complicate where

import SourceLanguage as SL
import Types
import NanoParsec
import Operation

complicate :: String -> (STerm a (RealN n))
complicate str = complicate' (run str)

complicate' :: LT (Dr1 a) => Expr -> (STerm a (RealN n))
complicate' (Add x y) = SL.Comp (SL.Pair (complicate' x) (complicate' y)) (SL.Op EAdd)
complicate' _ = undefined