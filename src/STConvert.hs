{-# LANGUAGE GADTs #-}

-- | Convert a source-language program to a target-language program without
-- changing semantics. This is always possible because the target language is a
-- superset of the source language.
module STConvert (
  stConvert,
) where

import SourceLanguage
import TargetLanguage


stConvert :: STerm env a -> TTerm env a
stConvert (SVar i) = Var i
stConvert (SLambda e) = Lambda (stConvert e)
stConvert (SLet rhs e) = Let (stConvert rhs) (stConvert e)
stConvert (SApp f a) = App (stConvert f) (stConvert a)
stConvert SUnit = Unit
stConvert (SPair a b) = Pair (stConvert a) (stConvert b)
stConvert (SFst p) = Fst (stConvert p)
stConvert (SSnd p) = Snd (stConvert p)
stConvert (SOp op a) = Op op (stConvert a)
stConvert (SMap a b) = Map (stConvert a) (stConvert b)
stConvert (SMap1 a b) = Map1 (stConvert a) (stConvert b)
-- stConvert SMap2 = Map2
stConvert (SReplicate x) = Replicate (stConvert x)
stConvert (SSum x) = Sum (stConvert x)
