module TargetLanguage where

import SourceLanguage (STerm)
import Operation (LinearOperation)

-- | Terms of the target language
data TTerm =
           -- | Term of the source language
             ST STerm
           -- | Linear operation
           | LOp LinearOperation TTerm
           -- Linear functions
           | LId
           | LComp TTerm TTerm
           | LApp  TTerm TTerm
           | LEval TTerm -- Function form of LApp?!
           -- Tuples
           | LFst
           | LSnd
           | LPair TTerm TTerm
           -- Singleton
           | Singleton TTerm
           -- Zero, Plus
           | Zero
           | Plus TTerm TTerm
           -- Swap
           | LSwap TTerm -- What does this do?
           -- | Tensor-elimination
           | LCur TTerm

