module SourceLanguage where

import Operation (Operation)

-- | Terms of the source language
data STerm = Var String -- TODO: Also needs a type?
           -- Product tuples
           | Nullary              -- Empty tuple
           | Tuple (STerm, STerm) -- Binary product
           | Fst STerm
           | Snd STerm
           -- Functions
           | Lambda String STerm -- TODO: Have to specify type of the var?
           | Apply STerm STerm
           -- Operations
           -- Idea: Op OperationName STerm, where OperationName is an enum with the operations
           | Op Operation STerm
