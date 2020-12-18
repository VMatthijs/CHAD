module SourceLanguage where

import Operation (Operation)

-- TODO:
-- - Point-free
-- - Remove var
-- - Identity
-- - Composition
-- Page 9

-- | Terms of the source language
data STerm =
           -- | Identity function
             Id
           -- | Composition
           | Comp STerm STerm
           -- Product tuples
           | Unit                 -- Empty tuple
           | Tuple (STerm, STerm) -- Binary product
           | Fst
           | Snd
           -- | Evaluation
           | Ev
           -- | Curry
           | Curry STerm
           -- | Operation
           | Op Operation
