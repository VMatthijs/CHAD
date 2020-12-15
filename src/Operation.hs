module Operation where

import Lib (RealN)


-- | Possible operators in the source language
data Operation = Constant RealN -- Necessary?
               | EAdd
               | EProd
               | MProd
               | Sum
               | Sigmoid
               | Map


-- | D op and D op^t of the Operators in the source language?
data LinearOperation = Undefined
