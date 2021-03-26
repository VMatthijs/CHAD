-- | Different helper functions used in the library
module Helper where

import           Control.Monad.State.Lazy (State, evalState)

-- | Helper function to run one of the AD methods
runAD :: (t -> State Integer a) -> t -> a
runAD d term = evalState (d term) 0
