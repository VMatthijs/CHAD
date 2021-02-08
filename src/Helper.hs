-- | Different helper functions used in the library
module Helper where

import Control.Monad.State.Lazy (State, evalState, get, put)

(&&&) :: (a -> b) -> (a -> c) -> a -> (b, c)
(&&&) f g x = (f x, g x)

-- | Helper function to run one of the AD methods
runAD :: (t -> State Integer a) -> t -> a
runAD d term = evalState (d term) 0

-- | Generate a variable name based on the current state
gensym :: State Integer String
gensym = do i <- get
            put (i + 1)
            return ("x" ++ show i)
