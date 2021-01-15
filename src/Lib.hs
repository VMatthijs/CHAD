module Lib where

import Control.Monad.State.Lazy (State, evalState)

(&&&) :: (a -> b) -> (a -> c) -> a -> (b, c)
(&&&) f g x = (f x, g x)


runAD :: (t -> State Integer a) -> t -> a
runAD d term = evalState (d term) 0
