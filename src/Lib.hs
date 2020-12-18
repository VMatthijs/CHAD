module Lib where

(&&&) :: (a -> b) -> (a -> c) -> a -> (b, c)
(&&&) f g x = (f x, g x)

someFunc :: IO ()
someFunc = putStrLn "someFunc"
