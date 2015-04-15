
module Main where

import qualified Test1
import qualified Test2


main :: IO ()
main = do
  putStrLn "===== Approach 1 ====="
  Test1.runTests

  putStrLn "===== Approach 2 ====="
  Test2.runTests

