
module Main where

import qualified Test2
import qualified Test3

main :: IO ()
main = do

  putStrLn "===== Approach 2 ====="
  Test2.runTests
