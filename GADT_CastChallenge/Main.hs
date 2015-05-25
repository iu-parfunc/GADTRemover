
module Main where

import qualified Test2
import qualified Test3

import qualified GADT_Feldspar
import qualified ADT_Feldspar
import qualified ADT_Feldspar2

main :: IO ()
main = do

  putStrLn "===== Approach 2 ====="
  Test2.runTests
