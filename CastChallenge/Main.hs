
module Main where

import qualified Test2
import qualified Test3

import qualified Feldspar.GADT
import qualified Feldspar.ADT1
import qualified Feldspar.ADT2

main :: IO ()
main = do

  putStrLn "===== Approach 2 ====="
  Test2.runTests
