{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

-- |

module Main where

import Ghostbuster.Types
import Ghostbuster.Examples.Feldspar
import Ghostbuster.Interp as I
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

case_I2 :: Assertion
case_I2 = assertEqual "interp_case"
                      (VK (Var "Two") []) I.ti2

case_I3 :: Assertion
case_I3 = assertEqual "interp dict"
            (VDict (Var "Int") []) I.ti3

main :: IO ()
main = $(defaultMainGenerator)
