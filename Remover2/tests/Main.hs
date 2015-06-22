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

case_I2 = assertEqual "interp_case"
                      (VK (Var "Two") []) I.ti2

main :: IO ()
main = $(defaultMainGenerator)
