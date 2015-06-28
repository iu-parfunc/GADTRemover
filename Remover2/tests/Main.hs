{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

-- |

module Main where

import Ghostbuster.Types
import Ghostbuster.Examples.Feldspar
import Ghostbuster.Interp as I
import Ghostbuster.Ambiguity as A
import Ghostbuster.KindCheck as K

-- import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

------------------------------------------------------------

case_I2 :: Assertion
case_I2 = assertEqual "interp_case"
                      (VK (Var "Two") []) I.ti2

case_I3 :: Assertion
case_I3 = assertEqual "interp dict"
            (VDict (Var "Int") []) I.ti3

case_I5 :: Assertion
case_I5 = assertEqual "nested casedict"
                      (VK (Var "One") []) ti5

case_I6 :: Assertion
case_I6 = assertEqual "take a false CaseDict branch"
                      (VK (Var "Three") []) ti6

case_I7 :: Assertion
case_I7 = assertEqual "apply identity function"
                      (VK "Three" []) ti7

------------------------------------------------------------

case_AmbCheck1 :: Assertion
case_AmbCheck1 = assertEqual "Feldspar gadt passes ambiguity check"
              () (ambCheckErr feldspar_gadt)

case_AmbCheck2 :: Assertion
case_AmbCheck2 = assertEqual "Feldspar adt passes ambiguity check"
             () (ambCheckErr feldspar_adt)

------------------------------------------------------------

case_KindFeldspar0 :: Assertion
case_KindFeldspar0 = assertEqual "" (Right ()) (K.kindClosedDefs [ints,dd3])

case_KindFeldspar1 :: Assertion
case_KindFeldspar1 = assertEqual "" (Right ()) (K.kindClosedDefs feldspar_gadt)

case_KindFeldspar2 :: Assertion
case_KindFeldspar2 = assertEqual "" (Right ()) (K.kindClosedDefs feldspar_adt)

------------------------------------------------------------

main :: IO ()
main = $(defaultMainGenerator)
