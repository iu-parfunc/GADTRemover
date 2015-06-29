{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

-- |

module Main where

import Ghostbuster.LowerDicts
import Ghostbuster.Ambiguity as A
import Ghostbuster.Examples.Feldspar
import Ghostbuster.Examples.Tiny
import Ghostbuster.Interp as I
import Ghostbuster.KindCheck as K
import Ghostbuster.Types

-- import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH
import System.Environment (withArgs, getArgs)

------------------------------------------------------------

case_E02 :: Assertion
case_E02 = assertEqual "interp_case"
                       (VK (Var "Two") []) (interp $ Prog [ints] [] e02)

case_E03 :: Assertion
case_E03 = assertEqual "interp dict"
             (VDict (Var "Int") []) (interp $ Prog [ints] [] e03)

case_E04 :: Assertion
case_E04 = assertEqual "construct arrow dict"
             (VDict (Var "ArrowTy") [VDict (Var "Int") [],VDict (Var "Int") []])
             (interp $ Prog [] [] e04)

case_E05 :: Assertion
case_E05 = assertEqual "nested casedict, return one"
                       (VK "One" []) $
                       interp $ Prog [ints] [] e05

case_E06 :: Assertion
case_E06 = assertEqual "take a false CaseDict branch"
                       (VK (Var "Three") [])
                       (interp $ Prog [ints] [] e06)

case_E07 :: Assertion
case_E07 = assertEqual ""
                       (VK "True" []) $
                       interp $ Prog [] [] e07

case_E08 :: Assertion
case_E08 = assertEqual ""
                       (VK "False" []) $
                       interp $ Prog [] [] e08

case_E10 :: Assertion
case_E10 = assertEqual "apply identity function"
                       (VK "Three" []) $
                       interp $ Prog [ints] [] e10

-- | This should NOT diverge (lazy evaluation):
case_P8 :: Assertion
case_P8 = assertEqual "" (VK "Nothing" []) (interp p8_unusedLoop)

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

case_KindMutRecurseDDefs :: Assertion
case_KindMutRecurseDDefs = assertEqual "" (Right ()) (K.kindClosedDefs mutRecurseDDefsGood)

------------------------------------------------------------

case_lowerE4 :: Assertion
case_lowerE4 = assertEqual "lower dicts from a program "
                 result
                 (progDDefs (lowerDicts (Prog [] [] e04)))
 where
 result = [DDef {tyName = Var "TypeDict", kVars = [(Var "a",Star)], cVars = [], sVars = [], cases = [KCons {conName = Var "ArrowTyDict", fields = [ConTy (Var "TypeDict") [VarTy (Var "a")],ConTy (Var "TypeDict") [VarTy (Var "b")]], outputs = [ConTy (Var "ArrowTyDict") [VarTy (Var "a"),VarTy (Var "b")]]},KCons {conName = Var "IntDict", fields = [], outputs = [ConTy (Var "IntDict") []]}]},DDef {tyName = Var "TyEquality", kVars = [(Var "a",Star),(Var "b",Star)], cVars = [], sVars = [], cases = [KCons {conName = Var "Refl", fields = [], outputs = [VarTy (Var "a"),VarTy (Var "a")]}]}]

progDDefs :: Prog -> [DDef]
progDDefs (Prog d _ _) = d

case_InterpLowered_e4 :: Assertion
case_InterpLowered_e4 =
  assertEqual ""
    (VK (Var "ArrowTyDict") [VK (Var "IntDict") [],VK (Var "IntDict") []])
    (interp $ lowerDicts $ Prog [] [] e04)

case_InterpLowered_e5 :: Assertion
case_InterpLowered_e5 =
  assertEqual ""
    (VK "One" [])
    (interp $ lowerDicts $ Prog [] [] e05)

case_InterpLowered_e07 :: Assertion
case_InterpLowered_e07 =
  assertEqual "" (VK "True" [])
             (interp $ lowerDicts $ Prog [] [] e07)

case_InterpLowered_e08 :: Assertion
case_InterpLowered_e08 =
  assertEqual "" (VK "False" [])
             (interp $ lowerDicts $ Prog [] [] e08)

------------------------------------------------------------

main :: IO ()
main =
  do args <- getArgs
     withArgs (["-t","2"] ++ args) $
      $(defaultMainGenerator)
