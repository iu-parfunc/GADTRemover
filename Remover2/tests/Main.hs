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

ti2 :: Val
ti2 = interp $ Prog [ints] [] p2

ti3 :: Val
ti3 = interp $ Prog [ints] [] p3

ti4 :: Val
ti4 = interp $ Prog [] [] p4

ti5 :: Val
ti5 = interp $ Prog [ints] [] p5

ti6 :: Val
ti6 = interp $ Prog [ints] [] p6

ti7 :: Val
ti7 = interp $ Prog [ints] [] p7

case_I2 :: Assertion
case_I2 = assertEqual "interp_case"
                      (VK (Var "Two") []) ti2

case_I3 :: Assertion
case_I3 = assertEqual "interp dict"
            (VDict (Var "Int") []) ti3

case_I4 :: Assertion
case_I4 = assertEqual "construct arrow dict"
            (VDict (Var "ArrowTy") [VDict (Var "Int") [],VDict (Var "Int") []])
            ti4

case_I5 :: Assertion
case_I5 = assertEqual "nested casedict"
                      (VK (Var "One") []) ti5

case_I6 :: Assertion
case_I6 = assertEqual "take a false CaseDict branch"
                      (VK (Var "Three") []) ti6

case_I7 :: Assertion
case_I7 = assertEqual "apply identity function"
                      (VK "Three" []) ti7

-- | This should NOT diverge (lazy evaluation):
case_I8 :: Assertion
case_I8 = assertEqual "" (VK "Nothing" []) (interp p8_unusedLoop)

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

case_lowerP4 :: Assertion
case_lowerP4 = assertEqual "lower dicts from a program "
                 result
                 (progDDefs (lowerDicts (Prog [] [] p4)))
 where
 result = [DDef {tyName = Var "TypeDict", kVars = [(Var "a",Star)], cVars = [], sVars = [], cases = [KCons {conName = Var "ArrowTyDict", fields = [ConTy (Var "TypeDict") [VarTy (Var "a")],ConTy (Var "TypeDict") [VarTy (Var "b")]], outputs = [ConTy (Var "ArrowTyDict") [VarTy (Var "a"),VarTy (Var "b")]]},KCons {conName = Var "IntDict", fields = [], outputs = [ConTy (Var "IntDict") []]}]},DDef {tyName = Var "TyEquality", kVars = [(Var "a",Star),(Var "b",Star)], cVars = [], sVars = [], cases = [KCons {conName = Var "Refl", fields = [], outputs = [VarTy (Var "a"),VarTy (Var "a")]}]}]

progDDefs :: Prog -> [DDef]
progDDefs (Prog d _ _) = d

case_InterpLowered1 :: Assertion
case_InterpLowered1 =
  assertEqual ""
    (VK (Var "ArrowTyDict") [VK (Var "IntDict") [],VK (Var "IntDict") []])
    (interp $ lowerDicts $ Prog [] [] p4)

------------------------------------------------------------

main :: IO ()
main =
  do args <- getArgs
     withArgs (["-t","2"] ++ args) $
      $(defaultMainGenerator)
