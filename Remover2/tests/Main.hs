{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}

-- |

module Main where

import           Ghostbuster.LowerDicts
import           Ghostbuster.Ambiguity as A
import           Ghostbuster.Examples.Feldspar
import           Ghostbuster.Examples.Tiny
import           Ghostbuster.Interp as I
import           Ghostbuster.KindCheck as K
import           Ghostbuster.Types

import           Control.DeepSeq
import           Control.Exception (evaluate)
import           Control.Monad
import qualified Data.List as L
import           Data.Typeable
import           Ghostbuster.CodeGen.Prog as CG
import           Language.Haskell.Exts.Pretty
import           Language.Haskell.Interpreter as Hint
import           System.Environment (withArgs, getArgs)
import           System.Exit
import           System.IO
import           System.IO.Temp
import           System.Process
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.TH
import           Text.PrettyPrint.GenericPretty (Out(doc))

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
 result = [DDef {tyName = Var "TypeDict", kVars = [(Var "a",Star)], cVars = [], sVars = [], cases = [KCons {conName = Var "ArrowTyDict", fields = [ConTy (Var "TypeDict") [VarTy (Var "a")],ConTy (Var "TypeDict") [VarTy (Var "b")]], outputs = [ConTy (Var "ArrowTy") [VarTy (Var "a"),VarTy (Var "b")]]},KCons {conName = Var "IntDict", fields = [], outputs = [ConTy (Var "Int") []]}]},DDef {tyName = Var "TyEquality", kVars = [(Var "a",Star),(Var "b",Star)], cVars = [], sVars = [], cases = [KCons {conName = Var "Refl", fields = [], outputs = [VarTy (Var "a"),VarTy (Var "a")]}]}]


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
-- Feldspar tests:


-- | Just make sure the GADTs defs codegen properly.
case_FeldsparGADTCodeGen :: Assertion
case_FeldsparGADTCodeGen =
  interpretProg (Just "FeldsparGADTCodegen") $ Prog feldspar_gadt [] (EK "One")

case_FeldsparADTCodeGen :: Assertion
case_FeldsparADTCodeGen =
    interpretProg (Just "FeldsparADTCodegen") $ Prog feldspar_adt [] (EK "Two")

------------------------------------------------------------
-- Test codegen

-- Attempt to load the generated code for a Prog and run it using Hint. Since
-- Hint can't interpret a whole module from a string, and we need to write it to
-- file anyway, we could also just compile the module directly using 'runghc' or
-- similar.
--

-- TLM: This is shows how to do it, but won't be usable in our setup. Namely,
--      what should 'a' be? This has to be something defined in an _installed_
--      module imported by both this file and the generated code.
--
-- interpretProg :: (Show a, Typeable a) => Prog -> IO a
interpretProg :: Maybe String -> Prog -> IO ()
interpretProg Nothing p = interpretProg (Just "Ghostbuster") p
interpretProg (Just name) prg =
 do
   -- Temporarily keeping these while debugging:
   (file,hdl) <- openTempFile "./" ("temp_"++name++ ".hs")
  -- withSystemTempFile "Ghostbuster.hs" $ \file hdl -> do
   putStrLn $ "\n   Writing file to: "++ file
   let contents = (prettyPrint (moduleOfProg prg))
   hPutStr hdl contents
   hClose hdl
   putStrLn $ "   File written."
   -- putStrLn contents

   when False $ do
      x <- fmap (either interpreterError id) $
        runInterpreter $ do
          loadModules [ file ]
          setImportsQ [ ("Ghostbuster", Nothing )
                      , ("Prelude", Nothing) ]
          interpret "main" infer
      putStrLn "   Interpreter complete.  Got IO action from loaded program.  Running:"
      () <- x
      return ()

   ExitSuccess <- system $ "runghc "++file

   return ()

interpreterError :: InterpreterError -> a
interpreterError e
  = error
  $ case e of
    UnknownError s      -> s
    NotAllowed s        -> s
    GhcException s      -> s
    WontCompile ss      -> unlines $ map errMsg ss


------------------------------------------------------------

testsAbove :: TestTree
testsAbove = $(testGroupGenerator)

-- | This creates a series of "dumb" tests, that run everything, but
-- don't check the outputs.
runAllProgs :: [TestTree]
runAllProgs =
  [ testCase ("runAllProgs"++show ix) $ evaluate $ rnf $ show $
    interp prg
  | prg <- allProgs
  | ix <- [1::Int ..]
  ]

runAllLoweredProgs :: [TestTree]
runAllLoweredProgs =
    [ testCase ("runAllLoweredProgs"++show ix) $
       do putStrLn "  Original:"
          print $ doc prg
          putStrLn "  Lowered:"
          print $ doc $ lowerDicts prg
          putStrLn "  Interpreted:"
          print $ doc $ interp $ lowerDicts prg
  --        evaluate $ rnf $ show $ interp $ lowerDicts prg
          return ()
    | prg <- allProgs
    | ix <- [1::Int ..]
    ]

runAndCompareLowered :: [TestTree]
runAndCompareLowered =
  [ testCase ("runAndCompareLowered"++show ix) $
     do let res1 = interp prg
            res2 = interp $ lowerDicts prg
        assertEqual "interp and (interp . lower) yield the same" res1 res2
  | prg <- allProgsSameLowered
  | ix <- [1::Int ..]
  ]

codegenAllProgs :: [TestTree]
codegenAllProgs =
  [ testCase ("codegenAllProgs"++show ix) $
    -- putStrLn $
    -- evaluate $ rnf $ show $
    --  prettyPrint $ CG.moduleOfProg $ lowerDicts prg
    interpretProg Nothing $ lowerDicts prg
  | prg <- allProgs
  | ix <- [1::Int ..]
  ]

main :: IO ()
main =
  do args <- getArgs
     withArgs (["-t","2"] ++ args) $
      defaultMain $
        testGroup "" $
        [ testsAbove ] ++
        runAllProgs ++
        runAllLoweredProgs ++
        runAndCompareLowered ++
        codegenAllProgs
