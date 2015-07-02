{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE NamedFieldPuns #-}

-- |

module Main where

import           Ghostbuster.LowerDicts
import           Ghostbuster.Ambiguity as A
import           Ghostbuster.Examples.Feldspar
import           Ghostbuster.Examples.Tiny
import           Ghostbuster.Interp as I
import           Ghostbuster.KindCheck as K
import           Ghostbuster.Types
import           Ghostbuster.Utils
import qualified Ghostbuster.Core as Core

import           Control.DeepSeq
import           Control.Exception (evaluate, catch, SomeException, throw)
import           Control.Monad
import qualified Data.List as L
import           Ghostbuster.CodeGen.Prog as CG
import           Language.Haskell.Exts.Pretty
import           Language.Haskell.Interpreter as Hint
import           System.Environment (withArgs, getArgs)
import           System.Exit
import           System.IO
-- import           System.IO.Temp
import           System.Process
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.TH
import           Text.PrettyPrint.GenericPretty (Out(doc))
import           Text.Printf

import           Prelude hiding ( putStrLn, print ) -- use 'say' instead!!

------------------------------------------------------------
-- Print something to console

-- | This deferred version ONLY chats when there's an exception raised.
say :: String -> IO a ->  IO a
say msg act =
  catch act
    (\e ->
       do hPutStrLn stderr ("\n"++msg)
          throw (e::SomeException))

------------------------------------------------------------
-- Deal with in-development tests:

expectFailure :: String -> IO () -> IO ()
expectFailure testname act
  | L.any (==testname) expectedFailures =
    do hPutStrLn stderr $ " ** Expecting failure for test "++testname
       exn <- catch (do act
                        return False)
                    (\e ->
                      do hPutStrLn stderr $ "Caught expected exception: " ++ show (e :: SomeException)
                         return True)
       unless exn $
         error "Expected exception but did not get one!!"
  | otherwise = act

mkTestCase :: TestName -> IO () -> TestTree
mkTestCase tname act = testCase tname (expectFailure tname act)

------------------------------------------------------------

case_E02 :: Assertion
case_E02 = assertEqual "interp_case"
                       (VK (Var "Two") []) (interp $ Prog [ints] [] v02)

case_E03 :: Assertion
case_E03 = assertEqual "interp dict"
             (VDict (Var "Int") []) (interp $ Prog [ints] [] v03)

case_E04 :: Assertion
case_E04 = assertEqual "construct arrow dict"
             (VDict (Var "ArrowTy") [VDict (Var "Int") [],VDict (Var "Int") []])
             (interp $ Prog [] [] v04)

case_E05 :: Assertion
case_E05 = assertEqual "nested casedict, return one"
                       (VK "One" []) $
                       interp $ Prog [ints] [] v05

case_E06 :: Assertion
case_E06 = assertEqual "take a false CaseDict branch"
                       (VK (Var "Three") [])
                       (interp $ Prog [ints] [] v06)

case_E07 :: Assertion
case_E07 = assertEqual ""
                       (VK "True" []) $
                       interp $ Prog [] [] v07

case_E08 :: Assertion
case_E08 = assertEqual ""
                       (VK "False" []) $
                       interp $ Prog [] [] v08

case_E10 :: Assertion
case_E10 = assertEqual "apply identity function"
                       (VK "Three" []) $
                       interp $ Prog [ints] [] v10

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
case_KindFeldspar0 = assertEqual "" (Right ()) (K.kindClosedDefs (primitiveTypes++[dd3]))

case_KindFeldspar1 :: Assertion
case_KindFeldspar1 = assertEqual "" (Right ()) (K.kindClosedDefs (primitiveTypes++feldspar_gadt))

case_KindFeldspar2 :: Assertion
case_KindFeldspar2 = assertEqual "" (Right ()) (K.kindClosedDefs (primitiveTypes++feldspar_adt))

case_KindMutRecurseDDefs :: Assertion
case_KindMutRecurseDDefs = assertEqual "" (Right ()) (K.kindClosedDefs mutRecurseDDefsGood)

------------------------------------------------------------

case_lowerE4 :: Assertion
case_lowerE4 = assertEqual "lower dicts from a program "
                 result
                 (progDDefs (lowerDicts (Prog [] [] v04)))
 where
 result = [DDef {tyName = Var "TypeDict", kVars = [(Var "a",Star)], cVars = [], sVars = [], cases = [KCons {conName = Var "ExistentialDict", fields = [], outputs = [VarTy (Var "any")]},KCons {conName = Var "ArrowTyDict", fields = [ConTy (Var "TypeDict") [VarTy (Var "a")],ConTy (Var "TypeDict") [VarTy (Var "b")]], outputs = [ConTy (Var "ArrowTy") [VarTy (Var "a"),VarTy (Var "b")]]},KCons {conName = Var "IntDict", fields = [], outputs = [ConTy (Var "Int") []]}]},DDef {tyName = Var "TyEquality", kVars = [(Var "a",Star),(Var "b",Star)], cVars = [], sVars = [], cases = [KCons {conName = Var "Refl", fields = [], outputs = [VarTy (Var "a"),VarTy (Var "a")]}]}]



progDDefs :: Prog -> [DDef]
progDDefs (Prog d _ _) = d

case_InterpLowered_e4 :: Assertion
case_InterpLowered_e4 =
  assertEqual ""
    (VK (Var "ArrowTyDict") [VK (Var "IntDict") [],VK (Var "IntDict") []])
    (interp $ lowerDicts $ Prog [] [] v04)

case_InterpLowered_e5 :: Assertion
case_InterpLowered_e5 =
  assertEqual ""
    (VK "One" [])
    (interp $ lowerDicts $ Prog [] [] v05)

case_InterpLowered_e07 :: Assertion
case_InterpLowered_e07 =
  assertEqual "" (VK "True" [])
             (interp $ lowerDicts $ Prog [] [] v07)

case_InterpLowered_e08 :: Assertion
case_InterpLowered_e08 =
  assertEqual "" (VK "False" [])
             (interp $ lowerDicts $ Prog [] [] v08)

------------------------------------------------------------
-- Feldspar tests:


-- | Just make sure the GADTs defs codegen properly.
case_FeldsparGADTCodeGen :: Assertion
case_FeldsparGADTCodeGen
  = interpretProg (Just "FeldsparGADTCodegen")
  $ Prog feldspar_gadt []
  $ VDef "feldspar1" (ForAll [] "Int") (EK "One")

case_FeldsparADTCodeGen :: Assertion
case_FeldsparADTCodeGen
  = interpretProg (Just "FeldsparADTCodegen")
  $ Prog feldspar_adt []
  $ VDef "feldspar2" (ForAll [] "Int") (EK "Two")


_FeldsparGhostbust :: Assertion
_FeldsparGhostbust =
  do let _ = Core.ghostbuster feldspar_gadt
     undefined


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
   (file,hdl) <- openTempFile "./" ("temp_"++name++ "_.hs")
  -- withSystemTempFile "Ghostbuster.hs" $ \file hdl -> do
   say ("\n   Writing file to: "++ file) $ do
    let contents = (prettyPrint (moduleOfProg prg))
    hPutStr hdl contents
    hClose hdl
    say ("   File written.") $
     when False $ do
       x <- fmap (either interpreterError id) $
         runInterpreter $ do
           loadModules [ file ]
           setImportsQ [ ("Ghostbuster", Nothing )
                       , ("Prelude", Nothing) ]
           interpret "main" infer
       say "   Interpreter complete.  Got IO action from loaded program.  Running:" $ do
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
  [ mkTestCase (printf "runAllProgs%02d" ix) $ evaluate $ rnf $ show $
    interp prg
  | prg <- allProgs
  | ix <- [1::Int ..]
  ]

runAllLoweredProgs :: [TestTree]
runAllLoweredProgs =
    [ mkTestCase (printf "runAllLoweredProgs%02d" ix) $
       let p2 = lowerDicts prg
           p3 = interp p2
       in say ("\n  Original:\n"++
               show (doc prg)++
               "\n  Lowered:\n"++
               show (doc p2)++
               "\n  Interpreted:\n"++
               show (doc p3))
            (evaluate $ rnf $ show p3)
    | prg <- allProgs
    | ix <- [1::Int ..]
    ]

runAndCompareLowered :: [TestTree]
runAndCompareLowered =
  [ mkTestCase (printf "runAndCompareLowered%02d" ix) $
     do let res1 = interp prg
            res2 = interp $ lowerDicts prg
        assertEqual "interp and (interp . lower) yield the same" res1 res2
  | prg <- allProgsSameLowered
  | ix <- [1::Int ..]
  ]

codegenAllProgs :: [TestTree]
codegenAllProgs =
  [ mkTestCase (printf "codegenAllProgs%02d" ix) $
    say ("  Original:\n"++ show (doc prg)) $ do
     interpretProg Nothing $ lowerDicts prg
  | prg <- allProgs
  | ix <- [1::Int ..]
  ]

ghostbustAllProgs :: [TestTree]
ghostbustAllProgs =
  [ mkTestCase testname $ expectFailure testname $ do
    let p2 = Core.ghostbuster ddefs mainE
        mainE = (ForAll [] (ConTy "Int" []), (EK "Three"))
        p3 = lowerDicts p2
    say ("\n ***** Full ghostbuster test "++
        "\n  Original:\n"++
        show (doc ddefs)++
        "\n  Busted:\n"++
        show (doc p2)++
        "\n  Lowered:\n"++
        show (doc p3))
     (interpretProg (Just testname) p3)
  | (Prog ddefs _ _) <- allProgs
  | ix <- [1::Int ..]
  , let testname = printf "ghostbust%02d" ix
  ]

downList :: TestTree
downList = mkTestCase tname $
 do let Prog {prgDefs} = p11_bustedList
        mainE = (ForAll [] (ConTy "List'" []),
                 (appLst "downList"
                                  [ EDict "Int"
                                  , appLst (EK "Cons") [EK "Three", EK "Nil"]]))
    interpretProg (Just tname) $
       lowerDicts $ Core.ghostbuster prgDefs mainE
  where
   tname = "Down-convert-list"


downFeldspar :: TestTree
downFeldspar = mkTestCase tname $
  interpretProg (Just tname) $
    lowerDicts $ Core.ghostbuster feldspar_gadt $
      (ForAll [] (ConTy "Int" []), EK "Three")
  where
   tname = "Down-convert-feldspar"


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
        ghostbustAllProgs ++
        codegenAllProgs ++
        [ downList
        , downFeldspar
        ]

-- | Some tests are expected to fail as we develop new functionality.
--   This documents that fact.  Update as we fix things.
expectedFailures :: [String]
expectedFailures =
 [ -- "Down-convert-feldspar"
 ]
