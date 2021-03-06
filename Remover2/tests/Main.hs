{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE NamedFieldPuns #-}

-- | Test the ghostbuster software.

module Main where

import           Ghostbuster (runWGhostbusted, runghcProg, say)
import           Ghostbuster.Ambiguity as A
import qualified Ghostbuster.Core as Core
import           Ghostbuster.Examples.Feldspar
import           Ghostbuster.Examples.Tiny
import           Ghostbuster.Interp as I
import           Ghostbuster.KindCheck as K
import           Ghostbuster.LowerDicts
import           Ghostbuster.Types
import           Ghostbuster.Utils

import           Control.DeepSeq
import           Control.Exception (evaluate, catch, SomeException)
import           Control.Monad
import qualified Data.List as L
-- import           Ghostbuster.CodeGen.Prog as CG
-- import           Language.Haskell.Exts.Pretty
-- import           Language.Haskell.Interpreter as Hint
import           System.Environment (withArgs, getArgs)
-- import           System.Exit
import           System.IO
-- import           System.IO.Temp
-- import           System.Process
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.TH
import           Text.PrettyPrint.GenericPretty (Out(doc))
import           Text.Printf
import           Prelude hiding ( putStrLn, print ) -- use 'say' instead!!

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
                       (VK (Var "Two") []) (interp $ Prog [intD] [] v02)

case_E03 :: Assertion
case_E03 = assertEqual "interp dict"
             (VDict (Var "Int") []) (interp $ Prog [intD] [] v03)

case_E04 :: Assertion
case_E04 = assertEqual "construct arrow dict"
             (VDict (Var "ArrowTy") [VDict (Var "Int") [],VDict (Var "Int") []])
             (interp $ Prog [] [] v04)

case_E05 :: Assertion
case_E05 = assertEqual "nested casedict, return one"
                       (VK "One" []) $
                       interp $ Prog [intD] [] v05

case_E06 :: Assertion
case_E06 = assertEqual "take a false CaseDict branch"
                       (VK (Var "Three") [])
                       (interp $ Prog [intD] [] v06)

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
                       interp $ Prog [intD] [] v10

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
  = runghcProg (Just "FeldsparGADTCodegen")
  $ Prog feldspar_gadt []
  $ VDef "feldspar1" (ForAll [] "Int") (EK "One")

case_FeldsparADTCodeGen :: Assertion
case_FeldsparADTCodeGen
  = runghcProg (Just "FeldsparADTCodegen")
  $ Prog feldspar_adt []
  $ VDef "feldspar2" (ForAll [] "Int") (EK "Two")


_FeldsparGhostbust :: Assertion
_FeldsparGhostbust =
  do let _ = Core.ghostbuster feldspar_gadt
     undefined


------------------------------------------------------------
-- Test codegen


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
     runghcProg Nothing $ lowerDicts prg
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
     (runghcProg (Just testname) p3)
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
    runWGhostbusted (Just tname) prgDefs mainE
  where
   tname = "Down-list1"

 -- | Test with the SAME name used in T and K:
downList2 :: TestTree
downList2 = mkTestCase tname $
 -- FIXME: replacing "elt" with "a" will currently cause an error, but we
 -- need to fix the toolchain so that is not the case.
 do let prgDefs = [DDef "List" [] [("elt", Star)] []
                      [ KCons "Nil" [] ["a"]
                      , KCons "Cons" ["a", ConTy "List" ["a"]] ["a"]
                      ]
                  ]
        mainE = (ForAll [] (ConTy "List'" []),
                 (appLst "downList"
                                  [ EDict "Int"
                                  , appLst (EK "Cons") [EK "Three", EK "Nil"]]))
    runWGhostbusted (Just tname) prgDefs mainE
  where
   tname = "Down-list2"


downupList1 :: TestTree
downupList1 = mkTestCase tname $
 do let Prog {prgDefs} = p11_bustedList
        mainE = (ForAll [] (ConTy "List" ["Int"]),
                 (appLst "upList"
                  [ EDict "Int"
                  , (appLst "downList"
                                     [ EDict "Int"
                                     , appLst (EK "Cons") [EK "Three", EK "Nil"]])]))
    runghcProg (Just tname) $
       lowerDicts $ Core.ghostbuster prgDefs mainE
  where
   tname = "Downup-list1"


downFeldspar :: [TestTree]
downFeldspar =
  [ mkTestCase tname $
     runWGhostbusted (Just tname) feldspar_gadt $
             (ForAll [] (ConTy "Exp'" []),
              appLst "downExp" [EDict "Unit" , dictE, expr])
  | (_,dictE,expr) <- feldspar_progs
  | ix <- [1::Int ..]
  , let tname = "Down-feldspar"++show ix]


downupFeldspar :: [TestTree]
downupFeldspar =
  [ mkTestCase tname $
     runWGhostbusted (Just tname) feldspar_gadt $
        (ForAll []
         -- (ConTy "SealedExp" ["Unit"]),
         (ConTy "Exp" ["Unit", typ]),
         openSealedExp typ $
         appLst "upExp"
                [EDict "Unit",
                 appLst "downExp" [EDict "Unit" , dictE, expr]] )
  | (typ,dictE,expr) <- feldspar_progs
  | ix <- [1::Int ..]
  , let tname = "Downup-feldspar"++show ix]

downupdownFeldspar :: [TestTree]
downupdownFeldspar =
  [ mkTestCase tname $
     runWGhostbusted (Just tname) feldspar_gadt $
       (ForAll []
        (ConTy "Exp'" []),
        appLst "downExp"
          [ EDict "Unit", dictE
          , openSealedExp typ $
             appLst "upExp"
                    [EDict "Unit",
                     appLst "downExp" [EDict "Unit" , dictE, expr]] ]
                   )
  | (typ,dictE,expr) <- feldspar_progs
  | ix <- [1::Int ..]
  , let tname = "Downupdown-feldspar"++show ix]

openSealedExp :: MonoTy -> Exp -> Exp
openSealedExp typ e =
  ECase e
    [ (Pat "SealedExp" ["dict","x"],
       EIfTyEq ("dict", mkDict typ) "x" "undefined")]

feldspar_progs :: [(MonoTy, Exp, Exp)]
feldspar_progs = feldspar_intprogs ++ feldspar_funprogs

feldspar_intprogs :: [(MonoTy, Exp, Exp)]
feldspar_intprogs = [ ( "Int", EDict "Int", lit "Three" )
                    , ( "Int", EDict "Int"
                      , app (lamN zro) (lit "Two"))
                    , ( "Int", EDict "Int"
                      , appLst (EK "Mul") [lit "One",
                        appLst (EK "Add") [lit "Two", lit "Three"]])
                    ]

feldspar_funprogs :: [(MonoTy, Exp, Exp)]
feldspar_funprogs = [ ( ArrowTy "Int" "Int", intToIntDict
                      , lamN (lit "Three"))
                    , ( ArrowTy "Int" "Int", intToIntDict
                      , (lamN zro)) ]


----------------------------------------
-- Feldspar constructors

lit :: KName -> Exp
lit n = EApp (EK "Con") (EK n)

zro :: Exp
zro = EApp (EK "Var") (EK "Zro")

intToIntDict :: Exp
intToIntDict = mkDict (ArrowTy intT intT)
-- appLst (EDict "ArrowTy") [EDict "Int",EDict "Int"]
  where
  intT = (ConTy "Int" [])

mkDict :: MonoTy -> Exp
mkDict (VarTy t) = EDict t -- This could be an error.
mkDict (ArrowTy t1 t2) = appLst (EDict "ArrowTy") [mkDict t1, mkDict t2]
mkDict (ConTy tn ls) = appLst (EDict tn) (map mkDict ls)
mkDict (TypeDictTy t) =
  error$ "mkDict: not allowing dict of dict currently: "++show (TypeDictTy t)

app :: Exp -> Exp -> Exp
app f x = appLst (EK "App") [f,x]

lamN :: Exp -> Exp
lamN bod = appLst (EK "Abs") [intTyp, bod]

intTyp :: Exp
intTyp = EK "Int"

----------------------------------------

main :: IO ()
main = do
  args <- getArgs
  withArgs (["-t","2"] ++ args)
    $ defaultMain
    $ testGroup ""
    $ testsAbove :
      runAllProgs ++
      runAllLoweredProgs ++
      runAndCompareLowered ++
      ghostbustAllProgs ++
      codegenAllProgs ++
      downFeldspar ++
      downupFeldspar ++
      downupdownFeldspar ++
      [ downList, downList2
      , downupList1
      ]

-- | Some tests are expected to fail as we develop new functionality.
--   This documents that fact.  Update as we fix things.
expectedFailures :: [String]
expectedFailures =
 [ -- "Down-feldspar4"
   -- "Down-list2"
 -- "Downup-feldspar"++show i | i <- [1..5 :: Int]
 ]
