{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Ghostbuster
-- import Ghostbuster.Types (tyName)
import Ghostbuster.Parser.Prog as Parse
import System.Environment
import System.Exit
import System.FilePath
import System.Process
import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit   (testCase, assertEqual)
import qualified Data.Map as M

main :: IO ()
main = do
  args  <- getArgs
  check args
  let (inputFilename, outputFilename) = parse args
  ghostBustToFile inputFilename outputFilename

fuzztest :: Bool -> [String] -> IO ()
fuzztest _ []            = putStrLn "fuzztest: requires input file.\n" >> usage >> exit
fuzztest doStrong (infile:rest) = do
  let (_,outfile) = parse [infile]
  --
  printf "Begin fuzz testing: %s\n" infile
  printf "Passing extra arguments to tasty: %s\n" (show rest)
  --
  toTest <- fuzzTest doStrong infile outfile
  --
  withArgs rest
    $ defaultMain
    $ testGroup "FuzzTest"
      [ testCase ("variant"++ show ind) $ do
          status <- system (unwords [ "ghc", "-fforce-recomp", file ])
          assertEqual "process return code" ExitSuccess status
      | Just (ind,file) <- toTest
      ]

survey :: [String] -> IO ()
survey (infile:_rest) = do
  let (_,outfile) = parse [infile]
  putStrLn "Begin --survey of the input file, ignoring Ghostbuster annotations."
  putStrLn $ "Input: " ++infile
  prg <- Parse.gParseModule infile
  putStrLn $ "Input parsed..."
  SurveyResult{gadtsBecameASTS,surveyMode,results} <- (surveyFuzzTest prg outfile)
  putStrLn $ "gadtsBecameASTS: "++show (gadtsBecameASTS)

  let resList = M.elems results
  putStrLn $ "Total results: " ++ show (length results)
  putStrLn $ "Succedeed: "     ++ show (length [() | Success {}        <- resList])
  putStrLn $ "AmbFailure: "    ++ show (length [() | AmbFailure {}     <- resList])
  putStrLn $ "CodegenFailure: "++ show (length [() | CodeGenFailure {} <- resList])

  -- status <- system (unwords [ "ghc", "-fforce-recomp", file ])
  return ()

survey [] = error "survey: bad arguments"


check :: [String] -> IO ()
check ["-h"]                 = usage   >> exit
check ["-v"]                 = version >> exit
check ("--fuzz":args)        = fuzztest False args >> exit
check ("--strong-fuzz":args) = fuzztest True args >> exit
check ("--survey":args)      = survey args >> exit
check []              = die "Invalid arguments -- a file name MUST be passed to Ghostbuster.  Try -h."
check ls@(_:_:_:_)    = die (printf "Invalid args: %s\n" (show ls))
check _               = return ()

parse :: [String] -> (String, String)
parse [input]         = (input, takeDirectory input </> "output" </> "Busted_" ++ takeFileName input)
parse [input, output] = (input, output)
parse _               = error "parse failed"

exit :: IO a
exit = exitSuccess

usage :: IO ()
usage = do
  version
  putStrLn ""
  putStrLn "Usage: ghostbust [-vh] <inputFile> [<outputFile>]"
  putStrLn "       ghostbust --fuzz <inputFile> [<tastyArgs>]"
  putStrLn "       ghostbust --survey <inputFile> "
  putStrLn "       ghostbust --strong-fuzz <inputFile> [<tastyArgs>]"
  putStrLn " "
  putStrLn " Note that we don't expect the strong version of the gradual guarantee\
           \to hold (--strong-fuzz)."

version :: IO ()
version = putStrLn "Ghostbuster version 0.1"
