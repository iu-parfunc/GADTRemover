module Main where

import Ghostbuster
import System.Environment
import System.Exit
import System.FilePath
import System.Process
import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit   (testCase, assertEqual)

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
  printf "Begin fuzz testing: %s" infile
  printf "Passing extra arguments to tasty: %s" (show rest)
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


check :: [String] -> IO ()
check ["-h"]                 = usage   >> exit
check ["-v"]                 = version >> exit
check ("--fuzz":args)        = fuzztest False args >> exit
check ("--strong-fuzz":args) = fuzztest True args >> exit
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
  putStrLn "       ghostbust --strong-fuzz <inputFile> [<tastyArgs>]"
  putStrLn " "
  putStrLn " Note that we don't expect the strong version of the gradual guarantee\
           \to hold (--strong-fuzz)."

version :: IO ()
version = putStrLn "Ghostbuster version 0.1"
