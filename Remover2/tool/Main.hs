module Main where

import Ghostbuster
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.Process
import Test.Tasty
import Test.Tasty.HUnit   (testCase, assertEqual)

main :: IO ()
main = do
  args  <- getArgs
  check args
  let (inputFilename, outputFilename) = parse args
  ghostBustToFile inputFilename outputFilename

fuzztest :: [String] -> IO ()
fuzztest args = do
  let (inp:restargs) = args
      (_,outp)       = parse [inp]
  putStrLn$ "Begin fuzz testing: "++ show (inp) ++ " passing args to tasty: "++show restargs
  allOuts <- fuzzTest inp outp :: IO [IO (Maybe FilePath)]
  -- ExitSuccess <- system $ "ghc "++outp
  withArgs restargs
    $ defaultMain
    $ testGroup ""
    $ [ testCase ("FuzzTest"++show ind) $
         do Just outfile <- onetest
            -- testProgram outfile "ghc" [ "-fforce-recomp", outfile ] Nothing
            code <- system (unwords [ "ghc", "-fforce-recomp", outfile ])
            assertEqual "process return code" ExitSuccess code
      | (ind,onetest) <- zip [0..] allOuts ]


check :: [String] -> IO ()
check ["-h"] = usage   >> exit
check ["-v"] = version >> exit
check ("--fuzz":args) = fuzztest args >> exit
check []     = die "Invalid arguments -- a file name MUST be passed to Ghostbuster"
check ls@(a:b:c:d)= die $ "Invalid args " ++ show ls
check ls = return ()

parse :: [String] -> (String, String)
parse [input]         = (input, takeDirectory input </> "output" </> "Busted_" ++ takeFileName input)
parse [input, output] = (input, output)

exit = exitSuccess
usage = putStrLn $ "Usage: ghostbust [-vh] <input file name> [<output file name>]\n"++
                   "OR: ghostbust --fuzz <inputFile> <tastyArgs> ..."
version = putStrLn "Ghostbuster Version 0.1"
