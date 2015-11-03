module Main where

import Control.Monad
import Ghostbuster
import System.Environment
import System.Exit
import System.FilePath
import System.Process
import Test.Tasty
import Test.Tasty.Program

main :: IO ()
main = do
  args  <- getArgs
  check args
  let (inputFilename, outputFilename) = parse args
  ghostBustToFile inputFilename outputFilename

fuzztest :: [String] -> IO ()
fuzztest args = do
  let (inp,outp) = parse args
  putStrLn$ "Begin fuzz testing: "++ show (inp,outp)
  allOuts <- fuzzTest inp outp
  -- ExitSuccess <- system $ "ghc "++outp
  withArgs []
    $ defaultMain
    $ testGroup "Now try to compile each output file..."
    $ [ testProgram outfile "ghc" [ "-fforce-recomp", outfile ] Nothing | outfile <- allOuts ]


check :: [String] -> IO ()
check ["-h"] = usage   >> exit
check ["-v"] = version >> exit
check ("--fuzz":args) = fuzztest args >> exit
check []     = die "Invalid arguments -- a file name MUST be passed to Ghostbuster"
check ls@(a:b:c:d)= die $ "Invalid args " ++ show ls
check ls = return ()

parse :: [String] -> (String, String)
parse [input] = (input, takeDirectory input </> "Busted_" ++ takeFileName input)
parse [input, output] = (input, output)

exit = exitSuccess
usage = putStrLn "Usage: Ghostbust [-vh] <input file name> [<output file name>]"
version = putStrLn "Ghostbuster Version 0.1"
