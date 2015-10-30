module Main where

import Ghostbuster
import System.Exit
import System.Environment
import System.FilePath
import System.Process
import System.Exit

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
  putStrLn $ "Got output files: "++show allOuts
  return ()


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
