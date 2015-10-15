module Main where

import Ghostbuster
import System.Exit
import System.Environment


main :: IO ()
main = do
  args  <- getArgs
  check args
  let (inputFilename, outputFilename) = parse args
  ghostBustToFile inputFilename outputFilename

check :: [String] -> IO ()
check ["-h"] = usage   >> exit
check ["-v"] = version >> exit
check []     = die "Invalid arguments -- a file name MUST be passed to Ghostbuster"
check ls@(a:b:c:d)= die $ "Invalid args " ++ show ls
check ls = return ()

parse :: [String] -> (String, String)
parse [input] = (input, "Busted" ++ input)
parse [input, output] = (input, output)

exit = exitSuccess
usage = putStrLn "Usage: Ghostbust [-vh] <input file name> [<output file name>]"
version = putStrLn "Ghostbuster Version 0.1"
