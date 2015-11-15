#!/usr/bin/env stack
-- stack --no-system-ghc --verbosity silent --resolver lts-3.8 --install-ghc runghc --package Ghostbuster --package filemanip --package concurrent-output --package ascii-progress

-- | This script compiles the generated connected component definitions
-- that were ghostbusted in the previous step by 'ConnectedDDefs'.
--
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

-- module CompileBusted where

import ConnectedDDefs                                   ( Stats )
import qualified ConnectedDDefs                         as CC ( Stats(..) )

import Control.Concurrent.MVar
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Par.Class
import Control.Monad.Par.IO
import Data.Csv                                         as CSV
import Data.Default
import Data.List                                        as L
import Data.Vector                                      ( Vector )
import GHC.Generics
import System.Console.AsciiProgress                     ( newProgressBar, tick, pgRegion, pgTotal, pgFormat )
import System.Console.Concurrent
import System.Console.Regions
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.FilePath.GlobPattern
import System.IO
import System.Process
import Text.Printf
import qualified Data.ByteString                        as B
import qualified Data.ByteString.Lazy                   as BL
import qualified Data.Vector                            as V


helpMessage :: String
helpMessage = unlines $
  [ "CompileBusted version 0.1"
  , ""
  , "  Synopsis:"
  , "    CompileBusted [-p GlobPattern] ghostbust_data.csv [output directory]"
  , ""
  , "  Usage:"
  , "    This will read in the data from the provided 'ghostbust_data.csv'"
  , "    to locate ghostbusted files it will then attempt to compile. Only"
  , "    those filenames which match the optional glob pattern will be"
  , "    compiled."
  , ""
  , "    The basic glob pattern syntax is the same as for the Unix shell"
  , "    environment."
  , ""
  , "     - '*' matches up to a directory separator or end of string"
  , "     - '[range]' matches any character in range"
  , "     - '[!range]' matches any character _not_ in range"
  , ""
  , "    There are three extensions to the traditional glob syntax, taken"
  , "    from modern unix shells."
  , ""
  , "     - '\\' escapes a character that might otherwise have special"
  , "       meaning. For a literal '\\' character, use '\\\\'."
  , "     - '**' matches everything, including a directory separator"
  , "     - '(s1|s2|...)' matches any of the strings _s1_, _s2_, etc."
  , ""
  , "    Logs of standard input and output resulting from the compilation"
  , "    are written using into the output directory, using the same"
  , "    directory structure as the input files."
  , ""
  , "    To compile the files using multiple GHC instances, run the script"
  , "    using multiple threads: +RTS -N<number of threads> -RTS"
  , ""
  ]

data Options = Options
  { globPattern         :: Maybe GlobPattern
  , inputCSV            :: FilePath
  , outputDir           :: FilePath
  }

defaultOptions :: Options
defaultOptions = Options
  { globPattern         = Nothing
  , inputCSV            = error helpMessage
  , outputDir           = "."
  }

data Result = Result
  { filePath            :: FilePath
  , variants            :: !Integer
  , successes           :: !Integer
  }
  deriving (Show, Generic, NFData)

instance CSV.FromNamedRecord Result
instance CSV.ToNamedRecord   Result
instance CSV.ToRecord        Result
instance CSV.DefaultOrdered  Result


-- Poor man's concurrent file IO. This is okay for us because we expect to
-- spend most of the time compiling files, rather than writing to the log.
--
data SharedHandle = SharedHandle
  { sHandle     :: Handle
  , sLock       :: MVar ()
  }

newSharedHandle :: IO Handle -> IO SharedHandle
newSharedHandle makeHandle =
  SharedHandle <$> makeHandle <*> newMVar ()

withSharedHandle :: SharedHandle -> (Handle -> IO a) -> IO a
withSharedHandle SharedHandle{..} f =
  withMVar sLock $ \() -> f sHandle

closeSharedHandle :: SharedHandle -> IO ()
closeSharedHandle SharedHandle{..} = do
  () <- takeMVar sLock
  hClose sHandle

withSharedFile :: FilePath -> IOMode -> (SharedHandle -> IO a) -> IO a
withSharedFile name mode =
  bracket (newSharedHandle (openFile name mode))
          closeSharedHandle


-- Attempt to compile ghostbusted files.
--
main :: IO ()
main = displayConsoleRegions $ do
  argv  <- getArgs
  --
  let
      parse :: [String] -> Options -> Options
      parse ("-h":_)         _ = error helpMessage
      parse ("-p":glob:rest) o = parse rest (o { globPattern = Just glob })
      parse [csv]            o = o { inputCSV = csv }
      parse [csv,out]        o = o { inputCSV = csv , outputDir = out }
      parse _                _ = error helpMessage

      opts      = parse argv defaultOptions

      inDir     = takeDirectory (inputCSV opts)
      outDir    = outputDir opts
      outCSV    = outDir </> "ghostbust_result.csv"
  --
  sayIO $ printf "Input file: %s" (inputCSV opts)
  sayIO $ printf "Input directory: %s" inDir
  sayIO $ printf "Output directory: %s" outDir
  sayIO $ printf "Glob pattern: %s" (show (globPattern opts))

  -- Read in the statistics file from the previous step
  --
  statsfile     <- BL.readFile (inputCSV opts)
  stats         <-
    case CSV.decodeByName statsfile of
      Left err    -> error $ printf "Failed to decode stats file '%s'\nMessage: %s" (inputCSV opts) err
      Right (_,v) -> return (v :: Vector CC.Stats)

  let stats'    =  maybe stats (\pat -> (V.filter (\s -> CC.fileName s ~~ pat)) stats) (globPattern opts)

  -- Try to compile all of the ghostbusted files. The results file is
  -- written as we go.
  --
  createDirectoryIfMissing True outDir
  withSharedFile outCSV WriteMode $ \sh -> do
    -- Write the file header
    withSharedHandle sh $ \h -> do
      B.hPutStr h . B.intercalate "," . V.toList $ CSV.headerOrder (undefined :: Result)
      B.hPutStr h "\n"

    -- Run all tests in parallel, collecting the results. Each thread
    -- writes its result as it goes as well, just in case something goes
    -- wrong.
    res <- testAllP opts stats' sh

    let v = V.sum (V.map variants res)
        s = V.sum (V.map successes res)
        p = fromInteger s / fromInteger v * 100.0 :: Double

    sayIO $ printf ""
    sayIO $ printf "COMPLETE: "
    sayIO $ printf "  Files     : %d" (V.length res)
    sayIO $ printf "  Variants  : %d" v
    sayIO $ printf "  Successes : %d (%.2f%%)" s p


-- Test all Ghostbusted files, in parallel if possible.
--
testAllP :: Options -> Vector Stats -> SharedHandle -> IO (Vector Result)
testAllP opts stats sh = do
  progress <- newProgressBar def { pgTotal = toInteger (V.length stats) }
  results  <- runParIO $
    flip parMapM stats $ \s -> liftIO $ do
      r <- test1 opts s
      tick progress
      withSharedHandle sh $ \h -> BL.hPutStr h (CSV.encode [r])
      return r
  --
  closeConsoleRegion (pgRegion progress)
  return results


-- Same implementation as in Control.Monad.Par, but with fixed type
-- signature allowing ParIO.
--
parMapM :: (NFData b, ParFuture f m) => (a -> m b) -> Vector a -> m (Vector b)
parMapM f xs = V.mapM (spawn . f) xs >>= V.mapM get


-- Attempt to compile all of the ghostbusted CCs generated from the given
-- input file.
--
test1 :: Options -> Stats -> IO Result
test1 opts stat = do
  defs          <- locateBustedDDefs opts stat
  let result    = Result { filePath  = CC.fileName stat
                         , variants  = genericLength defs
                         , successes = 0
                         }
  --
  if null defs
    then return result
    else do
      progress  <- newProgressBar def
                      { pgTotal  = genericLength defs
                      , pgFormat = printf "%s :percent [:bar] :current/:total (for :elapsed, :eta remaining)" (takeBaseName (CC.fileName stat))
                      }
      !status   <- forM defs $ \d -> do
                      !s <- compileFile opts (takeDirectory (CC.fileName stat) </> d)
                             `catch`
                             \e -> do errIO $ printf "Testing '%s' returned error: %s" d (show (e :: SomeException))
                                      return False
                      tick progress
                      return s
      --
      closeConsoleRegion (pgRegion progress)
      return result { successes = sum [ 1 | True <- status ] }


-- Locate the ghostbusted CCs that were generated for a given file.
--
locateBustedDDefs :: Options -> Stats -> IO [FilePath]
locateBustedDDefs opts stats =
  let
      inDir             = takeDirectory (inputCSV opts)
      (base,name)       = splitFileName (CC.fileName stats)
      pat               = dropExtension name ++ "_*ghostbusted*"
  in
  if CC.successfulErasures stats > 0
    then do
      busted <- filter (~~ pat) `fmap` getDirectoryContents (inDir </> base)
      sayIO   $ printf "Found %d busted CCs for '%s'" (length busted) (CC.fileName stats)
      return busted
    else
      return []


-- Run GHC on the given file. No object files are generated. The standard
-- output and error logs are written into files in the output directory.
-- Return whether or not the file compiled successfully.
--
compileFile :: Options -> FilePath -> IO Bool
compileFile opts inFile = do
  let
      outFile   = outputDir opts </> inFile
      outDir    = takeDirectory outFile
      inRoot    = takeDirectory (inputCSV opts)
      inFile'   = inRoot </> inFile
  --
  createDirectoryIfMissing True outDir
  withFile (outFile `replaceExtension` "log") WriteMode $ \h -> do
    let
        compile = (proc "stack" ["exec", "ghc", "--", "-fno-code", "-odir", "/dev/null", "-hidir", "/dev/null", "-c", inFile'])
                    { std_out = UseHandle h
                    , std_err = UseHandle h
                    }
    --
    (_,_,_,hdl) <- createProcess compile
    status      <- waitForProcess hdl
    case status of
      ExitSuccess       -> return True
      ExitFailure code  -> do errIO $ printf "compileFile '%s' exited with status (%d)" inFile' code
                              return False


-- Debugging support
-- -----------------

sayIO :: String -> IO ()
sayIO msg = outputConcurrent (msg ++ "\n")
-- sayIO _ = return ()


errIO :: String -> IO ()
errIO msg = errorConcurrent (msg ++ "\n")
-- sayIO _ = return ()
