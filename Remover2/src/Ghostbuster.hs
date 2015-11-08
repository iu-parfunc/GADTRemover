{-# LANGUAGE NamedFieldPuns #-}

-- |  The main module which reexports the primary entrypoints into the Ghostbuster tool.

module Ghostbuster (
      Ghostbust
    , runWGhostbusted
    -- , interpWGhostbusted
    , runghcProg
    , say
    , ghostBustToFile
    , writeProg
    , fuzzTest
) where

import           Ghostbuster.Ambiguity                  as A
import           Ghostbuster.CodeGen.Prog               as CG
import qualified Ghostbuster.Core                       as Core
import           Ghostbuster.Interp                     ()
import           Ghostbuster.LowerDicts
import           Ghostbuster.Parser.Prog                as Parse
import           Ghostbuster.Types

import Control.Exception              (catch, SomeException, throw)
import Control.Monad                  (forM_, forM, liftM)
-- import Data.List                      (transpose)
-- import Data.Maybe                     (catMaybes)
import Language.Haskell.Exts.Pretty
import System.Directory
-- import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.Process
-- import Text.PrettyPrint.GenericPretty (Out(doc))
import Text.Printf


-- | Run an expression in the context of ghostbusted definitions.
-- This invokes the complete compiler pipeline, including ambiguity
-- checking, code generation, and running the generated code.
--
-- As for output, it prints the value of the main expression if its
-- type supports printing.  Otherwise, it evaluates it to WHNF.
runWGhostbusted :: Maybe String    -- ^ Descriptive name for this program.
                -> [DDef]          -- ^ Data definitions, including ones to be ghostbusted.
                -> (TyScheme, Exp) -- ^ Main expression to run.
                -> IO ()
runWGhostbusted tname ddefs mainE =
  case ambCheck ddefs of
    Left err -> error$ "Failed ambiguity check:\n" ++err
    Right () ->
      runghcProg tname $
        lowerDicts $ Core.ghostbuster ddefs mainE

-- | Just like runWGhostbusted, but run through the interpreter.
--
--   This pretty prints the resulting `Val`.
interpWGhostbusted :: Maybe String -> [DDef] -> (TyScheme, Exp) -> IO ()
interpWGhostbusted tname ddefs mainE =
  case ambCheck ddefs of
    Left err -> error$ "Failed ambiguity check:\n" ++err
    Right () ->
      undefined $
       lowerDicts $ Core.ghostbuster ddefs mainE


--------------------------------------------------------------------------------

-- TODO: Tim, add an entrypoint here for compiling to disk.  That can
-- be exposed via an executable in the cabal file.

ghostBustToFile :: FilePath -> FilePath -> IO ()
ghostBustToFile input output = do
  Prog prgDefs prgVals (VDef name tyscheme expr) <- Parse.gParseModule input
  case ambCheck prgDefs of
    Left err -> error$ "Failed ambiguity check:\n" ++err
    Right () ->
      writeProg output $
       lowerDicts $ Core.ghostbuster prgDefs (tyscheme, expr)

writeProg :: String -> Prog -> IO ()
writeProg filename prog = do
  createDirectoryIfMissing True (takeDirectory filename)
  hdl <- openFile filename WriteMode
  say ("\n Writing to file " ++ filename)$ do
    let contents = prettyPrint $ moduleOfProg prog
    hPutStr hdl contents
    hClose hdl
    say "\n File written." $
      return ()

-- | Try different weakenings of the ghostbuster configuration in the input
-- file, and write the outputs to filepaths at the given root.
--
-- This function immediately parses the input file and returns a list
-- of possible test actions corresponding to different weakenings.
-- Each test action returns an output filepath if it succeeds.
--
fuzzTest :: FilePath -> FilePath -> IO [IO (Maybe FilePath)]
fuzzTest inpath outroot = do
  Prog prgDefs _prgVals (VDef _name tyscheme expr) <- Parse.gParseModule inpath
  let possibilities = sequence $ map varyBusting prgDefs
  putStr $ "GOT POSSIBILITIES: "++ show (length possibilities) ++"\n"
  forM_ (zip [0..] possibilities) $ \ (ind,defs) -> do
    putStr $ show ind ++ ": "
    forM_ defs $ \ DDef{kVars,cVars,sVars} ->
      putStr $ "  " ++
               show ( map (unVar . fst) kVars
                    , map (unVar . fst) cVars
                    , map (unVar . fst) sVars)
    putStr "\n"

  return [
    let
        (file,ext) = splitExtension outroot
        newName    = file ++ printf "%03d" index <.> ext
    in
    case ambCheck defs of
      Left err -> do
        printf "Possibility %d failed ambiguity check!\n" index
        return Nothing

      Right () -> do
        writeProg newName $ lowerDicts $ Core.ghostbuster defs (tyscheme,expr)
        return (Just newName)
   | (index,defs) <- (zip [(0::Int) ..] possibilities)
   ]

 where
  varyBusting dd@(DDef{kVars,cVars,sVars}) =
   let total = length cVars + length sVars
       erased = (cVars++sVars)
   in
    [ -- (steal1A+steal1B, steal2)
     dd { kVars = kVars ++ take steal1A cVars ++ take steal1B sVars
        , cVars = drop steal1A cVars ++ take steal2 sVars
        , sVars = drop (steal1B + steal2) sVars }
    | steal1A <- [0..length cVars]
    , steal1B <- [0.. if steal1A == length cVars
                      then length sVars
                      else 0]
    -- This attempts the stronger form of gradualizaiton, where synth
    -- vars can be demoted to checked.  I think this form doesn't actually
    -- hold, but we need to pinpoint exactly why.
    -- , steal2  <- [0.. length sVars - steal1B]
    , let steal2 = 0 -- Alternatively, this uses only the simpler gradualization.
    ]

--------------------------------------------------------------------------------

-- Attempt to load the generated code for a Prog and run it using Hint. Since
-- Hint can't interpret a whole module from a string, and we need to write it to
-- file anyway, we could also just compile the module directly using 'runghc' or
-- similar.
--
-- TLM: This is shows how to do it, but won't be usable in our setup. Namely,
--      what should 'a' be? This has to be something defined in an _installed_
--      module imported by both this file and the generated code.
--
-- runghcProg :: (Show a, Typeable a) => Prog -> IO a
-- The alternative here is to just execute programs for effect.

-- | WRite a program to a file
runghcProg :: Maybe String -> Prog -> IO ()
runghcProg Nothing p = runghcProg (Just "Ghostbuster") p
runghcProg (Just tname) prg =
 do
   -- Temporarily keeping these while debugging:
   createDirectoryIfMissing True ghostbustTempDir
   (file,hdl) <- openTempFile ghostbustTempDir ("temp_"++tname++ "_.hs")
  -- withSystemTempFile "Ghostbuster.hs" $ \file hdl -> do
   say ("\n   Writing file to: "++ file) $ do
    let contents = (prettyPrint (moduleOfProg prg))
    hPutStr hdl contents
    hClose hdl
    say ("   File written.") $ do
  {-
-- Hint version:
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
  -}
     ExitSuccess <- system $ "runghc "++file
     return ()

ghostbustTempDir :: FilePath
ghostbustTempDir = "./ghostbuster_generated/"

------------------------------------------------------------
-- Helper functions
------------------------------------------------------------

{-
-- Depends on Hint:

interpreterError :: InterpreterError -> a
interpreterError e
  = error
  $ case e of
    UnknownError s      -> s
    NotAllowed s        -> s
    GhcException s      -> s
    WontCompile ss      -> unlines $ map errMsg ss

-}

-- | Print something to console.  This deferred version ONLY chats
-- when there's an exception raised.
say :: String -> IO a ->  IO a
say msg act =
  catch act
    (\e ->
       do hPutStrLn stderr ("\n"++msg)
          throw (e::SomeException))
