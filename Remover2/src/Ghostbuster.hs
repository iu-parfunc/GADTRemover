-- |  The main module which reexports the primary entrypoints into the Ghostbuster tool.

module Ghostbuster
       ( runWGhostbusted
--       , interpWGhostbusted
       , runghcProg
       , say
       ) where

import           Ghostbuster.Ambiguity as A
import qualified Ghostbuster.Core as Core
import           Ghostbuster.Interp
import           Ghostbuster.LowerDicts
import           Ghostbuster.Types

import           Control.Exception (catch, SomeException, throw)
-- import           Control.Monad
import           Ghostbuster.CodeGen.Prog as CG
import           Language.Haskell.Exts.Pretty
-- import           Language.Haskell.Interpreter as Hint
import           System.Exit
import           System.IO
-- import           System.IO.Temp
import           System.Process
import           Text.PrettyPrint.GenericPretty (Out(doc))

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
runghcProg :: Maybe String -> Prog -> IO ()
runghcProg Nothing p = runghcProg (Just "Ghostbuster") p
runghcProg (Just tname) prg =
 do
   -- Temporarily keeping these while debugging:
   (file,hdl) <- openTempFile "./" ("temp_"++tname++ "_.hs")
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
