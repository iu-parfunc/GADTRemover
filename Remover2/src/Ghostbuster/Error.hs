{-# LANGUAGE DeriveDataTypeable #-}

module Ghostbuster.Error
  where

import Data.Typeable
import Control.Exception
import Text.Printf


data Status
  = AmbiguityCheck
  | TypeCheck
  | Parser
  | CodeGen
  | Core
  | Interpreter
  | Internal
  | Unknown
  | NotImplemented
  deriving (Eq, Show, Enum)

data GhostbusterError
  = GhostbusterError Status String
  deriving Typeable

instance Exception GhostbusterError

instance Show GhostbusterError where
  showsPrec _ (GhostbusterError s m) = showString (printf "Ghostbuster exception (%s): %s" (show s) m)

ghostbusterError :: Status -> String -> a
ghostbusterError s m = throw (GhostbusterError s m)

ghostbusterErrorIO :: Status -> String -> IO a
ghostbusterErrorIO s m = throwIO (GhostbusterError s m)

