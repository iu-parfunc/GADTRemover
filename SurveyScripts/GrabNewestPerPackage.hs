#!/usr/bin/env stack
-- stack --verbosity silent --resolver lts-3.8 --install-ghc runghc  --package turtle --package filemanip --package optparse-applicative

-- | This is a shell script to extract the latest tarball for each package.

{-# LANGUAGE OverloadedStrings #-}
module Main where

-- import qualified Control.Foldl as L
import System.FilePath.Find as F
import Turtle as T
import Control.Monad

main :: IO ()
main =
  do putStrLn "Symlinking newest versions of each tarball"
     ls <- F.find (return True) (F.extension ==? ".gz") "./hackage_all_tarballs/"
     -- ls <- fold (L.)
     putStrLn "First ten files found:"
     forM_ (take 10 ls) putStrLn
