#!/usr/bin/env stack
-- stack --verbosity silent --resolver lts-3.8 --install-ghc runghc  --package turtle --package filemanip --package split

--   --package optparse-applicative

-- | This is a shell script to extract the latest tarball for each package.

{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Main where
import Turtle as T
import Filesystem.Path.CurrentOS as S
import qualified Data.Text as Text

outPath = "data/2_untarred"

main :: IO ()
main = sh $
  do mktree outPath
     liftIO $ putStrLn $ "Unpacking tarballs to: "++S.encodeString outPath
     cd outPath
     file <- ls "../1_only_newest_versions/"
     liftIO $ putStrLn $ "Unpacking: "++ S.encodeString file
     let (Right file_t) = S.toText file
     shell (Text.append "tar xf " file_t) T.empty
     return ()
