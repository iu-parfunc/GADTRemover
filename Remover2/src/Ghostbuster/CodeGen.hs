{-# LANGUAGE RecordWildCards #-}

module Ghostbuster.CodeGen where

import Ghostbuster.Types
import Ghostbuster.CodeGen.Prog

import Data.Maybe
import Text.Printf
import Language.Haskell.Exts


-- Pretty print a Ghostbuster Prog into Haskell source code. Additionally,
-- we include some information about what was ghostbusted in the file.
--
prettyProg :: Prog -> String
prettyProg prog =
    let
        mdl     = prettyPrint (moduleOfProg prog)
        header  = unlines $ mapMaybe erasureInfo (prgDefs prog)
    in
    unlines [ header, mdl ]


erasureInfo :: DDef -> Maybe String
erasureInfo DDef{..}
  | not (null cVars) || not (null sVars)
  = let
        n = unMkVar tyName
        k = unwords [ unMkVar v | (v,_k) <- kVars ]
        c = unwords [ unMkVar v | (v,_k) <- cVars ]
        s = unwords [ unMkVar v | (v,_k) <- sVars ]
    in
    Just $
      unlines [ printf "-- Ghostbusted data type '%s %s %s %s':" n k c s
              , printf "--    kept        : %s" k
              , printf "--    checked     : %s" c
              , printf "--    synthesised : %s" s
              , "--"
              ]

erasureInfo _ = Nothing

