{-# LANGUAGE OverloadedStrings #-}

module Ghostbuster.CodeGen.Prog
  where

import Ghostbuster.Types
import Ghostbuster.CodeGen.DDef
import Ghostbuster.CodeGen.VDef

import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc                     ( noLoc )


moduleOfProg :: Prog -> Module
moduleOfProg (Prog ddefs vdefs e) =
  Module
    noLoc
    (ModuleName "Ghostbuster")          -- TLM: module name???
    pragmas                             -- top-level module pragmas
    Nothing                             -- warning text, e.g. deprecated
    Nothing                             -- export spec; just export everything for now
    imports                             -- import declarations
    decls                               -- top-level module declarations
  where
    pragmas     = [ LanguagePragma noLoc [ Ident "GADTs"
                                         , Ident "ScopedTypeVariables"
                                         ]
                  ]

    imports     = map mkImport [ "Data.Typeable" ]
    mkImport n  = ImportDecl noLoc (ModuleName n) False False False Nothing Nothing Nothing

    decls       = map gadtOfDDef ddefs
               ++ concatMap declOfVDef vdefs
               ++ [ declOfExp "ghostbuster" e ]         -- TLM: ???
