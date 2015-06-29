{-# LANGUAGE OverloadedStrings #-}

module Ghostbuster.CodeGen.Prog
  where

import Ghostbuster.Types
import Ghostbuster.CodeGen.Exp
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

    imports     = map mkImport [ "Data.Typeable", "Prelude hiding (Bool,Maybe,Int)" ]

    mkImport n  = ImportDecl noLoc (ModuleName n) False False False Nothing Nothing Nothing

    -- RRN: Here we implicitly add the "prelude" types:
    allDDefs = ddefs ++ primitiveTypes

    decls       = map gadtOfDDef allDDefs
               ++ concatMap declOfVDef vdefs
               ++ [ mkDeclOfExp "ghostbuster" e ]         -- TLM: ???
