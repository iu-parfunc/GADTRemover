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
    pragmas     = [ LanguagePragma noLoc [ Ident "GADTs" ]
                  , LanguagePragma noLoc [ Ident "ScopedTypeVariables" ]
                  , OptionsPragma noLoc (Just GHC) " -fno-warn-dodgy-imports "
                  , OptionsPragma noLoc (Just GHC) " -fno-warn-unused-imports "
                  ]

    imports     = [ mkImport "Prelude"       {- hiding -} ["Maybe", "Bool", "Int"]
                  , mkImport "Data.Typeable" {- hiding -} ["(:~:)"]
                  ]

    mkImport name hiding
      = ImportDecl noLoc (ModuleName name) False False False Nothing Nothing
      $ Just (True, [ IThingAll (Ident h) | h <- hiding ])

    -- RRN: Here we implicitly add the "prelude" types:
    allDDefs = ddefs ++ primitiveTypes

    decls       = map gadtOfDDef allDDefs
               ++ concatMap declOfVDef vdefs
               ++ [ mkDeclOfExp "ghostbuster" e ]         -- TLM: ???

