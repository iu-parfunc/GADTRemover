{-# LANGUAGE OverloadedStrings #-}

module Ghostbuster.CodeGen.Prog
  where

import           Ghostbuster.Types
import           Ghostbuster.CodeGen.Exp
import           Ghostbuster.CodeGen.DDef
import           Ghostbuster.CodeGen.VDef
import           Ghostbuster.Showable

import qualified Data.Set as S
import           Language.Haskell.Exts as H
import           Language.Haskell.Exts.SrcLoc ( noLoc )

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
                  , OptionsPragma noLoc (Just GHC) " -fdefer-type-errors "
--                  , OptionsPragma noLoc (Just GHC) " -fno-warn-dodgy-imports "
--                  , OptionsPragma noLoc (Just GHC) " -fno-warn-unused-imports "
                  ]

    mkImport n  = ImportDecl noLoc (ModuleName n) False False False Nothing Nothing
    imports     = [ mkImport "Prelude" $ Just (True, [ IAbs      (Ident "Int")
                                                     , IThingAll (Ident "Maybe")
                                                     , IThingAll (Ident "Bool")
                                                     ])
--                  , mkImport "Data.Typeable" Nothing
                  ]

    -- RRN: Here we implicitly add the "prelude" types:
    ddefs'      = ddefs ++ primitiveTypes

    showable    = showableDefs ddefs'

    decls       = map (\d -> if S.member (tyName d) showable
-- RRN: TEMP/FIXME: Disabling this because of a temporary Showable.hs bug:
--                                then gadtOfDDef True d
                                then gadtOfDDef False d
                                else gadtOfDDef False d) ddefs'
               ++ concatMap declOfVDef vdefs
               ++ [ mkDeclOfExp "ghostbuster" e  -- TLM: ???
                  , valBind "main" mainExp
                  ]

valBind :: String -> H.Exp -> Decl
valBind str bod =
  FunBind [ Match noLoc (name str)
            [] Nothing (UnGuardedRhs bod) (BDecls [])
          ]

mainExp :: H.Exp
mainExp = app (var $ name "print")
              (appFun (var$name "seq") [var$name "ghostbuster", (tuple [])])
              -- RRN: We could just print it... but need to recover
              -- its type to tell if it's safe:
              -- (var$name "ghostbuster")
