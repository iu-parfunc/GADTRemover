{-# LANGUAGE OverloadedStrings #-}

module Ghostbuster.CodeGen.Prog
  where

import Ghostbuster.Types                                as G
import Ghostbuster.CodeGen.DDef
import Ghostbuster.CodeGen.VDef
import Ghostbuster.Showable

import Language.Haskell.Exts                            as H
import Language.Haskell.Exts.SrcLoc                     ( noLoc )
import qualified Data.Set                               as S


moduleOfProg :: Prog -> Module
moduleOfProg (Prog ddefs vdefs vtop) =
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

    ddefs'      = ddefs ++ primitiveTypes       -- Add the "Prelude" types
    showable    = showableDefs ddefs'
    showit d    = S.member (tyName d) showable

    -- FIXME: This test is insufficient.  It should make sure there is
    -- no polymorphism in the type of vtop:
    topShowable = case valTy vtop of
                    ForAll _ (ConTy tn _) -> S.member tn showable
                    _ -> False

    decls       = map (\d -> gadtOfDDef (showit d) d) ddefs'
               ++ concatMap declOfVDef vdefs
               ++ declOfVDef vtop
               ++ declOfVDef (mkMain topShowable vtop)


mkMain :: Bool -> VDef -> VDef
mkMain doprint vtop =
  VDef { valName = "main"
       , valTy   = ForAll [] (ConTy "IO" [ConTy "()" []])
       , valExp  = if doprint
                      then (EApp "print" (G.EVar (valName vtop)))
                      else EApp (EApp "seq" (G.EVar (valName vtop)))
                                (EApp "return" (EK "()"))
       }
