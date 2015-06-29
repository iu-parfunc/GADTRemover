{-# LANGUAGE RecordWildCards #-}

module Ghostbuster.CodeGen.VDef
  where

import Ghostbuster.Types                                as G
import Ghostbuster.CodeGen.Base                         as G
import Ghostbuster.CodeGen.Exp                          as G

import Language.Haskell.Exts                            as H
import Language.Haskell.Exts.SrcLoc                     ( noLoc )


-- Convert a value definition into a set of top-level declarations
--
declOfVDef :: VDef -> [Decl]
declOfVDef VDef{..} =
  [ mkTypeSig valName valTy
  , mkDeclOfExp valName valExp
  ]

