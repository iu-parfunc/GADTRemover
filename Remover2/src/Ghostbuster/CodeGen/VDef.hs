{-# LANGUAGE RecordWildCards #-}

module Ghostbuster.CodeGen.VDef
  where

import Ghostbuster.Types
import Ghostbuster.CodeGen.Base

import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc                     ( noLoc )


-- Convert a value definition into a set of top-level declarations
--
declOfVDef :: VDef -> [Decl]
declOfVDef VDef{..} =
  [ mkTypeSig valName valTy
  , FunBind [ ]
  ]


-- Convert a type scheme into a type signature
--
mkTypeSig :: Var -> TyScheme -> Decl
mkTypeSig ident scheme
  = TypeSig noLoc [varName ident]
  $ case scheme of
      MonTy t    -> mkType t
      ForAll a t -> TyForall (Just (map (uncurry mkTyVarBind) a)) [] (mkType t)

