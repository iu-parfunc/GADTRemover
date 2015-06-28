{-# LANGUAGE RecordWildCards #-}

module Ghostbuster.CodeGen.DDef
  where

import Ghostbuster.Types
import Ghostbuster.CodeGen.Base

import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc                     ( noLoc )


-- Convert a single datatype definition into a top-level GADT data type
-- declaration.
--
gadtOfDDef :: DDef -> Decl
gadtOfDDef DDef{..} =
  let vars = kVars ++ cVars ++ sVars            -- TLM: order??
  in
  GDataDecl
    noLoc                                       -- source location
    DataType                                    -- data type or newtype declaration
    []                                          -- context, class assertions
    (varName tyName)
    (map (uncurry mkTyVarBind) vars)
    Nothing                                     -- TLM: Maybe Kind ???
    (map (mkGADTCtor tyName) cases)             -- GADT constructors
    []                                          -- [deriving]


-- Generate the declaration for a single GADT constructor
--
mkGADTCtor :: TName -> KCons -> GadtDecl
mkGADTCtor tyName KCons{..} =
  GadtDecl
    noLoc                       -- source location
    (varName conName)
    []                          -- TLM ???
    theType
  where
    resultType  = ConTy tyName outputs
    theType     = case map mkType (fields ++ [resultType]) of
                    []  -> error "GADT constructor with empty type"
                    xs  -> foldr1 TyFun xs

