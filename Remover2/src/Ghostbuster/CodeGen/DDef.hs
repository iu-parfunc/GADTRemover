{-# LANGUAGE RecordWildCards #-}

module Ghostbuster.CodeGen.DDef
  where

import Ghostbuster.Types
import Ghostbuster.CodeGen.Base

import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc                     ( noLoc )


-- Convert a single datatype definition into a top-level GADT data type
-- declaration.  First argument specifies whether to derive show.
--
gadtOfDDef :: Bool -> DDef -> Decl
gadtOfDDef deriveShow DDef{..} =
  let vars = kVars ++ cVars ++ sVars            -- TLM: order??
      derives = if deriveShow
                   then [(UnQual$ name "Show",[])]
                   else []
  in
  GDataDecl
    noLoc                                       -- source location
    DataType                                    -- data type or newtype declaration
    []                                          -- context, class assertions
    (varName tyName)
    (map (uncurry mkTyVarBind) vars)
    Nothing                                     -- TLM: Maybe Kind ???
    (map (mkGADTCtor tyName) cases)             -- GADT constructors
    derives                                     -- [deriving]

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
    theType     = foldr1 TyFun
                $ map mkType (fields ++ [ConTy tyName outputs])
