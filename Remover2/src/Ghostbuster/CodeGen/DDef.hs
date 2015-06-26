{-# LANGUAGE RecordWildCards #-}

module Ghostbuster.CodeGen.DDef
  where

import Ghostbuster.Types                                as G
import Language.Haskell.Exts                            as H
import Language.Haskell.Exts.SrcLoc


-- Convert a single datatype definition into a top-level GADT data type
-- declaration.
--
gadtOfDDef :: DDef -> Decl
gadtOfDDef DDef{..} =
  GDataDecl
    noLoc                                       -- source location
    DataType                                    -- data type or newtype declaration
    []                                          -- context, class assertions
    (varName tyName)
    (map toTyVarBind (kVars ++ cVars ++ sVars))
    Nothing                                     -- TLM: Maybe Kind ???
    (map toGADTConstr cases)                    -- GADT constructors
    []                                          -- [deriving]


toGADTConstr :: KCons -> GadtDecl
toGADTConstr KCons{..} =
  GadtDecl
    noLoc                       -- source location
    (varName conName)
    []                          -- TLM ???
    theType
  where
    theType     = case map toType (fields ++ outputs) of
                    [x] -> x
                    xs  -> foldr1 TyFun xs

varName :: Var -> Name
varName = name . unMkVar

toTyVarBind :: (Var, G.Kind) -> H.TyVarBind
toTyVarBind (v, G.Star) = UnkindedVar (varName v)
toTyVarBind (v, k)      = KindedVar (varName v) (toKind k)

toKind :: G.Kind -> H.Kind
toKind G.Star              = KindStar
toKind (G.ArrowKind k1 k2) = KindFn (toKind k1) (toKind k2)

toType :: MonoTy -> Type
toType (VarTy v)        = TyVar (varName v)
toType (ArrowTy a b)    = TyFun (toType a) (toType b)
toType (TupleTy tup)    = TyTuple Boxed (map toType tup)
toType (ConTy c tys)    = foldl TyApp (TyCon (UnQual (varName c))) (map toType tys)
toType (TypeDictTy _v)  = error "toType.TypeDictTy"     -- TLM: ???

