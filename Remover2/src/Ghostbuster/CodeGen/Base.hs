
module Ghostbuster.CodeGen.Base
  where

import Ghostbuster.Types                                as G
import Language.Haskell.Exts                            as H


varName :: Var -> Name
varName = name . unMkVar

-- Generate a type variable declaration, with kind annotation if not simply kind
-- star.
--
toTyVarBind :: Var -> G.Kind -> H.TyVarBind
toTyVarBind v G.Star = UnkindedVar (varName v)
toTyVarBind v k      = KindedVar (varName v) (toKind k)

-- Convert a Ghostbuster kind to a haskell-src-exts kind
--
toKind :: G.Kind -> H.Kind
toKind G.Star              = KindStar
toKind (G.ArrowKind k1 k2) = KindFn (toKind k1) (toKind k2)

-- Convert a Ghostbuster type to a haskell-src-exts type
--
toType :: MonoTy -> Type
toType (VarTy v)        = TyVar (varName v)
toType (ArrowTy a b)    = TyFun (toType a) (toType b)
toType (TupleTy tup)    = TyTuple Boxed (map toType tup)
toType (ConTy c tys)    = foldl TyApp (TyCon (UnQual (varName c))) (map toType tys)
toType (TypeDictTy _v)  = error "toType.TypeDictTy"     -- TLM: ???

