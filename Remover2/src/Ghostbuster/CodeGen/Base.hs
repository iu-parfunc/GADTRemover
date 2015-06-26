
module Ghostbuster.CodeGen.Base
  where

import Ghostbuster.Types                                as G
import Language.Haskell.Exts                            as H


varName :: Var -> Name
varName = name . unMkVar

-- Generate a type variable declaration, with kind annotation if not simply kind
-- star.
--
mkTyVarBind :: Var -> G.Kind -> H.TyVarBind
mkTyVarBind v G.Star = UnkindedVar (varName v)
mkTyVarBind v k      = KindedVar (varName v) (mkKind k)

-- Convert a Ghostbuster kind to a haskell-src-exts kind
--
mkKind :: G.Kind -> H.Kind
mkKind G.Star              = KindStar
mkKind (G.ArrowKind k1 k2) = KindFn (mkKind k1) (mkKind k2)

-- Convert a Ghostbuster type to a haskell-src-exts type
--
mkType :: MonoTy -> Type
mkType (VarTy v)        = TyVar (varName v)
mkType (ArrowTy a b)    = TyFun (mkType a) (mkType b)
mkType (TupleTy tup)    = TyTuple Boxed (map mkType tup)
mkType (ConTy c tys)    = foldl TyApp (TyCon (UnQual (varName c))) (map mkType tys)
mkType (TypeDictTy v)   = mkType (ConTy "TypeDict" [VarTy v])   -- TLM: ???

