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
  , FunBind body
  ]
  where
    body = case valExp of
      -- If we have a top-level (f = \x -> case x of ...), unfold this
      -- into a series of top-level pattern matches.
      ELam (x,_) (ECase x' es)
        | G.EVar x == x' -> map (uncurry (topLevelCase valName)) es

      _ -> [topLevelFun valName valExp]


-- Convert a type scheme into a type signature
--
mkTypeSig :: Var -> TyScheme -> Decl
mkTypeSig ident (ForAll a t)
  = TypeSig noLoc [varName ident]
  $ TyForall (Just (map (uncurry mkTyVarBind) a)) [] (mkType t)


topLevelCase :: Var -> G.Pat -> G.Exp -> Match
topLevelCase fn p e =
  Match
    noLoc                       -- source location
    (varName fn)                -- name of the function
    [mkPat p]                   -- patterns, to be matched against a value
    Nothing                     -- type signature
    (mkRhs e)                   -- the right hand side of the function, pattern, or case alternative
    (BDecls [])                 -- binding group for let or where clause

topLevelFun :: Var -> G.Exp -> Match
topLevelFun fn e =
  Match
    noLoc
    (varName fn)
    []
    Nothing
    (mkRhs e)
    (BDecls [])

