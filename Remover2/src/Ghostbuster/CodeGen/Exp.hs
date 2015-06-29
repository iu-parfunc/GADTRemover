
module Ghostbuster.CodeGen.Exp
  where

import Ghostbuster.Types                                as G
import Ghostbuster.CodeGen.Base                         as G

import Language.Haskell.Exts                            as H
import Language.Haskell.Exts.SrcLoc                     ( noLoc )


-- Convert a Ghostbuster expression into Haskell expression
--
mkExp :: G.Exp -> H.Exp
mkExp (G.EK n)                  = var (varName n)                               -- TLM ???
mkExp (G.EVar n)                = var (varName n)
mkExp (G.ELam (x,_) b)          = lamE noLoc [mkPat (Pat x [])] (mkExp b)       -- TLM: add local type signature?
mkExp (G.EApp a b)              = app (mkExp a) (mkExp b)
mkExp (G.ECase e ps)            = caseE (mkExp e) (map (uncurry mkAlt) ps)
mkExp (G.ELet (v,t,bnd) body)   = letE [ mkTypeSig v t, mkDeclOfExp v bnd ] (mkExp body)
-- mkExp _                 = error "TODO"
mkExp (G.EDict{})      = error "EDict: not handled by codegen"
mkExp (G.ECaseDict {}) = error "ECaseDict: not handled by codegen"
mkExp (G.EIfTyEq {})   = error "EIfTyEq: not handled by codegen"

mkAlt :: G.Pat -> G.Exp -> H.Alt
mkAlt p e =
  Alt noLoc (mkPat p) (mkRhs e) (BDecls [])

mkPat :: G.Pat -> H.Pat
mkPat (Pat pn pv) = pApp (varName pn) (map (pvar . varName) pv)

mkRhs :: G.Exp -> H.Rhs
mkRhs = UnGuardedRhs . mkExp

-- Convert a type scheme into a type signature
--
mkTypeSig :: Var -> TyScheme -> Decl
mkTypeSig ident (ForAll a t)
  = TypeSig noLoc [varName ident]
  $ TyForall (Just (map (uncurry mkTyVarBind) a)) [] (mkType t)

-- Create a (top-level) declaration for an expression
--
mkDeclOfExp :: Var -> G.Exp -> Decl
mkDeclOfExp n e
  = FunBind
  $ case e of
      -- If we have a top-level (f = \x -> case x of ...), unfold this
      -- into a series of top-level pattern matches.
      ELam (x,_) (ECase x' es)
        | G.EVar x == x' -> map (uncurry (expandCaseOfExp n)) es

      -- Otherwise, just a single match expression
      _ -> [matchOfExp n e]


expandCaseOfExp :: Var -> G.Pat -> G.Exp -> Match
expandCaseOfExp fn p e =
  Match
    noLoc                       -- source location
    (varName fn)                -- name of the function
    [mkPat p]                   -- patterns, to be matched against a value
    Nothing                     -- type signature
    (mkRhs e)                   -- the right hand side of the function, pattern, or case alternative
    (BDecls [])                 -- binding group for let or where clause

matchOfExp :: Var -> G.Exp -> Match
matchOfExp fn e =
  Match
    noLoc
    (varName fn)
    []
    Nothing
    (mkRhs e)
    (BDecls [])
