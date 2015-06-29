
module Ghostbuster.CodeGen.Exp
  where

import Ghostbuster.Types                                as G
import Ghostbuster.CodeGen.Base                         as G

import Language.Haskell.Exts                            as H
import Language.Haskell.Exts.SrcLoc                     ( noLoc )


-- Convert a Ghostbuster expression into Haskell expression
--
mkExp :: G.Exp -> H.Exp
mkExp (G.EK n)          = var (varName n)                               -- TLM ???
mkExp (G.EVar n)        = var (varName n)
mkExp (G.ELam (x,_) b)  = lamE noLoc [mkPat (Pat x [])] (mkExp b)       -- TLM: add local type signature?
mkExp (G.EApp a b)      = app (mkExp a) (mkExp b)
mkExp (G.ECase e ps)    = caseE (mkExp e) (map (uncurry mkAlt) ps)
-- mkExp _                 = error "TODO"

mkAlt :: G.Pat -> G.Exp -> H.Alt
mkAlt p e =
  Alt noLoc (mkPat p) (mkRhs e) (BDecls [])

mkPat :: G.Pat -> H.Pat
mkPat (Pat pn pv) = pApp (varName pn) (map (pvar . varName) pv)

mkRhs :: G.Exp -> H.Rhs
mkRhs = UnGuardedRhs . mkExp

