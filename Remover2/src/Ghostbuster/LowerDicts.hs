{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Rewrite dictionary primitives as explicit datatype operations.

module Ghostbuster.LowerDicts where

import qualified Data.Set as S
import qualified Data.ByteString.Char8 as B
import Ghostbuster.Types
import Ghostbuster.Utils

-- | This operates on a whole program, processing all occurences of
-- `ECaseDict`
lowerDicts :: Prog -> Prog
lowerDicts (Prog ddefs vdefs main) =
  Prog (dictGADT : reflDef : ddefs)
       (mkTeq allDicts : vdefs')
       main
  where
  vdefs' = [ VDef v t (doExp e) | VDef v t e <- vdefs ]

  allDicts = S.toList $ S.unions $
             gatherDicts main :
             [ gatherDicts valExp | VDef {valExp} <- vdefs ]

  dictGADT =
    DDef "TypeDict" [("a",Star)] [] []
    [ KCons name
            [ ConTy "TypeDict" [VarTy $ mkVar c]
            | (c) <- letters ]
            [ (ConTy name (map (VarTy . mkVar) letters)) ]
    | tn <- allDicts
    , let name = (dictConsName tn)
          letters = map (\(c,_) -> [c]) $
                    zip ['a' ..] (getArgStatus ddefs tn)
   ]

-- | Keep the output a little smaller by not generating dictionaries
-- for EVERY type constructor, only those that are reefiied somewhere
-- in the program.
gatherDicts :: Exp -> S.Set TName
gatherDicts e =
  case e of
    (EK _)        -> S.empty
    (EVar _)      -> S.empty
    (ELam _ x)    -> gatherDicts x
    (EApp x1 x2)  -> S.union (gatherDicts x1) (gatherDicts x2)
    (ELet (_,_,x1) x2) -> S.union (gatherDicts x1) (gatherDicts x2)
    (ECase x1 ls) -> S.unions $ (gatherDicts x1) :
                                (map (gatherDicts . snd) ls)
    (EDict t)     -> S.singleton t
    (ECaseDict x1 (_,_,x2) x3) ->
      S.unions [gatherDicts x1, gatherDicts x2, gatherDicts x3]
    (EIfTyEq (x1,x2) x3 x4) ->
      S.unions [ gatherDicts x1, gatherDicts x2,
                 gatherDicts x3, gatherDicts x4 ]


doExp :: Exp -> Exp
doExp e =
  case e of
    (EDict x) -> EK $ dictConsName x
    (ECaseDict x1 (name,vars,x2) x3) ->
      -- If we don't have "_ ->" fall-through cases, then we would need
      -- to provide a pattern for ALL of the cases of TypeDict, and so we
      -- probably want to let-bind "x3" if it's non-trivial.
      --
      -- TODO: refactor this into a combinator for let-binding-non-trivial.
      -- TODO: this pass also needs to be in a monad that can generate names.
      ELet ("otherwise", recoverType, go x3) $
      ECase (go x1)
            [ (Pat (dictConsName name) vars , go x2)
             -- TODO: otherwise case for EVERY other dictionary.
            ]

    (EIfTyEq x1 x2 x3) -> undefined

    -- Boilerplate:
    ----------------------------
    (EK x)       -> EK x
    (EVar x)     -> EVar x
    (ELam x1 x2) -> ELam x1 (go x2)
    (EApp x1 x2) -> EApp (go x1) (go x2)
    (ELet (v,t,x1) x2) -> ELet (v,t,go x1) (go x2)
    (ECase x1 x2) -> ECase (go x1) [ (p,go x) | (p,x) <- x2]
 where
  go = doExp

-- If we hoist things out with ELet, then we need to have their type.
-- This should go in the type checking module.
recoverType = undefined

-- Generate a definition for a type-equality-checking function.
mkTeq :: [TName] -> VDef
mkTeq tns = VDef "checkTEQ" typesig $
            ELam ("x", typeDict "a") $
            ELam ("y", typeDict "b") $
            EK "UNFINISHED"
 where
 typesig = ForAll [] (typeDict "t" `ArrowTy`
                      typeDict "u" `ArrowTy`
                      ConTy "Maybe" [ConTy "TyEquality" ["t","u"]])


reflDef :: DDef
reflDef = DDef "TyEquality" [("a",Star),("b",Star)] [] []
          [KCons "Refl" [] ["a","a"]]


--------------------------------------------------------------------------------
-- Naming conventions

dictConsName :: Var -> Var
dictConsName (Var v) = Var (v `B.append` "Dict")


typeDict :: MonoTy -> MonoTy
typeDict x = ConTy "TypeDict" [x]
