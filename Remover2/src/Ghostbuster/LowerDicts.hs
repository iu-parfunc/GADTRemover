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
  Prog [dictGADT] [] main
  where
  allDicts = S.toList $ S.unions $
             gatherDicts main :
             [ gatherDicts valExp | VDef {valExp} <- vdefs ]

  dictGADT =
    DDef "TypeDict" [("a",Star)] [] []
    [ KCons name
            [ ConTy "TypeDict" [VarTy $ mkVar [c]]
            | (c) <- letters ]
            [ (ConTy name []) ]
    | tn <- allDicts
    , let name = (dictConsName tn)
          letters = map fst $ zip ['a' ..] (getArgStatus ddefs tn)
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


--------------------------------------------------------------------------------
-- Naming conventions

dictConsName :: Var -> Var
dictConsName (Var v) = Var (v `B.append` "Dict")
