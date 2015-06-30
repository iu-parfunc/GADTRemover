{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Rewrite dictionary primitives as explicit datatype operations.

module Ghostbuster.LowerDicts
  (lowerDicts, gatherDicts) where

import           Control.Exception
import qualified Data.ByteString.Char8 as B
import           Data.Char (isAlpha)
import           Data.List as L
import qualified Data.Set as S
-- import           Debug.Trace
import           Ghostbuster.Types
import           Ghostbuster.Utils

-- | This operates on a whole program, processing all occurences of
-- `ECaseDict`
lowerDicts :: Prog -> Prog
lowerDicts origprog@(Prog ddefs vdefs main) =
  -- trace ("LowerDicts: allDicts = "++show allDicts ) $
  assert (length ddefSubset == length allDicts) $
  if null allDicts
     then origprog
     else finalProg
  where
  finalProg = Prog (dictGADT : reflDef : ddefs)
                   (mkTeq ddefSubset : vdefs')
                   (doExp ddefSubset main)

  vdefs' = [ VDef v t (doExp ddefSubset e)
           | VDef v t e <- vdefs ]

  allDicts = S.toList allDictsSet
  allDictsSet = gatherDicts origprog
  ddefSubset = [ dd | dd@DDef{tyName} <- ddefs ++ primitiveTypes
                    , S.member tyName allDictsSet ]

  dictGADT =
    DDef "TypeDict" [("a",Star)] [] []
    [ KCons name
            [ ConTy "TypeDict" [VarTy $ mkVar c]
            | (c) <- letters ]
            [ (ConTy tn (map (VarTy . mkVar) letters)) ]
    | tn <- allDicts
    , let name = (dictConsName tn)
          letters = map (\(c,_) -> [c]) $
                    zip ['a' ..] (getArgStatus ddefs tn)
   ]

-- | Gather all the type constructor names whose dictionaries are
-- refied or tested against.
gatherDicts :: Prog -> S.Set TName
gatherDicts (Prog _ vdefs main) =
   S.unions $
   gatherExp main :
   [ gatherExp valExp
   | VDef {valExp} <- vdefs ]

-- | Keep the output a little smaller by not generating dictionaries
-- for EVERY type constructor, only those that are reefiied somewhere
-- in the program.
gatherExp :: Exp -> S.Set TName
gatherExp e =
  case e of
    (EK _)        -> S.empty
    (EVar _)      -> S.empty
    (ELam _ x)    -> gatherExp x
    (EApp x1 x2)  -> S.union (gatherExp x1) (gatherExp x2)
    (ELet (_,_,x1) x2) -> S.union (gatherExp x1) (gatherExp x2)
    (ECase x1 ls) -> S.unions $ (gatherExp x1) :
                                (map (gatherExp . snd) ls)
    (EDict t)     -> S.singleton t
    (ECaseDict x1 (pat,_,x2) x3) ->
      S.insert pat $
      S.unions [gatherExp x1, gatherExp x2, gatherExp x3]
    (EIfTyEq (x1,x2) x3 x4) ->
      S.unions [ gatherExp x1, gatherExp x2,
                 gatherExp x3, gatherExp x4 ]

-- | Takes only the DDefs which are modeled in TypeDict
doExp :: [DDef] -> Exp -> Exp
doExp ddefs e =
  case e of

    -- (1) Dict reification is just calling a data constructor!
    (EDict x) -> EK $ dictConsName x

    -- (2) Dict pattern matching becomes regular pattern matching.
    (ECaseDict x1 (name,vars,x2) x3) ->
      -- If we don't have "_ ->" fall-through cases, then we would need
      -- to provide a pattern for ALL of the cases of TypeDict, and so we
      -- probably want to let-bind "x3" if it's non-trivial.
      --
      letBindNonTriv (go x3) $ \x3' ->
       -- leftleftLambda (go x1) (ConTy "TypeDict" ["any"]) $ \x1' ->
       -- funBindLet (go x1) (ConTy "TypeDict" ["any"]) $ \x1' ->
       ECase (go x1) $
             [ (Pat (dictConsName name) vars , go x2)
             ] ++ -- otherwise case for EVERY other dictionary:
             [ (Pat (dictConsName oth) vars', x3')
             | oth <- allDicts, oth /= name
             , let vars' = take (length $ getArgStatus ddefs oth)
                                (patVars)
             ]

    -- (3) Equality tests call the out-of-line library function that
    -- we generate on the side.
    (EIfTyEq (x0,x1) x2 x3) ->
      unpackJustRefl (app2 "checkTEQ" (go x0) (go x1))
                     (go x2)
                     (go x3)

    -- Boilerplate:
    ----------------------------
    (EK x)       -> EK x
    (EVar x)     -> EVar x
    (ELam x1 x2) -> ELam x1 (go x2)
    (EApp x1 x2) -> EApp (go x1) (go x2)
    (ELet (v,t,x1) x2) -> ELet (v,t,go x1) (go x2)
    (ECase x1 x2) -> ECase (go x1) [ (p,go x) | (p,x) <- x2]
 where
  allDicts = L.map tyName ddefs
  go = doExp ddefs


unpackJustRefl :: Exp -> Exp -> Exp -> Exp
unpackJustRefl ex conseq altern =
  ECase ex
    [ ( Pat "Just"    ["Refl"], conseq)
    , ( Pat "Nothing" [],       altern)
    ]


app2 :: Exp -> Exp -> Exp -> Exp
app2 f x y = EApp (EApp f x) y


-- | Potentially infinite list of temporary pattern vars:
-- TODO: replace with freshenVar of a single root name.
patVars :: [Var]
patVars = map (\c -> mkVar [c]) $
          filter isAlpha ['a'..]

-- | Generate a definition for a type-equality-checking function.
--   Takes only the DDefs which are modeled in TypeDict.
--
--   The code size here will be quadratic in the number of constructors of TypeDict.
mkTeq :: [DDef] -> VDef
mkTeq ddefs = VDef "checkTEQ" typesig $
              ELam ("x", typeDict "a") $
              ELam ("y", typeDict "b") $
              ECase "x"
               [ (Pat (dictConsName tyName) patVs, makeInner tyName patVs)
               | dd@DDef{tyName} <- ddefs
               , let patVs = (mkPatVars dd "1")
               ]
 where

 mkPatVars DDef{kVars,cVars,sVars} suff =
   let arity = length kVars + length cVars + length sVars
   in map (+++ suff) $ take arity patVars

 -- Construct the inner of the two-step pattern match:
 makeInner outerT outerPatVs =
   ECase "y" [ (Pat (dictConsName tn) innerPatVs
               , if tn == outerT
                    then doRecurs $ zip outerPatVs innerPatVs
                    else (EK "Nothing"))
             | dd@DDef{tyName=tn} <- ddefs
             , let innerPatVs = (mkPatVars dd "2")
                   doRecurs [] = justRefl
                   doRecurs ((a,b):rst) =
                     unpackJustRefl (app2 "checkTEQ" (EVar a) (EVar b))
                                    (doRecurs rst)
                                    (EK "Nothing")
             ]

 justRefl = EApp (EK "Just") (EK "Refl")

 typesig = ForAll [] (typeDict "t" `ArrowTy`
                     (typeDict "u" `ArrowTy`
                      ConTy "Maybe" [ConTy "TyEquality" ["t","u"]]))

reflDef :: DDef
reflDef = DDef "TyEquality" [("a",Star),("b",Star)] [] []
          [KCons "Refl" [] ["a","a"]]


--------------------------------------------------------------------------------
-- Naming conventions

dictConsName :: Var -> Var
dictConsName (Var v) = Var (v `B.append` "Dict")


typeDict :: MonoTy -> MonoTy
typeDict x = ConTy "TypeDict" [x]


(+++) :: Var -> Var -> Var
(+++) (Var x) (Var y) = Var (x `B.append` y)
