{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}

module Ghostbuster.Core
--  ( ghostbuster
--  , ghostbusterDDef )
  where

import Ghostbuster.Types
import Ghostbuster.Utils
import qualified Data.Map as HM
import Data.String

type Equations = (HM.Map TyVar [TyVar])
type Patterns = (HM.Map TyVar MonoTy)

toSealedName :: Var -> Var
toSealedName tyName = mkVar ("Sealed" ++ (unMkVar tyName))

-- | The name of the down-conversion function.
downName :: TName -> TermVar
downName tyName = mkVar ("down" ++ (unMkVar tyName))

-- | Take a type or data constructor from the higher (pre-stripping)
-- type to the lower one.
primeName :: Var -> Var
primeName tyName = mkVar ((unMkVar tyName) ++ "'")


ghostbuster :: [DDef] -> Prog
ghostbuster ddefs = Prog (ddefs ++ ddefsNew) vdefsNew (EK "Nothing")
  where
  allddefs = ddefs ++ primitiveTypes
  bustedDefs = [ dd | dd@DDef {cVars,sVars} <- allddefs
                    , not (null cVars) || not (null sVars) ]

  result = map ghostbusterDDef bustedDefs
  ddefsNew = concat (map fst result)
  vdefsNew = concat (map snd result)

  ghostbusterDDef :: DDef -> ([DDef], [VDef])
  ghostbusterDDef ddef = (returnDDefs, returnVDefs)
    where
    ddefStripped = gadtToStripped allddefs ddef
    (ddefNoEquals, equalities) =  equalityRemoval ddef
    (ddefNormilized, patterns) = pmRemoval ddefNoEquals
    sealed = generateSealed ddef
    returnDDefs = [ddefStripped, sealed]   -- at the moment, these two.
    returnVDefs = [generateDown allddefs (tyName ddef)
                  , generateUpcast allddefs patterns equalities ddefNormilized
                  ]

gadtToStripped :: [DDef] -> DDef -> DDef
gadtToStripped alldefs ddef = ddef {tyName = (gadtDownName (tyName ddef)), kVars= [], cVars = [], sVars = (sVars ddef), cases = strippedCases}
  where
  strippedCases = map (gadtToStrippedByClause alldefs) (cases ddef)

gadtDownName :: TName -> TName
gadtDownName tyname = mkVar ((unMkVar tyname) ++ "'")

gadtToStrippedByClause :: [DDef] -> KCons -> KCons
gadtToStrippedByClause alldefs clause = clause {conName = gadtDownName (conName clause), fields = (map toTypeDictWrap (getKConsDicts alldefs (conName clause)) ++ (map (gadtToStrippedByMono alldefs) (fields clause))), outputs = (map (gadtToStrippedByMono alldefs) (outputs clause))}
  where
  toTypeDictWrap = \var -> TypeDictTy var

gadtToStrippedByMono :: [DDef] -> MonoTy -> MonoTy
gadtToStrippedByMono alldefs monoty = case monoty of
  ArrowTy mono1 mono2 -> ArrowTy (gadtToStrippedByMono alldefs mono1) (gadtToStrippedByMono alldefs mono2)
  ConTy tname monos -> ConTy (gadtDownName tname) (map (gadtToStrippedByMono alldefs) (onlyKeep alldefs tname monos))
  _ -> monoty

onlyKeep :: [DDef] -> TName -> [MonoTy] -> [MonoTy]
onlyKeep alldefs tname monos = take (numberOfKeep alldefs tname) monos

generateSealed :: DDef -> DDef
generateSealed (DDef tyName k c s _cases) = 
    DDef (toSealedName tyName) k [] []
     [ KCons (toSealedName tyName)
             ((map typeDictForSynth synthVars) ++ conTy)
             (map toVarTy (keepVars ++ checkVars)) ]
  where
  keepVars  = map fst k
  checkVars = map fst c
  synthVars = map fst s
  allVars   = keepVars ++ checkVars ++ synthVars
  typeDictForSynth var = (TypeDictTy var)
  conTy = [ConTy tyName (map toVarTy allVars)]

equalityRemoval :: DDef -> (DDef, [Equations])
equalityRemoval ddef = (ddef {cases = newcases} , patterns)
   where
   (newcases, patterns) = unzip (map equalityRemovalByClause (cases ddef))

equalityRemovalByClause :: KCons -> (KCons, Equations)
equalityRemovalByClause clause = (clause {fields = newfields, outputs = newoutputs} , equations2)
  where
  (newfields, equations1) = equalityRemovalMonoList (fields clause) HM.empty
  (newoutputs, equations2) = equalityRemovalMonoList (outputs clause) equations1

equalityRemovalMonoList :: [MonoTy] -> Equations -> ([MonoTy], Equations)
equalityRemovalMonoList [] _equations = ([], HM.empty)
equalityRemovalMonoList (mono:rest) equations = (newmono:newrest, equations2)
  where
  (newmono, equations1) = equalityRemovalMono mono equations
  (newrest, equations2) = equalityRemovalMonoList rest equations1

equalityRemovalMono :: MonoTy -> Equations -> (MonoTy, Equations)
equalityRemovalMono monoty equations = case monoty of
  VarTy var -> case HM.lookup var equations of
     Just listOfVars -> (toVarTy newvar, HM.insert var (newvar:listOfVars) equations)
     Nothing -> (monoty, HM.insert var [] equations)
  ArrowTy mono1 mono2 -> ((ArrowTy mono1' mono2'), equations2)
     where
     (mono1', equations1) = equalityRemovalMono mono1 equations
     (mono2', equations2) = equalityRemovalMono mono2 equations1
  ConTy name monos -> ((ConTy name newmonos), equations1)
     where
     (newmonos, equations1) = equalityRemovalMonoList monos equations
  _ -> (monoty, HM.empty)
  where
  newvar = (mkVar "newVar")

pmRemoval :: DDef -> (DDef, [Patterns])
pmRemoval ddef = (ddef {cases = newcases} , patterns)
   where
   (newcases, patterns) = unzip (map pmRemovalByClause (cases ddef))

pmRemovalByClause :: KCons -> (KCons, Patterns)
pmRemovalByClause clause = (clause {fields = newfields, outputs = newoutputs} , patterns)
  where
  (newfields, pattern1) = unzip (map pmRemovalMono (fields clause))
  (newoutputs, pattern2) = unzip (map pmRemovalMono (outputs clause))
  patterns = HM.union (HM.unions pattern1) (HM.unions pattern2)

pmRemovalMono :: MonoTy -> (MonoTy, Patterns)
pmRemovalMono monoty = case monoty of
  ArrowTy mono1 mono2 -> (toVarTy newvar, patterns)
     where
     (mono1', pattern1) = pmRemovalMono mono1
     (mono2', pattern2) = pmRemovalMono mono2
     patterns = HM.insert newvar (ArrowTy mono1' mono2') (HM.union pattern1 pattern2)
  ConTy name monos -> (toVarTy newvar, patterns)
     where
     (newmonos, pattern1) = unzip (map pmRemovalMono monos)
     patterns = HM.insert newvar (ConTy name newmonos) (HM.unions pattern1)
  _ -> (monoty, HM.empty)
  where
  newvar = (mkVar "newVr")

generateUpcast :: [DDef] -> [Patterns] -> [Equations] -> DDef -> VDef
generateUpcast alldefs patterns equalities ddef = VDef {valName = upcastname, valTy = signature, valExp = bodyOfUp}
  where
  upcastname = (upCastName (tyName ddef))
  signature = ForAll onlyKeepAndCheck (ArrowTy (ConTy (gadtDownName (tyName ddef)) onlyKeepVars) (ConTy "Maybe" [ConTy (toSealedName (tyName ddef)) onlyKeepAndCheckVars]))
  onlyKeepAndCheck = (kVars ddef) ++ (cVars ddef)
  onlyKeepAndCheckVars = (map toVarTy (map fst onlyKeepAndCheck))
  onlyKeepVars = (map toVarTy (map fst (kVars ddef)))
  bodyOfUp = ELam ("x", ConTy (gadtDownName (tyName ddef)) []) (ECase "x" (map (generateUpcastByClause patterns equalities) (cases ddef)))

generateUpcastByClause :: [Patterns] -> [Equations] -> KCons -> (Pat,Exp)
generateUpcastByClause patterns equalities clause = ((Pat (gadtDownName (conName clause)) newVars), generateUpcastMono 1 patterns equalities (fields clause) (outputs clause))
  where
  newVars = ["x"]  -- to change in x1 x2 x3.. 

generateUpcastMono :: Int -> [Patterns] -> [Equations] -> [MonoTy] -> [MonoTy] -> Exp
generateUpcastMono n patterns equalities [] conclusion = undefined -- here generate patternmatching, equalities, and the finish with (EApp "SealedTyp" (EApp (EApp "Arr" "a") "b" )))
generateUpcastMono n patterns equalities (mono:rest) conclusion = case mono of
  ConTy name monos -> (ECase (EApp (EVar (upCastName name)) (EVar (mkVar ("x" ++ (show n))))) [(Pat (toSealedName name) (map toVarFromMono monos), (generateUpcastMono (n+1) patterns equalities rest conclusion))])

toVarFromMono :: MonoTy -> Var
toVarFromMono (VarTy var) = var

upCastName :: Var -> Var
upCastName tyname = mkVar ("upCast" ++ (unMkVar tyname))


-- | Create a down-conversion function.  This is a simple tree-walk
-- over the input datatype, without any laborious type checking
-- obligations to discharge.
generateDown :: [DDef] -> TName -> VDef
generateDown alldefs which =
  VDef down (ForAll allVars (mkFunTy (dictTys ++ [startTy]) endTy)) $
   mkLams params $
    ECase "orig" $
    [ (Pat conName args,
      appLst (EVar (primeName conName)) $
       -- FIXME: We need some analysis here that applies a permutation
       -- between tyvars in the KCons and tyvars in the "T a b c" data decl.
       (map (EVar . dictArgify) newDicts) ++
         -- (map EDict newDicts) ++
      [ (dispatch arg ty)
      | (arg,ty) <- zip args fields ])
    | KCons {conName,fields} <- cases
    , let args = (take (length fields) patVars)
          newDicts = getKConsDicts alldefs conName
    ]
  where
  params = [ (d, TypeDictTy t) | (d,t) <- zip dictArgs erased ] ++
           [("orig",startTy)]

  dictArgify = (+++ "_dict")
  dictArgs = map dictArgify erased

  erased = map fst $ cVars ++ sVars
  dictTys = map TypeDictTy erased
  DDef {tyName,kVars,cVars,sVars, cases} = lookupDDef alldefs which

  down    = (downName tyName)
  startTy = (ConTy tyName  (map (VarTy . fst) allVars))
  endTy   = (ConTy tyName' (map (VarTy . fst) kVars))
  tyName' = primeName tyName
  allVars = kVars++cVars++sVars

  -- For a type T_i, we dispatch to downT_i
  -- FIXME: We need to add extra dictionary arguments here.
  dispatch vr (ConTy name _)
    | name == which = appLst (EVar (downName name))
                             (map EVar $ dictArgs++[vr])
    | otherwise = error$  "generateDown: UNFINISHED: need some logic here to dispatch a call to "
                  ++ show name ++" while providing the right dictionary arguments."
  -- If we just have an abstract type, we return it.  No recursions.
  dispatch vr (VarTy _)       = EVar vr
  -- For now functions are left alone.  Later we should generate proxies.
  dispatch vr (ArrowTy _ _)   = EVar vr

  -- Are dicts ALLOWED in the input program, or just the output?
  -- For now they are allowed...
  dispatch vr (TypeDictTy _)  = EVar vr
