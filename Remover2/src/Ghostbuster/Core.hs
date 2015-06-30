{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}

module Ghostbuster.Core
  ( ghostbuster
  , ghostbusterDDef )
  where

import Ghostbuster.Types
import Ghostbuster.Utils
import qualified Data.Map as HM

type Equations = (HM.Map TyVar [TyVar])
type Patterns = (HM.Map TyVar MonoTy)

toSealedName :: Var -> Var
toSealedName tyName = mkVar ("Sealed" ++ (unMkVar tyName))

ghostbuster :: [DDef] -> Prog
ghostbuster ddefs = Prog ddefsNew vdefsNew (EK "Nothing")
  where
  result = map ghostbusterDDef ddefs
  ddefsNew = concat (map fst result)
  vdefsNew = concat (map snd result)


ghostbusterDDef :: DDef -> ([DDef], [VDef])
ghostbusterDDef ddef = (returnDDefs, returnVDefs)
  where
  (ddefNoEquals, _equalities) =  equalityRemoval ddef
  (ddefNoPatternM, _patterns) = pmRemoval ddefNoEquals
  sealed = generateSealed ddef
  returnDDefs = [sealed, ddefNoPatternM]   -- at the moment, these two.
  returnVDefs = []                         -- to be fed later.


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
