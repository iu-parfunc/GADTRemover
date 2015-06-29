{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}

module Ghostbuster.Core
  where

import Ghostbuster.Types
import qualified Data.Map as HM

type Equations = (HM.Map TyVar [TyVar])
type Patterns = (HM.Map TyVar MonoTy)

toSealedName = \tyName -> mkVar ("Sealed" ++ (unMkVar tyName))

ghostbuster :: [DDef] -> Prog
ghostbuster ddef = Prog [sealed] [] "dummyvar" 
  where
  (ddefNoEquals, equalities) =  equalityRemoval ddef
  (ddefNoPatternM, patterns) = patternMatchingRemoval ddefNoEquals
  sealed = generateSealed ddef


generateSealed :: DDef -> DDef
generateSealed (DDef tyName k c s cases) = DDef (toSealedName tyName) k [] []
  [KCons (toSealedName tyName) ((map typeDictForSynth synthVars) ++ conTy) (map toVarTy (keepVars ++ checkVars))]
  where
  keepVars = map fst k
  checkVars = map fst c
  synthVars = map fst s
  typeDictForSynth = \var -> (TypeDictTy var)
  conTy = [ConTy tyName (map toVarTy (keepVars ++ checkVars ++ synthVars))]

equalityRemoval :: DDef -> (DDef, [Equations])
equalityRemoval = undefined

patternMatchingRemoval :: DDef -> (DDef, [Patterns])
patternMatchingRemoval = undefined
