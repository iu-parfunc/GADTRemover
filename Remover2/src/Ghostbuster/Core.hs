{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}

module Ghostbuster.Core
  where

import Types 

toSealedName = \tyName -> "Sealed" ++ tyName

ghostbuster :: DDef -> Prog
ghostbuster ddef = Prog [sealed] [] "dummyvar" 
  where
  (ddefNoEquals, equalities) =  equalityRemoval ddef
  (ddefNoPatternM, patterns) = patternMatchingRemoval ddefNoEquals
  sealed = generateSealed ddef


generateSealed :: DDef -> DDef
generateSealed (DDef tyName k c s) = DDef (toSealedName tyName) k [] []
  [Kcons (toSealedName tyName) [((map typeDictForSynth synthVars) ++ conTy)] checkVars]
  where
  keepVars = map snd k
  checkVars = map snd c
  synthVars = map snd s
  typeDictForSynth = \var -> (TypeDictTy var)
  conTy = ConTy tyName (keepVars ++ checkVars ++ synthVars) 
