{-# LANGUAGE NamedFieldPuns #-}
-- {-# OPTIONS_GHC -fno-warn-typed-holes #-}

-- |

module Ghostbuster.Ambiguity where

import Control.Monad
import qualified Data.Set as S
import Ghostbuster.Types
import Ghostbuster.Utils
import qualified Data.List as L


type AmbError = TypeError

-- | Do a set of data type definitions, with their
-- keep/check/synthesize specifications meet the ambiguity
-- requirements?
ambCheck :: [DDef] -> Either AmbError ()
ambCheck defs = loop defs
  where
  loop [] = return ()
  loop (DDef {tyName, cases} : rest) =
    do sequence_ $ map (checkKCons tyName (getArgStatus defs)) cases
       loop rest

checkKCons :: TName -> (TName -> [TyStatus]) -> KCons -> Either AmbError ()
checkKCons myT getStatus KCons{conName,fields,outputs} =
  do -- First, check that synthesized info can be recovered:
     forM_ ss $ \synthTau ->
       forM_ (S.toList (ftv synthTau)) $ \free ->
          checkSynthVar free
     -- Second, check that checked-arguments to recursive calls can be created:

     -- map (checkSynthVar) ss
  where
  (ks,cs,ss) = splitTyArgs myStatus outputs

  myStatus = getStatus myT

  varsInKeep = ftv ks
  varsInChecked = ftv cs

  fieldInputs = S.unions $ L.map (fvNonChecked getStatus) fields

  checkSynthVar v
    | S.member v varsInKeep    = return ()
    | S.member v varsInChecked = return ()
    | S.member v fieldInputs   = return ()
    | otherwise =
      Left $ "Ambiguous var in synthesized output position: "++show v++
             "\nNot found in kept output vars: "++show varsInKeep++
             "\nNot found in checked output vars: "++show varsInChecked++
             "\nNot found in relavant vars from fields: "++show fieldInputs

-- | Partition type variables into (kept,checked,synth)
splitTyArgs :: [TyStatus] -> [t] -> ([t],[t],[t])
splitTyArgs myStatus outputs
  | length myStatus /= length outputs = error "splitTyArgs: mismatched lengths."
  | otherwise  = (ks,cs,ss)
  where
  ks = [ x | (Keep,x)  <- wStatus ]
  cs = [ x | (Check,x) <- wStatus ]
  ss = [ x | (Synth,x) <- wStatus ]
  wStatus  = zip myStatus outputs

-- | Retrieve free type variables that do NOT occur in checked
-- position.
fvNonChecked :: (TName -> [TyStatus]) -> MonoTy -> S.Set TyVar
fvNonChecked getStatus mt =
  case mt of
    (VarTy x) -> S.singleton x
    (ArrowTy x1 x2) -> S.union (lp x1) (lp x2)
    (ConTy ty args) ->
      let (k,_,s) = splitTyArgs (getStatus ty) args
      in S.unions $ (map lp k) ++ (map lp s)
    (TupleTy xs) -> S.unions $ map lp xs
    (TypeDictTy _tau) -> S.empty
 where
 lp = fvNonChecked getStatus
