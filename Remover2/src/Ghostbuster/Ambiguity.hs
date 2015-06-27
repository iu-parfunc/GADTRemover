{-# LANGUAGE NamedFieldPuns #-}
-- |

module Ghostbuster.Ambiguity where

import Control.Monad
import qualified Data.Set as S
import Ghostbuster.Types
import Ghostbuster.Utils

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

checkKCons :: TName -> (TName -> [TyArgStatus]) -> KCons -> Either AmbError ()
checkKCons myT getStatus KCons{conName,fields,outputs} =
  forM_ ss $ \synthTau ->
    forM_ (S.toList (ftv synthTau)) $ \free ->
       undefined
  -- map (checkSynthVar) ss
  where
  ks = [ x | (Keep,x) <- wStatus ]
  cs = [ x | (Check,x) <- wStatus ]
  ss = [ x | (Synth,x) <- wStatus ]

  wStatus  = zip myStatus outputs
  myStatus = getStatus myT
