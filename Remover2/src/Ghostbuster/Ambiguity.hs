{-# LANGUAGE NamedFieldPuns #-}
-- {-# OPTIONS_GHC -fno-warn-typed-holes #-}

-- |

module Ghostbuster.Ambiguity
       (ambCheck, ambCheckErr, AmbError) where

import           Control.Monad
import qualified Data.List as L
import qualified Data.Set as S
import           Debug.Trace
import           Ghostbuster.Types
import           Ghostbuster.Utils

type AmbError = TypeError

-- | Do a set of data type definitions, with their
-- keep/check/synthesize specifications meet the ambiguity
-- requirements?
ambCheck :: [DDef] -> Either AmbError ()
ambCheck defs = loop defs
  where
  loop [] = return ()
  loop (DDef {tyName, cases} : rest) =
    do addToErr ("When type checking type constructor: "++show tyName++"\n") $
         sequence_ $ map (checkKCons tyName (getArgStatus defs)) cases
       loop rest

ambCheckErr :: [DDef] -> ()
ambCheckErr defs =
  case ambCheck defs of
    Left e -> error e
    Right () -> ()

addToErr :: String -> Either String x -> Either String x
addToErr s (Left err) = Left (s++err)
addToErr _ (Right x)  = Right x

checkKCons :: TName -> (TName -> [TyStatus]) -> KCons -> Either AmbError ()
checkKCons myT getStatus KCons{conName,fields,outputs} =
  trace ("Splitting for constructor "++show myT++
         " with status "++show myStatus++ "\n  and outs "++show outputs) $
  addToErr ("When type checking data constructor: "++show conName++"\n") $
  do -- First, check that synthesized info can be recovered:
     forM_ ss $ \synthTau ->
       forM_ (S.toList (ftv synthTau)) $ \free ->
          checkSynthVar free
     -- Second, check that checked-arguments to recursive calls can be created:
     _ <- foldM (\acc field ->
                 do forM_ (S.toList $ inCheckedContext getStatus field) $ \checkedVar ->
                      checkChecked acc checkedVar
                    return $ S.union acc (ftv field)
                ) S.empty fields
     return ()
     -- map (checkSynthVar) ss
  where
  (ks,cs,ss)    = splitTyArgs myStatus outputs
  myStatus      = getStatus myT
  varsInKeep    = ftv ks
  varsInChecked = ftv cs

  -- everything but checked, in ALL fields:
  fieldInputs   = S.unions $ L.map (fvNonChecked getStatus) fields

  -- Non-erased vars:
  allNonErased  = S.unions $
                  varsInKeep :
                  map (nonErased getStatus) fields

  checkSynthVar v
    | S.member v varsInKeep    = return ()
    | S.member v varsInChecked = return ()
    | S.member v fieldInputs   = return ()
    | otherwise =
      Left $ "Ambiguous var in synthesized output position: "++show v++
             "\nNot found in kept output vars: "++show varsInKeep++
             "\nNot found in checked output vars: "++show varsInChecked++
             "\nNot found in relavant vars from fields: "++show fieldInputs

  checkChecked varsToTheLeft tyvar
    | S.member tyvar varsToTheLeft = return ()
    | S.member tyvar allNonErased = return ()
    | S.member tyvar varsInChecked = return ()
    | otherwise =
      Left $ "Ambiguous tyvar in checked poisiton within field: "++show tyvar++
             "\nNot found in type vars in fields on the left: "++show varsToTheLeft++
             "\nNot found in checked 'inputs': "++show varsInChecked++
             "\nNot found in non-erased vars: "++show allNonErased


-- | Partition type variables into (kept,checked,synth)
splitTyArgs :: Show t => [TyStatus] -> [t] -> ([t],[t],[t])
splitTyArgs myStatus outputs
  | length myStatus /= length outputs =
    error $ "splitTyArgs: mismatched lengths: "++ show (length myStatus, length outputs)++
            "\n  "++ show myStatus ++
            "\n  "++ show outputs
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

-- | Opposite of fvNonChecked, this returns type variables mentioned
-- in checked context.
inCheckedContext :: (TName -> [TyStatus]) -> MonoTy -> S.Set TyVar
inCheckedContext getStatus mt =
  case mt of
    (VarTy _) -> S.empty
    (ArrowTy x1 x2) -> S.union (lp x1) (lp x2)
    (ConTy ty args) ->
      -- return EVERYTHING under this checked branch:
      let (_,cs,_) = splitTyArgs (getStatus ty) args
      in ftv cs
    (TupleTy xs) -> S.unions $ map lp xs
    (TypeDictTy _tau) -> S.empty
 where
 lp = inCheckedContext getStatus

-- | Include nothing under checked or synth contexts.
nonErased :: (TName -> [TyStatus]) -> MonoTy -> S.Set TyVar
nonErased getStatus mt =
  case mt of
    (VarTy x) -> S.singleton x
    (ArrowTy x1 x2) -> S.union (lp x1) (lp x2)
    (ConTy ty args) ->
      let (k,_,_) = splitTyArgs (getStatus ty) args
      in S.unions (map lp k)
    (TupleTy xs) -> S.unions $ map lp xs
    (TypeDictTy _tau) -> S.empty
 where
 lp = nonErased getStatus
