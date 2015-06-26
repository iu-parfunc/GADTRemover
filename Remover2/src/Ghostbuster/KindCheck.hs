{-# LANGUAGE RecordWildCards #-}
-- | TODO: Need to make this handle mutually recursive data definitions
-- | TODO: How to deal with type variables that aren't bound by a quantifier? (ie., implicit foralls?)
--         OR can we always assume that any type variables will either be bound somewhere?

module Ghostbuster.KindCheck where

import           Ghostbuster.Types
import           Ghostbuster.Examples.Feldspar
import qualified Ghostbuster.TypeCheck as GTC 
import qualified Data.Map as Map

-- Our environment for data constructors
type DEnv = Map.Map Var DDef

-- Our environment mapping types to kinds
type TKEnv = Map.Map Var Kind

toDEnv :: [DDef] -> DEnv
toDEnv ls = Map.fromList $ zip (map tyName ls) ls

-- Check it out!
-- mapM (kindCheck (toDEnv primitiveTypes) (Map.fromList [(mkVar "b", Star)])) feldspar_gadt
kindCheck ::DEnv -> TKEnv -> DDef -> Either TypeError ()
kindCheck env tenv d@DDef{..} =
  -- All kept and synthesized vars must be of kind *
  if (allStars cVars) && (allStars sVars)
  -- Now check all the constructors for this datatype
  then case mapM (kindConstr d env tenv) cases of
         Left a  -> Left $ "Failed to kindCheck data constructor: " ++ show a
         Right k -> Right ()
  else Left "Failed to infer proper kinds for C and S args for data constructor"
 where
   allStars :: [(TyVar, Kind)] -> Bool
   allStars x = foldl (&&) True $ map ((== Star) . snd) x

kindConstr :: DDef -> DEnv -> TKEnv -> KCons -> Either TypeError ()
kindConstr parent@DDef{..} env tenv constr@KCons{..} =
  -- Get the kind for each of the taus that lead up to this guy
  let flds   = mapM (kindType env (tenv `Map.union` (Map.fromList (kVars ++ cVars ++ sVars)))) (map MonTy fields)
      -- Get the kinds for all the output types
      outpts = mapM (kindType env (tenv `Map.union` (Map.fromList (kVars ++ cVars ++ sVars)))) (map MonTy outputs)
      -- Now get the kinds that we expect for all the outputs
      tConstrKinds = map snd $ kVars ++ cVars ++ sVars
   in case outpts of
        Right ks ->
          -- Now make sure that all the kinds that we expect the type
          -- constructor to be applied to are actually applied to it
          if tConstrKinds == ks then Right ()
          else Left $ "Invalid Kinds for type constructor " ++
                       show tyName ++ " Expected " ++ show tConstrKinds ++ " but received " ++ show ks
        Left err -> Left $ "Unable to infer kind for " ++ err ++ " in constructor " ++ show conName

-- kindType Map.empty Map.empty kindTyScheme1
-- kindType Map.empty Map.empty kindTyScheme2
-- kindType Map.empty Map.empty kindTyScheme3
kindType :: DEnv -> TKEnv -> TyScheme -> Either TypeError Kind
kindType env tenv tscheme =
  case tscheme of
    ForAll tks mty       ->
      -- Add the variables bound by the forall into our type->kind env
      -- and recur with that info
      case kindType env ((Map.fromList tks) `Map.union` tenv) (MonTy mty) of
        Left err -> Left err
        Right k -> Right $ foldr ArrowKind k $ (map snd tks)
    MonTy (VarTy tyVar) ->
        -- Lookup this guy in our type->kind environment and see what we
        -- get. We should always find him, otherwise we have an unbound
        -- type variable
      case Map.lookup tyVar tenv of
        Nothing -> Left $ "Unbound type variable found! " ++ show tyVar
        Just k  -> Right k
    MonTy (ArrowTy monoTy1 monoTy2) -> do
      mtk1 <- kindType env tenv (MonTy monoTy1)
      mtk2 <- kindType env tenv (MonTy monoTy2)
      return $ ArrowKind mtk1 mtk2
    MonTy (TypeDictTy tname)        -> do
      -- According to our typing rules, this guy had beeter have kind * so
      -- enforce that here
      kindt <- kindType env tenv (MonTy (VarTy tname))
      if kindt /= Star
      then Left $ "TypeDict constructor requires types of kind *, but we received a type of kind " ++ show kindt
      else Right Star
    MonTy (ConTy tname monotys) -> do
      kinds <- mapM (kindType env tenv) $ map MonTy monotys
      case Map.lookup tname env of
        Nothing   -> Left $ "Unbound type constructor found! " ++ show tname
        Just ddef -> let tnameKinds = getTyArgs [ddef] tname
                     in if kinds == tnameKinds
                        then return Star -- Only allow fully applied type constructors for now
                        else Left $ "Invalide type constructor application: " ++ show kinds

kindProg :: Prog -> DEnv -> Either TypeError ()
kindProg = undefined
 -- Typecheck/infer
 -- Once we get the types go and run kindType on it


