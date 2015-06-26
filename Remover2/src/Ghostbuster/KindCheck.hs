{-# LANGUAGE RecordWildCards #-}
-- | TODO: need to make this handle mutually recursive data definitions

module Ghostbuster.KindCheck where

import           Ghostbuster.Types
import           Ghostbuster.Examples.Feldspar
import qualified Ghostbuster.TypeCheck as GTC 
import qualified Data.Map as Map

-- Our environment for data constructors
type DEnv = Map.Map Var DDef

-- Our environment mapping types to kinds
type TKEnv = Map.Map Var Kind

kindCheck :: DDef -> DEnv -> Either TypeError ()
kindCheck d@DDef{..} env =
  -- All kept and synthesized vars must be of kind *
  if (allStars cVars) && (allStars sVars)
  -- Now check all the constructors for this datatype
  then case mapM (kindConstr d env) cases of
         Left a  -> Left $ "Failed to kindCheck data constructor: " ++ show a
         Right k -> Right ()
  else Left "Failed to infer proper kinds for C and S args for data constructor"
 where
   allStars :: [(TyVar, Kind)] -> Bool
   allStars x = foldl (&&) True $ map ((== Star) . snd) x

kindConstr :: DDef -> DEnv -> KCons -> Either TypeError ()
kindConstr parent@DDef{..} env constr@KCons{..} =
  -- Get the kind for each of the taus that lead up to this guy
  let flds   = mapM (kindType env (Map.fromList (kVars ++ cVars ++ sVars))) (map MonTy fields)
      -- Get the kinds for all the output types
      outpts = mapM (kindType env (Map.fromList (kVars ++ cVars ++ sVars))) (map MonTy outputs)
      -- Now get the kinds that we expect for all the outputs
      tConstrKinds = map snd $ kVars ++ cVars ++ sVars
   in case outpts of
        Right ks ->
          -- Now make sure that all the kinds that we expect the type
          -- constructor to be applied to are actually applied to it
          let allCorrect = foldl (\ b (expected,actual) -> b && (expected == actual))
                                 True $ zip tConstrKinds ks
          in if allCorrect then Right ()
             else Left $ "Invalid Kinds for type constructor " ++
                          show tyName ++ " Expected " ++ show tConstrKinds ++ " but received " ++ show ks
        Left err -> Left $ "Unable to infer kind for " ++ err ++ " in constructor " ++ show conName

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
    MonTy (ConTy kname monotys) -> error $ "ConTy is not implemented yet!"

kindProg :: Prog -> DEnv -> Either TypeError ()
kindProg = undefined
 -- Typecheck/infer
 -- Once we get the types go and run kindType on it


