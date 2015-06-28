{-# LANGUAGE RecordWildCards #-}
-- | TODO: Need to make this handle mutually recursive data definitions

module Ghostbuster.KindCheck
       ( kindProg
       , kindClosedDefs
       ) where

import           Ghostbuster.Types
-- import           Ghostbuster.Examples.Feldspar
-- import qualified Ghostbuster.TypeCheck as GTC
import           Ghostbuster.Utils (getTyArgs)
import qualified Data.Map as Map
import Control.Monad

-- Our environment for data constructors
type DEnv = Map.Map TName DDef

-- Our environment mapping type variables to kinds
type TKEnv = Map.Map TyVar Kind

toDEnv :: [DDef] -> DEnv
toDEnv ls = Map.fromList $ zip (map tyName ls) ls

kindClosedDefs :: [DDef] -> Either TypeError ()
kindClosedDefs defs =
  do _ <- kindCheckDDefs (toDEnv defs) Map.empty defs
     return ()

-- | This is for checking multiple DDefs at once that we see. We assume for
--   now that something will not be refered to until it has been defined.
--   kindCheckDDefs (toDEnv primitiveTypes) (Map.fromList [(mkVar "b", Star)]) feldspar_gadt
kindCheckDDefs :: DEnv -> TKEnv -> [DDef] -> Either TypeError DEnv
kindCheckDDefs denv tkenv (ddef : defs) = do
  newEnv <- kindCheck denv tkenv ddef
  kindCheckDDefs newEnv tkenv defs
kindCheckDDefs denv _ [] = return denv

-- Check it out!
-- mapM (kindCheck (toDEnv (dd2 : dd3 : primitiveTypes)) (Map.fromList [(mkVar "b", Star)])) feldspar_gadt
kindCheck :: DEnv -> TKEnv -> DDef -> Either TypeError DEnv
kindCheck env tenv d@DDef{..} =
  -- All checked and synthesized vars must be of kind *
  if allStars cVars && allStars sVars
  -- Now check all the constructors for this datatype
  then case mapM (kindConstr d newEnv newTenv) cases of
         Left a  -> Left $ "Failed to kindCheck data constructor: " ++ show a
         Right _ -> Right newEnv
  else Left "Failed to infer proper kinds for C and S args for data constructor"
 where
   allStars :: [(TyVar, Kind)] -> Bool
   allStars x = foldl (&&) True $ map ((== Star) . snd) x
   newEnv :: DEnv
   newEnv = Map.union (toDEnv [d]) env
   newTenv :: TKEnv
   newTenv = Map.union (Map.fromList (kVars ++ cVars ++ sVars)) tenv

getVars :: [MonoTy] -> Either TypeError TKEnv
getVars (mt : mtys) = case mt of
                        VarTy tyVar     -> Map.insert tyVar Star <$> getVars mtys
                        ArrowTy mt1 mt2 -> getVars $ mt1:mt2:mtys
                        ConTy _ monoTys -> getVars $ monoTys ++ mtys
                        TupleTy monoTys -> getVars $ monoTys ++ mtys
                        TypeDictTy _    -> getVars mtys
getVars [] = return Map.empty

kindConstr :: DDef -> DEnv -> TKEnv -> KCons -> Either TypeError ()
kindConstr ddef@DDef{..} env tenv KCons{..} = do
  -- All constructors have an implicit forall in front of them binding any free variables
  newTenv <- Map.union tenv <$> getVars (fields ++ outputs)
  -- Get the kind for each of the taus that lead up to this guy and make sure they all check out
  _flds <- mapM (kindType env (newTenv `Map.union` Map.fromList (kVars ++ cVars ++ sVars)) . MonTy) fields
      -- Get the kinds for all the output types and make sure that the kinds check out there too
  outpts <- mapM (kindType env (newTenv `Map.union` Map.fromList (kVars ++ cVars ++ sVars)) . MonTy) outputs
  let tKinds = getTyArgs [ddef] tyName
  when (tKinds /= outpts) $
    Left $ "Invalid Type constructor application, expected " ++ show tKinds ++ 
           " but receieved " ++ show outpts ++ "in data constructor " ++ show conName

-- kindType Map.empty Map.empty kindTyScheme1
-- kindType Map.empty Map.empty kindTyScheme2
-- kindType Map.empty Map.empty kindTyScheme3
kindType :: DEnv -> TKEnv -> TyScheme -> Either TypeError Kind
kindType env tenv tscheme =
  case tscheme of
    ForAll tks mty       ->
      -- Add the variables bound by the forall into our type->kind env
      -- and recur with that info
      case kindType env (Map.fromList tks `Map.union` tenv) (MonTy mty) of
        Left err -> Left err
        Right k -> Right $ foldr (ArrowKind . snd) k tks
    MonTy (VarTy tyVar) ->
        -- Lookup this guy in our type->kind environment and see what we
        -- get. We should always find him, otherwise we have an unbound
        -- type variable
      case Map.lookup tyVar tenv of
        Nothing -> Left $ "Unbound type variable found! " ++ show tyVar
        Just k  -> Right k
    MonTy (ArrowTy monoTy1 monoTy2) -> do
      Star <- kindType env tenv (MonTy monoTy1)
      Star <- kindType env tenv (MonTy monoTy2)
      return Star -- ArrowKind mtk1 mtk2
    MonTy (TypeDictTy tname)        -> do
      -- According to our typing rules, this guy had better have kind * so
      -- enforce that here
      kindt <- kindType env tenv (MonTy (VarTy tname))
      if kindt /= Star
      then Left $ "TypeDict constructor requires types of kind *, but we received a type of kind "
                  ++ show kindt
      else Right Star
    MonTy (ConTy tname monotys) -> do
      kinds <- mapM (kindType env tenv . MonTy) monotys
      case Map.lookup tname env of
        Nothing   -> Left $ "Unbound type constructor found! " ++ show tname
        Just ddef -> let tnameKinds = getTyArgs [ddef] tname
                     in if kinds == tnameKinds
                        then return Star -- Only allow fully applied type constructors for now
                        else Left $ "Invalide type constructor application: " ++ show kinds
    t -> error $ "FOund " ++ show t

-- | Convenience: verify that the data defs that come with a program kind-check.
kindProg :: Prog -> Either TypeError ()
kindProg (Prog ddefs _ _) = kindClosedDefs ddefs

 -- Typecheck/infer
 -- Once we get the types go and run kindType on it
