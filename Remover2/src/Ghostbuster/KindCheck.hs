{-# LANGUAGE RecordWildCards #-}

module Ghostbuster.KindCheck
       ( kindProg
       , kindClosedDefs
       ) where

import           Control.Applicative
import           Ghostbuster.Types
-- import           Ghostbuster.Examples.Feldspar
-- import qualified Ghostbuster.TypeCheck as GTC
import           Ghostbuster.Utils (getTyArgs)
import qualified Data.Map as Map
import           Control.Monad

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
getVars (mt : mtys) =
  case mt of
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
  _flds <- mapM (kindMonoType env (newTenv `Map.union` Map.fromList (kVars ++ cVars ++ sVars))) fields
      -- Get the kinds for all the output types and make sure that the kinds check out there too
  outpts <- mapM (kindMonoType env (newTenv `Map.union` Map.fromList (kVars ++ cVars ++ sVars))) outputs
  let tKinds = getTyArgs [ddef] tyName
  when (tKinds /= outpts) $
    Left $ "Invalid Type constructor application, expected " ++ show tKinds ++
           " but receieved " ++ show outpts ++ "in data constructor " ++ show conName

-- kindType Map.empty Map.empty kindTyScheme1
-- kindType Map.empty Map.empty kindTyScheme2
-- kindType Map.empty Map.empty kindTyScheme3
kindTyScheme :: DEnv -> TKEnv -> TyScheme -> Either TypeError Kind
kindTyScheme env tenv (ForAll tks mty) =
  -- Add the variables bound by the forall into our type->kind env
  -- and then check the monotypes inside the forall
  case kindMonoType env (Map.fromList tks `Map.union` tenv) mty of
    Left err -> Left err
    Right k -> Right $ foldr (ArrowKind . snd) k tks

kindMonoType :: DEnv -> TKEnv -> MonoTy -> Either TypeError Kind
kindMonoType env tenv ty =
  case ty of
    (VarTy tyVar) ->
        -- Lookup this guy up in our type->kind environment and see what we
        -- get. We should always find him, otherwise we have an unbound
        -- type variable
      case Map.lookup tyVar tenv of
        Nothing -> Left $ "Unbound type variable found! " ++ show tyVar
        Just k  -> Right k
    (ArrowTy monoTy1 monoTy2) -> do
      Star <- kindMonoType env tenv monoTy1
      Star <- kindMonoType env tenv monoTy2
      return Star -- ArrowKind mtk1 mtk2
    (TypeDictTy tname)        -> do
      -- According to our typing rules, this guy had better have kind * so
      -- enforce that here
      kindt <- kindMonoType env tenv (VarTy tname)
      if kindt /= Star
      then Left $ "TypeDict constructor requires types of kind *, but we received a type of kind "
                  ++ show kindt
      else Right Star
    (ConTy tname monotys) -> do
      kinds <- mapM (kindMonoType env tenv) monotys
      case Map.lookup tname env of
        Nothing   -> Left $ "Unbound type constructor found! " ++ show tname
        Just ddef -> let tnameKinds = getTyArgs [ddef] tname
                     in if kinds == tnameKinds
                        then return Star -- Only allow fully applied type constructors for now
                        else Left $ "Invalid type constructor application: " ++ show kinds
                                    ++ " Expected " ++ show tnameKinds ++ " for type constructor "
                                    ++ show tname
                                  

-- | Convenience: verify that the data defs that come with a program kind-check.
kindProg :: Prog -> Either TypeError ()
kindProg (Prog ddefs _ _) = kindClosedDefs ddefs

 -- Typecheck/infer
 -- Once we get the types go and run kindType on it

