{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- Large portions of this are from this repo:
-- https://github.com/mgrabmueller/AlgorithmW.git

-- | FYI: Everywhere where we see 'map fst' we are losing kinding info
module Ghostbuster.TypeCheck1
      ( typeExp, typeDef, typeProg

      -- * Temporary exports:
      , main, typeInference, test
      , terr2, terr3, terr4
      )
      where

import           Ghostbuster.Types
import           Ghostbuster.Utils
import           Control.Monad.Error
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.ByteString.Char8 as B
import qualified Data.Map              as Map
import qualified Data.Set              as Set
import qualified Ghostbuster.Examples.Tiny as T
-- import qualified Text.PrettyPrint      as PP

import Debug.Trace

-- | Type check a value definition given a set of in-scope data type
-- definitions.
typeDef :: [DDef] -> VDef -> Maybe TypeError
typeDef = undefined

typeExp :: [DDef] -> Exp -> Maybe TypeError
typeExp = undefined

typeProg :: Prog -> Maybe TypeError
typeProg = undefined

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv (Map.elems env)
  apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)

-------------------------------- TypeChecker for Ghostbuster -------------------

------------------------------ Types and data defs ------------------------------

-- | Mapping from a TermVar to it's type TyScheme
newtype TypeEnv = TypeEnv (Map.Map TermVar TyScheme)

data TIEnv = TIEnv

data TIState = TIState { tiSupply :: Int
                       ,  tiSubst  :: Subst}

type TI a = ErrorT String (ReaderT TIEnv (StateT TIState IO)) a

------------------------------ Utility Functions ------------------------------

nullSubst :: Subst
nullSubst = Map.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = (Map.map (apply s1) s2) `Map.union` s1

remove :: TypeEnv -> TermVar -> TypeEnv
remove (TypeEnv env) var = TypeEnv $ Map.delete var env

-- FIXME: We need to fix kinding here
generalize :: TypeEnv -> MonoTy -> TyScheme
generalize env t = ForAll vars t
  where vars = map (,Star) $ Set.toList $ (ftv t) `Set.difference` (ftv env)

runTI :: TI a -> IO (Either String a, TIState)
runTI t =
    do (res, st) <- runStateT (runReaderT (runErrorT t) initTIEnv) initTIState
       return (res, st)
  where initTIEnv = TIEnv{}
        initTIState = TIState{tiSupply = 0,
                              tiSubst = Map.empty}

newTyVar :: String -> TI MonoTy
newTyVar prefix =
    do  s <- get
        put s{tiSupply = tiSupply s + 1}
        return (VarTy $ Var $  B.pack (prefix ++ show (tiSupply s)))

----------------- The Actual Type Inference/Checking ------------------

instantiate :: TyScheme -> TI MonoTy
instantiate (ForAll vars t) =
  do  nvars <- mapM (\ _ -> newTyVar "a") vars
      let s = Map.fromList (zip (map fst vars) nvars)
      return $ apply s t

unify :: MonoTy -> MonoTy -> TI Subst
unify (ArrowTy l r)  (ArrowTy l' r') =
  do s1 <- unify l l'
     s2 <- unify (apply s1 r) (apply s1 r')
     return $ s1 `composeSubst` s2
unify (VarTy u) t = varBind u t
unify t (VarTy u) = varBind u t

unify (TypeDictTy t1) (TypeDictTy t2) = return $ nullSubst -- unify t1 t2 -- FIXME
unify (ConTy name mtypes) (ConTy name' mtypes') =
  -- They better have the same type constructor
  if name /= name'
  then throwError $ "Types are unable to be unified, incompatible type constructors " ++ show name ++ " and " ++ show name'
  else do
    -- If they have the same type constructor, each of the types had better be able to be unified with each other too
    substs <- zipWithM unify mtypes mtypes'
    return $ foldr composeSubst nullSubst substs
unify t1 t2 = throwError $ "Types are unable to be unified: " ++ show t1 ++ " and " ++ show t2

varBind :: TyVar -> MonoTy -> TI Subst
varBind u t  | t == VarTy u           =  return nullSubst
             | u `Set.member` ftv t  =  throwError $ "occurs check failed, with " ++ show u ++
                                         " and " ++ show t
             | otherwise             =  return (Map.singleton u t)

kconsLookup :: [KCons] -> KName -> Maybe KCons
kconsLookup (d@KCons{..} : ds) name = if conName == (name :: Var)
                                  then Just d
                                  else kconsLookup ds name
kconsLookup [] _name = Nothing

ddefLookup :: [DDef] -> KName -> Maybe (DDef, KCons)
ddefLookup (d@DDef{..} : ds) name =
  case kconsLookup cases name of
    Nothing -> ddefLookup ds name
    Just k  -> Just (d, k)
ddefLookup [] _name = Nothing

checkPat :: [DDef] -> TypeEnv -> MonoTy -> Pat -> TI Subst
checkPat denv tenv ty (Pat name tvars) = do
  -- Get the type of the constructor
  (subst, ConTy name' tvs') <- inferExp denv tenv (EK name)
  -- This guy had better be a constructor, which means we better get a nullSubst back out
  unless (Map.null subst) $
    throwError $ "Invalid pattern match! We MUST have a constructor to match on, but " ++
                 show name ++ " isn't a constructor"
  -- Get the substitutions that we need, and ensure that they can all unify with the type constructor
  -- If it all works out, return it.
  unify ty (ConTy name' tvs')

unifyAll :: [DDef] -> TypeEnv -> [(Subst, MonoTy)] -> TI (MonoTy, [Subst])
unifyAll denv env (t : ts)= do
  -- Make sure they all unify with the same type
  substs <- mapM ((unify (snd t)) . snd) ts
  -- Return that type, and all the substitutions that we came up with
  return (snd t, fst t : substs)
unifyAll denv env [] = throwError "Found case expression with no RHS"

inferExp :: [DDef] -> TypeEnv -> Exp -> TI (Subst, MonoTy)
inferExp denv (TypeEnv env) (EVar var) =
  case Map.lookup var env of
    Nothing -> throwError $ "Unbound variable " ++ show var
    Just scheme  -> do t <- instantiate scheme
                       return (nullSubst, t)
inferExp denv env (ELam (var, typ) e) =
  do tv <- newTyVar "a"
     let TypeEnv env' = remove env var
         env'' = TypeEnv (env' `Map.union` (Map.singleton var (ForAll [] typ)))
     (s1, t1) <- inferExp denv env'' e
     return (s1, ArrowTy (apply s1 typ) t1)
inferExp denv env (EApp e1 e2) =
  do  tv <- newTyVar "a"
      (s1, t1) <- inferExp denv env e1
      (s2, t2) <- inferExp denv (apply s1 env) e2
      s3 <- unify (apply s2 t1) (ArrowTy t2 tv)
      return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
inferExp denv env (ELet (x, s, e1) e2) = -- FIXME
    do  (s1, t1) <- inferExp denv env e1
        let TypeEnv env' = remove env x
            t' = generalize (apply s1 env) t1
            env'' = TypeEnv (Map.insert x t' env')
        (s2, t2) <- inferExp denv (apply s1 env'') e2
        return (s1 `composeSubst` s2, t2)
inferExp denv env (EK name) =
  case ddefLookup denv name of
    Nothing -> error $ "Unbound data constructor found! " ++ show name
    Just (topDef, constr) ->
      return (nullSubst,  foldr ArrowTy (ConTy (tyName topDef) (outputs constr)) (fields constr))
inferExp denv env (ECase e1 pats) = do
  -- Get the type of the thing we are matching on
  (s1, t1) <- inferExp denv env e1
  -- Make sure that in the updated environment that all the patters have type t1
  tas <- mapM (checkPat denv (apply s1 env) t1 . fst) pats
  -- Now get all the types of the rhs's of the patterns
  aas <- mapM (inferExp denv (apply s1 env) . snd) pats
  -- Make sure that they all unify with each other
  (typ, substs) <- unifyAll denv (apply s1 env) aas
  -- return the type of the alts, and we need to be optimisitic and apply
  -- all the substitutions to the environment (right??)
  return (foldr composeSubst s1 substs, typ)
inferExp denv env t = error $ "Type = " ++ show t

typeInference :: [DDef] -> Map.Map TermVar TyScheme -> Exp -> TI MonoTy
typeInference denv env e =
    do  (s, t) <- inferExp denv (TypeEnv env) e
        return (apply s t)


--------------------------------------------------------------------------------
-- Type-error tests:

terr2 :: Exp
terr2  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
                                          (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
                                          EVar (Var (B.pack "x")))
           (EApp (EVar (Var (B.pack "id"))) (EVar (Var (B.pack "id"))))

terr3 :: Exp
terr3  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
                                          (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
                                          (ELam (Var (B.pack "x"), VarTy (Var (B.pack "a"))) (EApp (EVar (Var (B.pack "x"))) (EVar (Var (B.pack "x"))))))
           (EVar (Var (B.pack "id")))

terr4 :: Exp
terr4  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
                                          (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
                                          (ELam (Var (B.pack "x"), VarTy (Var (B.pack "a"))) (EVar (Var (B.pack "x")))))
           (EVar (Var (B.pack "id")))

test :: [DDef] -> Exp -> IO ()
test denv e =
    do  (res, _) <- runTI (typeInference denv Map.empty e)
        case res of
          Left err  ->  putStrLn $ "error: " ++ err
          Right t   ->  putStrLn $ " :: " ++ show t

main :: IO ()
main = mapM_ (test primitiveTypes) [T.e11,T.e12,T.e13, terr2, terr3, terr4]
