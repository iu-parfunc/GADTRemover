{-# LANGUAGE TupleSections #-}

-- Large portions of this are from this repo:
-- https://github.com/mgrabmueller/AlgorithmW.git

-- | FYI: Everywhere where we see 'map fst' we are losing kinding info
module Ghostbuster.TypeCheck1
      (typeExp, typeDef, typeProg,
       main) where

import           Ghostbuster.Types
import           Ghostbuster.Utils
import           Control.Monad.Error
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.ByteString.Char8 as B
import qualified Data.Map              as Map
import qualified Data.Set              as Set
-- import qualified Text.PrettyPrint      as PP


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

unify (TypeDictTy t1) (TypeDictTy t2) = return $ nullSubst -- unify t1 t2          -- FIXME
unify (ConTy name mtypes) t = undefined                -- Punt on this for now
unify t (ConTy name mtypes) = undefined                -- Punt on this for now
unify t1 t2 = throwError $ "Types are unable to be unified: " ++ show t1 ++ " and " ++ show t2

varBind :: TyVar -> MonoTy -> TI Subst
varBind u t  | t == VarTy u           =  return nullSubst
             | u `Set.member` ftv t  =  throwError $ "occurs check failed, with " ++ show u ++
                                         " and " ++ show t
             | otherwise             =  return (Map.singleton u t)


inferExp :: TypeEnv -> Exp -> TI (Subst, MonoTy)
inferExp (TypeEnv env) (EVar var) =
  case Map.lookup var env of
    Nothing -> throwError $ "Unbound variable " ++ show var
    Just scheme  -> do t <- instantiate scheme
                       return (nullSubst, t)
inferExp env (ELam (var, typ) e) =
  do tv <- newTyVar "a"
     let TypeEnv env' = remove env var
         env'' = TypeEnv (env' `Map.union` (Map.singleton var (ForAll [] tv)))
     (s1, t1) <- inferExp env'' e
     return (s1, ArrowTy (apply s1 tv) t1)
inferExp env (EApp e1 e2) =
  do  tv <- newTyVar "a"
      (s1, t1) <- inferExp env e1
      (s2, t2) <- inferExp (apply s1 env) e2
      s3 <- unify (apply s2 t1) (ArrowTy t2 tv)
      return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
inferExp env (ELet (x, s, e1) e2) = -- FIXME
    do  (s1, t1) <- inferExp env e1
        let TypeEnv env' = remove env x
            t' = generalize (apply s1 env) t1
            env'' = TypeEnv (Map.insert x t' env')
        (s2, t2) <- inferExp (apply s1 env'') e2
        return (s1 `composeSubst` s2, t2)
inferExp _ _ = undefined
-- TODO:
--   CASE, DICT, CASEDICT, IFTYEQ

typeInference :: Map.Map TermVar TyScheme -> Exp -> TI MonoTy
typeInference env e =
    do  (s, t) <- inferExp (TypeEnv env) e
        return (apply s t)

e0  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
                                       (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
                                       (ELam (Var (B.pack "x"), VarTy (Var (B.pack "b"))) (EVar (Var (B.pack "x")))))
        (EVar (Var (B.pack "id")))

e1  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
                                       (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
                                       (ELam (Var (B.pack "x"), VarTy (Var (B.pack "a"))) (EVar (Var (B.pack "x")))))
        (EApp (EVar (Var (B.pack "id"))) (EVar (Var (B.pack "id"))))

e2  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
                                       (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
                                       EVar (Var (B.pack "x")))
        (EApp (EVar (Var (B.pack "id"))) (EVar (Var (B.pack "id"))))

e3  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
                                       (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
                                       (ELam (Var (B.pack "x"), VarTy (Var (B.pack "a"))) (EApp (EVar (Var (B.pack "x"))) (EVar (Var (B.pack "x"))))))
        (EVar (Var (B.pack "id")))
e4  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
                                       (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
                                       (ELam (Var (B.pack "x"), VarTy (Var (B.pack "a"))) (EVar (Var (B.pack "x")))))
        (EVar (Var (B.pack "id")))

test :: Exp -> IO ()
test e =
    do  (res, _) <- runTI (typeInference Map.empty e)
        case res of
          Left err  ->  putStrLn $ "error: " ++ err
          Right t   ->  putStrLn $ " :: " ++ show t

main :: IO ()
main = mapM_ test [e0,e1,e2,e3]