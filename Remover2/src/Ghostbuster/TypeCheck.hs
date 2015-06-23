{-# LANGUAGE TupleSections #-}
module Ghostbuster.TypeCheck where

import Control.Applicative
import Control.Monad (when, (=<<))
import Control.Monad.ST
import Data.Atomics.Counter
import Data.STRef
import Data.Foldable as F
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Ghostbuster.Types as Ghost
import System.IO.Unsafe (unsafePerformIO, unsafeDupablePerformIO)

--- Replicating the data types for now since it's a pain trying to add in
--  the stref stuff to the types. This should all go away soon once I switch
--  over to using DDefs for the primitive types.

type Var = String
type KName = Var
type TName = Var
type TermVar = Var

data Exp = ELit Int
         | EPair Exp Exp
         | EVar !Var
         | ELam (Var,MonoTy) Exp
         | EApp Exp Exp
         | ELet (Var,TyScheme,Exp) Exp
----------------------------------------------
-- This stuff should be easier to implement once we use DDefs.
         | EK KName
         | ECase Exp [(Pat,Exp)]
         | EDict TName
         | ECaseDict Exp (TName,[TermVar],Exp) Exp
         | EIfTyEq (Exp,Exp) Exp Exp
  deriving (Eq, Show)

--  FIXME: We need to unify this representation with the one in Types.hs
--  TODO: I think we should add an extra field representing the kind of the
--        variable
data MonoTy = VarTy Var (STRef RealWorld (Maybe MonoTy))
            | TInt
            | TEPair MonoTy MonoTy
            | ArrowTy MonoTy MonoTy
            | ConTy KName [MonoTy]
            | TypeDictTy TName
          deriving (Eq)

data Kind = Star | ArrowKind Kind Kind
  deriving (Eq,Show,Ord)

data TyScheme = TMonoTy MonoTy
              | ForAll (S.Set (Var, Kind)) MonoTy
            deriving (Eq, Show)

type Env       = M.Map Var TyScheme
type MonoTyEnv = M.Map Var MonoTy

data Pat = Pat KName [TermVar]
  deriving (Eq,Show)

data DDef = DDef { tyName :: Var
                 , kVars :: [(Var,Kind)]
                 , cVars :: [(Var,Kind)]
                 , sVars :: [(Var,Kind)]
                 , cases :: [KCons]
                 }
  deriving (Eq,Show)

-- | Data constructor signatures.
data KCons = KCons { conName :: Var
                   , fields  :: [MonoTy] -- ^ The \tau_1 through \tau_p arguments
                   , outputs :: [MonoTy] -- ^ The type params fed to 'T' in the RHS
                   }
  deriving (Eq,Show)

instance Show MonoTy where
  show (VarTy v _)        = "(VarTy "   ++ show v    ++ ")"
  show (ArrowTy a b)      = "(ArrowTy " ++ show a    ++ " "  ++ show b     ++ ")"
  show (TEPair a b)       = "(TEPair "  ++ show a    ++ ", " ++ show b     ++ ")"
  show (ConTy name monos) = "(ConTy "   ++ show name ++ " "  ++ show monos ++ ")"

freeVarTys :: TyScheme -> ST RealWorld (S.Set Var)
freeVarTys (ForAll tvns t)               = S.difference <$> (freeVarTys $ TMonoTy t) <*> (return (S.map fst tvns))
freeVarTys (TMonoTy TInt)                = return $ S.empty
freeVarTys (TMonoTy (ArrowTy t1 t2))     = S.union <$> freeVarTys (TMonoTy t1) <*> freeVarTys (TMonoTy t2)
freeVarTys (TMonoTy (ConTy name (m:ms))) = S.union <$> freeVarTys (TMonoTy (ConTy name ms)) <*> freeVarTys (TMonoTy m)
freeVarTys (TMonoTy (ConTy name []))     = return $ S.empty -- TODO: make this cleaner
freeVarTys (TMonoTy (TypeDictTy name))   = return $ S.empty
freeVarTys (TMonoTy (TEPair t1 t2))      = S.union <$> freeVarTys (TMonoTy t1) <*> freeVarTys (TMonoTy t2)
freeVarTys (TMonoTy tv@(VarTy v ref))    = do
  val <- readSTRef ref
  case val of
   Nothing -> return $ S.singleton v
   Just _ -> TMonoTy <$> collapse tv >>= freeVarTys

freeVarsEnv :: Env -> ST RealWorld (S.Set Var)
freeVarsEnv env = F.foldlM go S.empty env
  where go acc x = do
          tvs <- freeVarTys x
          return $ S.union acc tvs

occurs :: Var -> MonoTy -> Bool
occurs v t = case t of
  VarTy u _ -> u == v
  ArrowTy t1 t2 -> occurs v t1 || occurs v t2
  TEPair t1 t2 -> occurs v t1 || occurs v t2
  ConTy name monos -> L.foldl (||) False $ map (occurs v) monos
  _ -> False

collapse :: MonoTy -> ST RealWorld MonoTy
collapse tv@(VarTy _v ref) = do
  t <- readSTRef ref
  case t of
   Nothing -> return tv
   Just t' -> do
     p <- collapse t'
     writeSTRef ref $ Just p
     return p
collapse (ArrowTy t1 t2)     = ArrowTy <$> collapse t1 <*> collapse t2
collapse (TEPair t1 t2)      = TEPair <$> collapse t1 <*> collapse t2
collapse TInt                = return TInt
collapse (ConTy name monos)  = ConTy name <$> mapM collapse monos
collapse v@(TypeDictTy name) = return v

unify :: MonoTy -> MonoTy -> ST RealWorld ()
unify t01 t02 = do
  case (t01, t02) of
   (VarTy v ref, t) ->
     if occurs v t02
       then error "can't construct infinite type"
       else do
         contents <- readSTRef ref
         case contents of
           Nothing -> writeSTRef ref (Just t)
           Just t' -> unify t t'
   (t, tv@(VarTy _ _)) -> unify tv t
   (ArrowTy t1 t2, ArrowTy t1' t2') -> do unify t1 t1'; unify t2 t2'
   (TEPair t1 t2, TEPair t1' t2') -> do unify t1 t1'; unify t2 t2'
   (TInt, TInt) -> return ()
   (ConTy n1 mono1, ConTy n2 mono2) -> 
     if n1 /= n2
     then error "Can't unify different type constructors"
     else  do
       monos <- mapM (\(m1,m2) -> unify m1 m2) $ zip mono1 mono2
       return () -- Pretty sure this is correct but double check it
   (TypeDictTy n1, TypeDictTy n2) ->
     if n1 == n2
     then return ()
     else error "Unable to unify TypeDict applied to two different constructors"
   _ -> error $ "can't unify"

substMonoTy :: MonoTy -> MonoTyEnv -> MonoTy
substMonoTy x env = case x of
  tv@(VarTy v _) -> case M.lookup v env of
                    Nothing -> tv
                    Just t -> t
  ArrowTy t1 t2 -> ArrowTy (substMonoTy t1 env) (substMonoTy t2 env)
  TEPair t1 t2 -> TEPair (substMonoTy t1 env) (substMonoTy t2 env)
  ConTy name mons -> ConTy name $ map ((flip substMonoTy) env) mons
  t -> t

-- Punt for now. FIXME
inferKinds :: S.Set Var -> S.Set (Var, Kind)
inferKinds t = S.map (,Star) t

generalize :: MonoTy -> Env -> ST RealWorld TyScheme
generalize t env = do
  tFree <- freeVarTys $ TMonoTy t
  eFree <- freeVarsEnv env
  return $ ForAll (inferKinds (S.difference tFree eFree)) t

instantiate :: TyScheme -> ST RealWorld MonoTy
instantiate (TMonoTy t) = return t
instantiate (ForAll tvns t) = do
  env' <- F.foldlM (\acc x -> freshVarTy () >>= \v -> return $ M.insert x v acc) M.empty $ S.map fst tvns
  let t' = substMonoTy t env'
  case t of
   VarTy _v ref -> writeSTRef ref (Just t') >> return t'
   _ -> return t'

inferExp :: Env -> Exp -> ST RealWorld MonoTy
inferExp env expr = case expr of
  ELit _ -> return TInt
  EVar v -> case M.lookup v env of
    Nothing -> error $ "unbound variable " ++ show v
    Just t -> instantiate t >>= collapse
  EPair e1 e2 -> do
    t1 <- inferExp env e1
    t2 <- inferExp env e2
    return $ TEPair t1 t2
  ELam (v, mty) body -> do
    fresh@(VarTy _ _) <- freshVarTy ()
    t <- inferExp (M.insert v (TMonoTy fresh) env) body
    return $ ArrowTy fresh t
  EApp e1 e2 -> do
    fun <- inferExp env e1
    arg <- inferExp env e2
    res <- freshVarTy ()
    unify fun $ ArrowTy arg res
    return res
  ELet (var, tyscheme, val) body -> do -- TODO: Check this and make sure it works that way it should
    t1 <- inferExp env val             -- Get the type for val
    mTyScheme <- instantiate tyscheme -- Instantiate our given type (so we now have a monotype)
    unify t1 mTyScheme                -- and check that against the type that we were given for the value
    t1' <- generalize t1 env
    t2 <- inferExp (M.insert var t1' env) body -- Should we insert t1' or tyscheme here?
    return t2
  t -> error $ "Inference for type: " ++ show t ++ " not implented yet!"

varCounter :: AtomicCounter
varCounter = unsafePerformIO $ newCounter 0

freshVarTy :: () -> ST RealWorld MonoTy
freshVarTy _ = do
  ref <- newSTRef Nothing
  return . unsafeDupablePerformIO $ do
    result <- incrCounter 1 varCounter
    return $! VarTy ("a" ++ show result) ref

------------------------------ Testing ------------------------------

mainInfer :: Exp -> IO MonoTy
mainInfer term = stToIO (inferExp M.empty term)

eId :: Exp
eId = ELam ("x", ConTy "Int" []) $ EVar "x"

appeId :: Exp
appeId = EApp eId eId

------------------------------ PREVIUUS VERSION ------------------------------ 

-- {-# LANGUAGE TupleSections #-}
--- 
-- -- Large portions of this are from this repo:
-- -- https://github.com/mgrabmueller/AlgorithmW.git
-- 
-- -- | FYI: Everywhere where we see 'map fst' we are losing kinding info
-- module Ghostbuster.TypeCheck
--       (typeExp, typeDef, typeProg) where
-- 
-- import           Ghostbuster.Types
-- import           Control.Monad.Error
-- import           Control.Monad.Reader
-- import           Control.Monad.State
-- import qualified Data.ByteString.Char8 as B
-- import qualified Data.Map              as Map
-- import qualified Data.Set              as Set
-- import qualified Text.PrettyPrint      as PP
-- 
-- -- | Type check a value definition given a set of in-scope data type
-- -- definitions.
-- typeDef :: [DDef] -> VDef -> Maybe TypeError
-- typeDef = undefined
-- 
-- typeExp :: [DDef] -> Exp -> Maybe TypeError
-- typeExp = undefined
-- 
-- typeProg :: Prog -> Maybe TypeError
-- typeProg = undefined
-- 
-- -------------------------------- TypeChecker for Ghostbuster -------------------
-- 
-- ------------------------------ Types and data defs ------------------------------
-- 
-- type Subst = Map.Map TyVar MonoTy
-- 
-- -- | Mapping from a TermVar to it's type Sigma
-- newtype TypeEnv = TypeEnv (Map.Map TermVar Sigma)
-- 
-- data TIEnv = TIEnv  {}
-- 
-- data TIState = TIState {  tiSupply :: Int
--                        ,  tiSubst  :: Subst}
-- 
-- type TI a = ErrorT String (ReaderT TIEnv (StateT TIState IO)) a
-- 
-- class Types a where
--   ftv   :: a -> Set.Set TyVar
--   {-ftv   :: a -> Set.Set B.ByteString-}
--   apply :: Subst -> a -> a
-- 
-- ------------------------------ Instantiations -----------------------------
-- 
-- instance Types MonoTy where
--   ftv (VarTy var)         = Set.singleton var
--   ftv (ArrowTy mt1 mt2)   = ftv mt1 `Set.union` ftv mt2
--   ftv (ConTy name mtList) = Set.unions $ map ftv mtList
--   ftv (TypeDictTy tyName)   = Set.empty
-- 
--   apply s v@(VarTy var)        = case Map.lookup var s of
--                                  Nothing -> v
--                                  Just newVar -> newVar
--   apply s (ArrowTy mt1 mt2)    = ArrowTy (apply s mt1) (apply s mt2)
--   apply s (ConTy name mtList)  = ConTy name (map (apply s) mtList)
--   apply s td@(TypeDictTy tyName) = td -- Should we do something else here?
-- 
-- instance Types Sigma where
--   ftv (ForAll vars t) = (ftv t) `Set.difference` (Set.fromList (map fst vars))
--   apply s (ForAll vars t) = ForAll vars (apply (foldr Map.delete s (map fst vars)) t)
-- 
-- instance Types a => Types [a] where
--   ftv l = foldr Set.union Set.empty (map ftv l)
--   apply s = map (apply s)
-- 
-- instance Types TypeEnv where
--   ftv (TypeEnv env) = ftv (Map.elems env)
--   apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)
-- 
-- 
-- ------------------------------ Utility Functions ------------------------------
-- 
-- nullSubst :: Subst
-- nullSubst = Map.empty
-- 
-- composeSubst :: Subst -> Subst -> Subst
-- composeSubst s1 s2 = (Map.map (apply s1) s2) `Map.union` s1
-- 
-- remove :: TypeEnv -> TermVar -> TypeEnv
-- remove (TypeEnv env) var = TypeEnv $ Map.delete var env
-- 
-- -- FIXME: We need to fix kinding here
-- generalize :: TypeEnv -> MonoTy -> Sigma
-- generalize env t = ForAll vars t
--   where vars = map (,Star) $ Set.toList $ (ftv t) `Set.difference` (ftv env)
-- 
-- runTI :: TI a -> IO (Either String a, TIState)
-- runTI t =
--     do (res, st) <- runStateT (runReaderT (runErrorT t) initTIEnv) initTIState
--        return (res, st)
--   where initTIEnv = TIEnv{}
--         initTIState = TIState{tiSupply = 0,
--                               tiSubst = Map.empty}
-- 
-- newTyVar :: String -> TI MonoTy
-- newTyVar prefix =
--     do  s <- get
--         put s{tiSupply = tiSupply s + 1}
--         return (VarTy $ Var $  B.pack (prefix ++ show (tiSupply s)))
-- 
-- ----------------- The Actual Type Inference/Checking ------------------
-- 
-- instantiate :: Sigma -> TI MonoTy
-- instantiate (ForAll vars t) =
--   do  nvars <- mapM (\ _ -> newTyVar "a") vars
--       let s = Map.fromList (zip (map fst vars) nvars)
--       return $ apply s t
-- 
-- unify :: MonoTy -> MonoTy -> TI Subst
-- unify (ArrowTy l r)  (ArrowTy l' r') =
--   do s1 <- unify l l'
--      s2 <- unify (apply s1 r) (apply s1 r')
--      return $ s1 `composeSubst` s2
-- unify (VarTy u) t = varBind u t
-- unify t (VarTy u) = varBind u t
-- 
-- unify (TypeDictTy t1) (TypeDictTy t2) = return $ nullSubst -- unify t1 t2          -- FIXME
-- unify (ConTy name mtypes) t = undefined                -- Punt on this for now
-- unify t (ConTy name mtypes) = undefined                -- Punt on this for now
-- unify t1 t2 = throwError $ "Types are unable to be unified: " ++ show t1 ++ " and " ++ show t2
-- 
-- varBind :: TyVar -> MonoTy -> TI Subst
-- varBind u t  | t == VarTy u           =  return nullSubst
--              | u `Set.member` ftv t  =  throwError $ "occurs check failed, with " ++ show u ++
--                                          " and " ++ show t
--              | otherwise             =  return (Map.singleton u t)
-- 
-- inferExp :: TypeEnv -> Exp -> TI (Subst, MonoTy)
-- inferExp (TypeEnv env) (EVar var) =
--   case Map.lookup var env of
--     Nothing -> throwError $ "Unbound variable " ++ show var
--     Just scheme  -> do t <- instantiate scheme
--                        return (nullSubst, t)
-- inferExp env (ELam (var, typ) e) =
--   do tv <- newTyVar "a"
--      let TypeEnv env' = remove env var
--          env'' = TypeEnv (env' `Map.union` (Map.singleton var (ForAll [] tv)))
--      (s1, t1) <- inferExp env'' e
--      return (s1, ArrowTy (apply s1 tv) t1)
-- inferExp env (EApp e1 e2) =
--   do  tv <- newTyVar "a"
--       (s1, t1) <- inferExp env e1
--       (s2, t2) <- inferExp (apply s1 env) e2
--       s3 <- unify (apply s2 t1) (ArrowTy t2 tv)
--       return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
-- inferExp env (ELet (x, s, e1) e2) = -- FIXME
--     do  (s1, t1) <- inferExp env e1
--         let TypeEnv env' = remove env x
--             t' = generalize (apply s1 env) t1
--             env'' = TypeEnv (Map.insert x t' env')
--         (s2, t2) <- inferExp (apply s1 env'') e2
--         return (s1 `composeSubst` s2, t2)
-- inferExp _ _ = undefined
-- -- TODO:
-- --   CASE, DICT, CASEDICT, IFTYEQ
-- 
-- typeInference :: Map.Map TermVar Sigma -> Exp -> TI MonoTy
-- typeInference env e =
--     do  (s, t) <- inferExp (TypeEnv env) e
--         return (apply s t)
-- 
-- e0  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
--                                        (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
--                                        (ELam (Var (B.pack "x"), VarTy (Var (B.pack "b"))) (EVar (Var (B.pack "x")))))
--         (EVar (Var (B.pack "id")))
-- 
-- e1  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
--                                        (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
--                                        (ELam (Var (B.pack "x"), VarTy (Var (B.pack "a"))) (EVar (Var (B.pack "x")))))
--         (EApp (EVar (Var (B.pack "id"))) (EVar (Var (B.pack "id"))))
-- 
-- e2  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
--                                        (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
--                                        EVar (Var (B.pack "x")))
--         (EApp (EVar (Var (B.pack "id"))) (EVar (Var (B.pack "id"))))
-- 
-- e3  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
--                                        (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
--                                        (ELam (Var (B.pack "x"), VarTy (Var (B.pack "a"))) (EApp (EVar (Var (B.pack "x"))) (EVar (Var (B.pack "x"))))))
--         (EVar (Var (B.pack "id")))
-- e4  =  ELet (Var (B.pack "id"), ForAll [((Var (B.pack "a")),Star)]
--                                        (ArrowTy (VarTy (Var (B.pack "a"))) (VarTy (Var (B.pack "a")))),
--                                        (ELam (Var (B.pack "x"), VarTy (Var (B.pack "a"))) (EVar (Var (B.pack "x")))))
--         (EVar (Var (B.pack "id")))
-- 
-- test :: Exp -> IO ()
-- test e =
--     do  (res, _) <- runTI (typeInference Map.empty e)
--         case res of
--           Left err  ->  putStrLn $ "error: " ++ err
--           Right t   ->  putStrLn $ " :: " ++ show t
-- 
-- main :: IO ()
-- main = mapM_ test [e0,e1,e2,e3]
-- 
