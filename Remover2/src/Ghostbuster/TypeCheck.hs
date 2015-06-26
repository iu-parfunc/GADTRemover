{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
module Ghostbuster.TypeCheck where


import Control.Applicative

import Control.Monad.ST
import Data.Atomics.Counter
import Data.STRef
import Data.Foldable as F
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
-- import           Ghostbuster.Types (VDef (..), Exp (..), TypeError)
import System.IO.Unsafe (unsafePerformIO, unsafeDupablePerformIO)

import Prelude hiding (foldr)

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
         | EK KName
         | EDict TName
----------------------------------------------
-- This stuff should be easier to implement once we use DDefs.
         | ECase Exp [(Pat,Exp)]
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
freeVarTys (TMonoTy (ConTy _name []))    = return $ S.empty -- TODO: make this cleaner
freeVarTys (TMonoTy (TypeDictTy _name))  = return $ S.empty
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
  ConTy _name monos -> L.foldl (||) False $ map (occurs v) monos
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
collapse v@(TypeDictTy _)    = return v

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
     then error $ "Can't unify different type constructors. Tried unifying: " ++ show n1 ++ " and " ++ show n2
     else  do
       _monos <- mapM (\(m1,m2) -> unify m1 m2) $ zip mono1 mono2
       return () -- Pretty sure this is correct but double check it
   (TypeDictTy n1, TypeDictTy n2) ->
     if n1 == n2
     then return ()
     else error "Unable to unify TypeDict applied to two different constructors"
   (t1 , t2) -> error $ "Can't unify " ++ show t1 ++ " whith " ++ show t2

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

inferExp :: [DDef] -> Env -> Exp -> ST RealWorld MonoTy
inferExp ddef env expr = case expr of
  ELit _ -> return TInt
  EVar v -> case M.lookup v env of
    Nothing -> error $ "unbound variable " ++ show v
    Just t -> instantiate t >>= collapse
  EPair e1 e2 -> do
    t1 <- inferExp ddef env e1
    t2 <- inferExp ddef env e2
    return $ TEPair t1 t2
  ELam (v, mty) body -> do
    t <- inferExp ddef (M.insert v (TMonoTy mty) env) body
    return $ ArrowTy mty t
  EApp e1 e2 -> do
    fun <- inferExp ddef env e1
    arg <- inferExp ddef env e2
    res <- freshVarTy ()
    unify fun $ ArrowTy arg res
    return res
  ELet (var, tyscheme, val) body -> do
    -- Get the type for val
    t1 <- inferExp ddef env val
    -- We need to make this a monotype in order to try and unify it
    mTyScheme <- instantiate tyscheme
    -- Unify the two together to make sure that the annotation is correct
    unify t1 mTyScheme
    -- Now get the type of the body with (var :: tyscheme) in Gamma
    t <- inferExp ddef (M.insert var tyscheme env) body
    return t
  EK name -> case ddefLookup ddef name of
  -- We hit a raw constructor, so we lookup the constructor in our DDef
  -- env, and the type of it will be based upon what we already have from the DDef and KCons form
  -- e.g, EK Foo
  -- data Bar   = Foo     ==> Foo :: Bar
  -- data Car a = Foo Int ==> Foo :: Int -> Car a
  -- etc.
               Just (topDef, constr) ->
                 return $ foldr ArrowTy (ConTy (tyName topDef) (outputs constr)) (fields constr)
               Nothing -> error $ "Unbound data constructor found! " ++ show name
  EDict name                             -> undefined
  ECase expr [(pat,exps)]                -> undefined
  ECaseDict expr (tname,[tvar],exps) alt -> undefined
  -- Need to discuss what exactly this does before I proceed any further.
  EIfTyEq (e1,e2) t f                -> do --undefined
    _e1typ <- inferExp ddef env e1
    _e2typ <- inferExp ddef env e2
    ttyp  <- inferExp ddef env t
    ftyp  <- inferExp ddef env f
    unify ttyp ftyp
    {-unify e1typ e2typ -- FIXME: THIS IS WRONG, and do we even need to do this? -}
    return ttyp
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

mainInfer :: [DDef] -> Exp -> IO MonoTy
mainInfer ddefs term = stToIO (inferExp ddefs M.empty term)

eId :: Exp
eId = ELam ("x", ConTy "Int" []) $ EVar "x"

eBool :: Exp
eBool = ELam ("x", ConTy "Bool" []) $ EVar "x"

-- Our show instance is a bit messed up, but this does the correct thing
eBoolApp :: Exp
eBoolApp = EApp (ELam ("x", ConTy "Bool" []) $ EVar "x") (EK "False")

-- If you dont believe me, this one will work, but eBoolBadAppApp will not.
eBoolAppApp :: Exp
eBoolAppApp = EApp eBool (EApp (ELam ("x", ConTy "Bool" []) $ EVar "x") (EK "False"))

-- Should fail
appeId :: Exp
appeId = EApp eId eId

-- Should fail
eBoolAppBad :: Exp
eBoolAppBad = EApp (EK "False") (ELam ("x", ConTy "Bool" []) $ EVar "x")

eBoolBadAppApp :: Exp
eBoolBadAppApp = EApp eId (EApp (ELam ("x", ConTy "Bool" []) $ EVar "x") (EK "False"))

-------------

constrT1 :: DDef
constrT1 =  DDef "Pair" [("a",Star), ("b",Star)] [] [] [KCons "mkPair" [ConTy "Bool" []] [ConTy "Bool" []]]

rawConstrTyp :: Exp
rawConstrTyp = EK "mkPair"

constrTest1 :: IO MonoTy
constrTest1 = mainInfer [constrT1] rawConstrTyp

constrT2 :: DDef
constrT2 =  DDef "Bool" [] [] [] [KCons "True" [] [], KCons "False" [] []]

rawConstrTyp2 :: Exp
rawConstrTyp2 = EK "True"

rawConstrTyp3 :: Exp
rawConstrTyp3 = EK "False"

constrTest2 :: IO MonoTy
constrTest2 = mainInfer [constrT2] rawConstrTyp2

constrTest3 :: IO MonoTy
constrTest3 = mainInfer [constrT2] rawConstrTyp3

primitiveTypes :: [DDef]
primitiveTypes =
  [ DDef "->" [("a",Star), ("b",Star)] [] [] []]

------------------------------ PREVIUUS VERSION ------------------------------
