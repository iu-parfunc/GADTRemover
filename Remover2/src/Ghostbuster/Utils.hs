{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | General utility functions for working with the core lang.

module Ghostbuster.Utils where

import qualified Data.ByteString.Char8 as B
import           Data.Char (isAlpha)
import qualified Data.List as L
import qualified Data.Map as Map
import           Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import           Ghostbuster.Types


--------------------------------------------------------------------------------
-- Naming conventions

-- | What is the name of a dictionary for a given type `T_i`?
dictConsName :: TName -> Var
dictConsName (Var v) = Var (v `B.append` "Dict")

-- | What is the name of the (single) dictionary GADT produced by LowerDicts?
typeDict :: MonoTy -> MonoTy
typeDict x = ConTy "TypeDict" [x]

--------------------------------------------------------------------------------
-- Misc Helpers

-- | Add something to any error message that comes through.
addToErr :: String -> Either String x -> Either String x
addToErr s (Left err) = Left (s++err)
addToErr _ (Right x)  = Right x

-- | Look up the arguments for a given data constructor K
getConArgs :: [DDef] -> KName -> [MonoTy]
getConArgs [] k = error $ "getConArgs: cannot find definition for constructor "++show k
getConArgs (DDef {cases} : rst) k =
  case loop cases of
    Just x  -> x
    Nothing -> getConArgs rst k
  where
  loop [] = Nothing
  loop (KCons {conName,fields} : rest)
    | conName == k = Just fields
    | otherwise = loop rest

kLookup :: [DDef] -> KName -> Maybe (DDef, KCons)
kLookup []               _name = Nothing
kLookup (d@DDef{..} : ds) name =
  case kconsLookup cases name of
    Nothing -> kLookup ds name
    Just k  -> Just (d, k)
 where
  kconsLookup :: [KCons] -> KName -> Maybe KCons
  kconsLookup (dd@KCons{..} : ds') name'
    | conName == name' = Just dd
    | otherwise        = kconsLookup ds' name'
  kconsLookup [] _name = Nothing


-- | Look up the type arguments for a given type constructor T
getTyArgs :: [DDef] -> TName -> [Kind]
getTyArgs [] t = error$ "getTyArgs: cannot find type def with name: "++show t
getTyArgs (DDef {tyName,kVars,cVars,sVars} : rst) k
  | k == tyName  = L.map snd $ kVars ++ cVars ++ sVars
  | otherwise = getTyArgs rst k


-- | Given the global datatype defs and a specific data constructor, this
-- returns the sorted list of `TypeDict` fields that should be added
-- to the front of the KCons.  It only adds dicts for relevant vars
-- that are EXISTENTIAL.  It adds the dicts in a canonical order, and
-- in fact this function defines our standard for that order.
getKConsDicts :: [DDef] -> KName -> [TyVar]
getKConsDicts ddefs conName =
  (S.toAscList changed)
  where
  changed = S.difference newExistential origExistential

  origExistential = S.difference (ftv fields) (ftv outputs)
  newExistential =
    S.difference (S.unions$ L.map (nonErased getter) fields)
                 ((nonErased getter) (ConTy (tyName def) outputs))
  getter = getArgStatus ddefs
  Just (def,KCons{fields,outputs}) = kLookup ddefs conName

-- | Include nothing under checked or synth contexts.
nonErased :: (TName -> [TyStatus]) -> MonoTy -> S.Set TyVar
nonErased getStatus mt =
  case mt of
    (VarTy x) -> S.singleton x
    (ArrowTy x1 x2) -> S.union (lp x1) (lp x2)
    (ConTy ty args) ->
      let (k,_,_) = splitTyArgs (getStatus ty) args
      in S.unions (L.map lp k)
    (TypeDictTy _tau) -> S.empty
 where
 lp = nonErased getStatus

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

-- | Look up a DDef in a list.  TODO!  Switch over to Maps for all the helpers here and elsewhere.
lookupDDef :: [DDef] -> TName -> DDef
lookupDDef [] tn = error $ "lookupDDef: couldn't find: "++show tn
lookupDDef (dd:rst) tn
           | tyName dd == tn = dd
           | otherwise = lookupDDef rst tn

-- | Gather all the T_i mentioned in this type.
--   This ONLY counts `ConTy`, it does not count mentions in typeDicts.
gatherTypesMentioned :: MonoTy -> S.Set TName
gatherTypesMentioned ty =
  case ty of
    (VarTy _)       -> S.empty
    (ArrowTy t1 t2) -> S.union (go t1) (go t2)
    (ConTy t ts)    -> S.insert t $ S.unions (L.map go ts)
    (TypeDictTy _)  -> S.empty -- S.singleton t
  where
   go = gatherTypesMentioned

freeVars :: Exp -> S.Set Var
freeVars = error "FINISHME"



-- | Sometimes it's convenient to convert back to expression:
val2Exp :: Val -> Exp
val2Exp (VK k []) = EK k
val2Exp (VK k ls) = EApp (val2Exp (VK k (init ls)))
                         (val2Exp (last ls))
val2Exp (VDict t []) = EDict t
val2Exp (VDict t ls) = EApp (val2Exp (VDict t (init ls)))
                            (val2Exp (last ls))
val2Exp (VClo vt env bod) = loop (M.toList env)
  -- FIXME: we could just bind the variables that are actually free in the bod:
 where
   loop [] = (ELam vt bod)
   -- Need type recovery or typed environments at runttime to finish this:
   loop ((x,val):tl) = ELet (x,error "FINISHME-val2Exp",val2Exp val)
                            (loop tl)


--------------------------------------------------------------------------------

-- | The status of a given type argument.
data TyStatus = Keep | Check | Synth
  deriving (Show,Read,Eq,Ord,Generic)

-- | Get the "status signature" for a type constructor.
--   It must be in the provided list of defs OR
--   the type constructor can be defined in `primitiveTypes`.
getArgStatus :: [DDef] -> TName -> [TyStatus]
getArgStatus [] t
  | L.any (== t) (L.map tyName primitiveTypes)
  = getArgStatus primitiveTypes t
  --
  | otherwise
  = error $ "getArgStatus: could not find type constructor "++show t

getArgStatus (DDef{tyName,kVars,cVars,sVars} : rest) t
  | t == tyName
  = replicate (length kVars) Keep  ++
    replicate (length cVars) Check ++
    replicate (length sVars) Synth
  --
  | otherwise
  = getArgStatus rest t


numberOfKeepAndCheck :: [DDef] -> TName -> Int
numberOfKeepAndCheck alldefs
  = length
  . L.filter p
  . getArgStatus alldefs
  where
    p Keep  = True
    p Check = True
    p Synth = False

-- | How many keep type args are their to the given type constructor.
numberOfKeep :: [DDef] -> TName -> Int
numberOfKeep alldefs tn = length [ () | Keep <- getArgStatus alldefs tn ]

-- | A HOAS combinator to introduce a let-binding IFF the provided
-- syntax is anything more complex than an identifier.
--
-- TODO: this needs to be in a monad that can generate names.
letBindNonTriv :: Exp -> (Exp -> Exp) -> Exp
letBindNonTriv e f =
  case e of
    (EK _)       -> f e
    (EVar _)     -> f e
    (EDict _)    -> f e
    -----------------------------------------
    -- TODO: the remaining cases really need let bindings;
    _ -> f e  -- TEMP/FIXME
    _ -> ELet (tmp, recoverType e, e) (f (EVar tmp))
  where
  tmp = freshenVar "tmp"
  -- If we hoist things out with ELet, then we need to have their type.
  -- This should go in the type checking module.
  recoverType = error "FINISHME: implement recoverType"

-- | Create an immediately-applied lambda.  Very similar to a let-binding.
leftleftLambda :: Exp -> MonoTy -> (Exp -> Exp) -> Exp
leftleftLambda arg ty bod =
  EApp (ELam ("ltmp",ty) (bod "ltmp")) arg

-- | Return a fresh (unique) version of the input variable.
--
--   FIXME: this must be moved into a monad and all use sites refactored.
freshenVar :: Var -> Var
freshenVar v = v

(+++) :: Var -> Var -> Var
(+++) (Var x) (Var y) = Var (x `B.append` y)

-- | Potentially infinite list of temporary pattern vars:
-- TODO: replace with freshenVar of a single root name.
patVars :: [Var]
patVars = L.map (\c -> mkVar [c]) $
          L.filter isAlpha ['a'..]

--------------------------------------------------------------------------------
-- Generic smart syntax constructors:

appLst :: Exp -> [Exp] -> Exp
appLst f [] = f
appLst f ls = EApp (appLst f (init ls)) (last ls)

mkLams :: [(TermVar,MonoTy)] -> Exp -> Exp
mkLams [] bod = bod
mkLams (arg:rst) bod = ELam arg (mkLams rst bod)

mkFunTy :: [MonoTy] -> MonoTy -> MonoTy
mkFunTy [] res = res
mkFunTy (h:t) res = h `ArrowTy` mkFunTy t res

--------------------------------------------------------------------------------

class Types a where
  ftv   :: a -> Set.Set TyVar
  {-ftv   :: a -> Set.Set B.ByteString-}
  apply :: Subst -> a -> a

type Subst = Map.Map TyVar MonoTy

------------------------------ Instantiations -----------------------------

instance Types MonoTy where
  ftv (VarTy var)         = Set.singleton var
  ftv (ArrowTy mt1 mt2)   = ftv mt1 `Set.union` ftv mt2
  ftv (ConTy _name mtList) = Set.unions $ L.map ftv mtList
  ftv (TypeDictTy _tyName) = Set.empty

  apply s v@(VarTy var)        = case Map.lookup var s of
                                 Nothing -> v
                                 Just newVar -> newVar
  apply s (ArrowTy mt1 mt2)    = ArrowTy (apply s mt1) (apply s mt2)
  apply s (ConTy name mtList)  = ConTy name (L.map (apply s) mtList)
  apply _ td@(TypeDictTy _tyName) = td -- Should we do something else here?

instance Types TyScheme where
  ftv (ForAll vars t) = (ftv t) `Set.difference` (Set.fromList (L.map fst vars))
  apply s (ForAll vars t) = ForAll vars (apply (L.foldr Map.delete s (L.map fst vars)) t)

instance Types a => Types [a] where
  ftv l = L.foldr Set.union Set.empty (L.map ftv l)
  apply s = L.map (apply s)
