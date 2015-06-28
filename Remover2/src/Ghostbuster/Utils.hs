{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
-- |

module Ghostbuster.Utils where

import qualified Data.List as L
import qualified Data.Map as Map
import           Data.Map.Lazy as M
import qualified Data.Set as Set
import qualified Data.Set as S
import           GHC.Generics (Generic)
import           Ghostbuster.Types

--------------------------------------------------------------------------------
-- Misc Helpers

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

getTyArgs :: [DDef] -> TName -> [Kind]
getTyArgs [] t = error$ "getTyArgs: cannot find type def with name: "++show t
getTyArgs (DDef {tyName,kVars,cVars,sVars} : rst) k
  | k == tyName  = L.map snd $ kVars ++ cVars ++ sVars
  | otherwise = getTyArgs rst k

freeVars :: Exp -> S.Set Var
freeVars = undefined




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
getArgStatus :: [DDef] -> TName -> [TyStatus]
getArgStatus [] t = error $ "getArgStatus: could not find type constructor "++show t
getArgStatus (DDef{tyName,kVars,cVars,sVars} : rest) t
  | t == tyName = replicate (length kVars) Keep ++
                  replicate (length cVars) Check ++
                  replicate (length sVars) Synth
  | otherwise = getArgStatus rest t

addToErr :: String -> Either String x -> Either String x
addToErr s (Left err) = Left (s++err)
addToErr _ (Right x)  = Right x

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
