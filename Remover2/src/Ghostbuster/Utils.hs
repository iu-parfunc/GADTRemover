{-# LANGUAGE NamedFieldPuns #-}
-- |

module Ghostbuster.Utils where

import Data.Map.Lazy as M

import qualified Data.Set as S




import qualified Data.List as L
import Ghostbuster.Types

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
data TyArgStatus = Keep | Check | Synth

-- | Get the "status signature" for a type constructor.
getArgStatus :: [DDef] -> TName -> [TyArgStatus]
getArgStatus [] t = error $ "getArgStatus: could not find type constructor "++show t
getArgStatus (DDef{tyName,kVars,cVars,sVars} : rest) t
  | t == tyName = replicate (length kVars) Keep ++
                  replicate (length cVars) Check ++
                  replicate (length sVars) Synth
  | otherwise = getArgStatus rest t
