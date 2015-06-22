{-# LANGUAGE NamedFieldPuns #-}

-- | An interpreter for the Ghostbuster core language.

module Ghostbuster.Interp
       (interp) where

import Data.Map.Lazy as M
import Ghostbuster.Types
import Prelude as P hiding (exp)

type Env = Map Var Val

-- | This interprets the program with a call-by-need semantics.
interp :: Prog -> Val
interp (Prog ddefs vdefs main) =
  exp ddefs topenv main
  where
  -- Here we implement call-by-need in the target language using the
  -- host language (Haskell's) own lazy evaluation:
  topenv = M.fromList
             (P.map (\VDef{valName,valExp} ->
                       ( valName,
                         exp ddefs topenv valExp )
                    ) vdefs)

-- | Interpret an expression
exp :: [DDef] -> Env -> Exp -> Val
exp defs env exp0 =
  case exp0 of
    (EK x)   -> VK x [] -- FIXME: if we know the type of this
                        -- constructor, we need to make this a VLam!
    (EVar x) -> env # x
    (ELam (v,ty) bod) -> VLam (v,ty) bod
    (EApp x1 x2) -> let VLam (v,_) bod = exp defs env x1
                        arg = exp defs env x2
                        env' = M.insert v arg env
                    in exp defs env' bod
    (ELet (v,_,x1) x2) -> let x1' = exp defs env x1
                              env' = M.insert v x1' env
                          in exp defs env' x2
    (ECase x1 []) -> let v = exp defs env x1
                     in error $ "expression did not match any cases: "++show v
    (ECase x1 ((Pat kname vars, rhs ) : rst)) ->
      case exp defs env x1 of
        v@(VK k2 args) | k2 == kname ->
                         if length vars == length args
                          then exp defs (M.union (M.fromList (zip vars args))
                                                 env) rhs
                          else tyErr $ "bad number of constructor args." ++
                               "\nExpected: " ++show vars ++
                               "\nReceived: " ++show args
                       | otherwise  -> exp defs env (ECase (val2Exp v) rst)
        v@(VLam _ _) -> tyErr$ "cannot case on a lambda!: "++show v
        v@(VDict _) -> tyErr $ "cannot perform a regular ECase on a Dict value, use ECaseDict: "
                               ++ show v
    (EDict x) -> VDict x
    (ECaseDict x1 (tn,vs,rhs) x3) ->
      case exp defs env x1 of
        v@(VK{})   -> tyErr $ "ECaseDict got non-Dict value: "++show v
        v@(VLam{}) -> tyErr $ "ECaseDict got non-Dict value: "++show v
        (VDict t2) | tn == t2 ->
                     let env' = M.union
                                (M.fromList (zip vs newdicts))
                                env
                         newdicts = error "FINISHME: need the types at runtime to construct dicts..."
                     in exp defs env' rhs
                   | otherwise -> exp defs env x3
    (EIfTyEq (le,re) x2 x3) ->
      -- Here we would extend the type env on the x2 case when type checking.
      -- But the value env doesn't change at all.
      case (exp defs env le, exp defs env re) of
        (VDict k1, VDict k2) | k1 == k2  -> exp defs env x2
                             | otherwise -> exp defs env x3
        (bad1,bad2) -> tyErr $ "EIfTyEq must take two VDict values, got: "++show (bad1,bad2)


(#) :: (Ord k, Show k, Show v) => Map k v -> k -> v
m # k = case M.lookup k m of
          Nothing -> error$ "Map does not contain key: "++show k++"\nFull map:\n"++show m
          Just x  -> x


tyErr :: String -> t
tyErr s = error ("<Runtime Type Error>: "++s)
