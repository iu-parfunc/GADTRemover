{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | An interpreter for the Ghostbuster core language.

module Ghostbuster.Interp
       ( interp
       , ti1, ti2, ti3, ti4, ti5, ti6, ti7
       , p2, p3, p4, p5, p6, p7
       ) where

import Data.Map.Lazy as M
import Debug.Trace
import Ghostbuster.Types
import Prelude as P hiding (exp)
import Text.PrettyPrint.GenericPretty (Out(doc))
import Ghostbuster.Utils

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
  (\res ->
        trace ("((Eval: " ++ show (doc exp0)
                                    ++ " in env: "++ show (doc env)++ ")"
              ++ " -> "++ show (doc res)++ ")") res) $
  case exp0 of
    (EK x)   -> VK x []
      -- case (getConArgs defs x) of
      --   [] -> VK x []
      --   ls -> exp defs env (applyList (EK x) ls)
    (EVar x) -> env # x
    (ELam (v,ty) bod) -> VClo (v,ty) env bod
    (EApp x1 x2) ->
      let arg = exp defs env x2
      in case exp defs env x1 of
          VClo (v,_) env2 bod -> let env' = M.insert v arg env2
                                 in exp defs env' bod
          -- These values just accumulate arguments:
          VK k ls    -> VK k (ls++[arg])
          VDict t ls -> VDict t (ls++ [arg])

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
        v@(VClo{}) -> tyErr$ "cannot case on a lambda!: "++show v
        v@(VDict{}) -> tyErr $ "cannot perform a regular ECase on a Dict value, use ECaseDict: "
                               ++ show v
    (EDict x) -> VDict x []
      -- exp defs env $
      -- applyList (EDict x)
      --           [ TypeDictTy $ mkVar $ "tau" ++show i
      --           | (_,i) <- zip (getTyArgs defs x) [0::Int ..]]
    (ECaseDict x1 (tn,vs,rhs) x3) ->
      case exp defs env x1 of
        v@(VK{})   -> tyErr $ "ECaseDict got non-Dict value: "++show v
        v@(VClo{}) -> tyErr $ "ECaseDict got non-Dict value: "++show v
        (VDict t2 args)
         | tn == t2 ->
           (if length vs == length args
            then let env' = M.union
                            (M.fromList (zip vs args))
                            env
                 in exp defs env' rhs
            else tyErr $ "ECaseDict: mismatched length of pattern vars "++show vs
                         ++" and dict args: "++show args)
         | otherwise -> exp defs env x3
    (EIfTyEq (le,re) x2 x3) ->
      -- Here we would extend the type env on the x2 case when type checking.
      -- But the value env doesn't change at all.
      case (exp defs env le, exp defs env re) of
        (VDict k1 a1, VDict k2 a2)
           | k1 == k2 && a1 == a2  -> exp defs env x2
           | otherwise -> exp defs env x3
        (bad1,bad2) -> tyErr $ "EIfTyEq must take two VDict values, got: "++show (bad1,bad2)

applyList :: (Exp) -> [MonoTy] -> Exp
applyList f ls = loop [] ls
  where
  numArgs = length ls

  loop :: [Var] -> [MonoTy] -> Exp
  loop acc [] = loop2 (P.map EVar acc)
  loop acc (ty1:tys) =
    let var = mkVar $ "arg"++show (numArgs - length tys)
    in ELam (var, ty1) $
       loop (var:acc) tys

  loop2 [] = f
  loop2 (hd:tl) = EApp (loop2 tl) hd



(#) :: (Ord k, Show k, Show v) => Map k v -> k -> v
m # k = case M.lookup k m of
          Nothing -> error$ "Map does not contain key: "++show k++"\nFull map:\n"++show m
          Just x  -> x


tyErr :: String -> t
tyErr s = error ("<Runtime Type Error>: "++s)

--------------------------------------------------------------------------------
-- Tests and examples:

ti1 :: Exp
ti1 = applyList (EK "FOO") [VarTy "a", VarTy "b", VarTy "c"]

p2 :: Exp
p2 = (ECase (EK "One") [(Pat "One" [], EK "Two")])

ti2 :: Val
ti2 = interp $ Prog [ints] [] p2

p3 :: Exp
p3 = EDict ("Int")

ti3 :: Val
ti3 = interp $ Prog [ints] [] p3

p4 :: Exp
p4 = EApp (EApp (EDict ("ArrowTy")) p3) p3

ti4 :: Val
ti4 = interp $ Prog [] [] p4

p5 :: Exp
p5 = ECaseDict p4
      ("ArrowTy",["a","b"],
       ECaseDict "a" ("Int", [], EK "One")
                 (EK "Two")
      ) (EK "Three")

ti5 :: Val
ti5 = interp $ Prog [ints] [] p5

-- | Take a false branch
p6 :: Exp
p6 = ECaseDict p3
      ("->",["a","b"],
       ECaseDict "a" ("Int", [], EK "One")
                 (EK "Two")
      ) (EK "Three")

ti6 :: Val
ti6 = interp $ Prog [ints] [] p6

p7 :: Exp
p7 = EApp (ELam ("v",intTy) "v") (EK "Three")

intTy :: MonoTy
intTy = ConTy "Int" []

ti7 :: Val
ti7 = interp $ Prog [ints] [] p7