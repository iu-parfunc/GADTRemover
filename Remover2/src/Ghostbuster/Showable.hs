{-# LANGUAGE NamedFieldPuns #-}

-- | Conservative estimate of whether a type is Showable.

module Ghostbuster.Showable where

import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import           Ghostbuster.Types
import           Ghostbuster.Utils
import qualified Data.List as L

-- | Return a list of type names which can all be activated for "deriving Show"
showableDefs :: [DDef] -> S.Set TName
showableDefs ddefs =
  S.difference (S.fromList $ map tyName ddefs)
               allBads
  where
  bads = [ tyName dd | dd <- ddefs, (not (chkDDef dd)) ]

  -- Compute the fixpoint of deps to find ALL disqualified types.
  allBads = S.union (S.fromList bads)
                    (S.unions [ allDeps M.! b | b <- bads ])

  allDeps :: M.Map TName (S.Set TName)
  allDeps = transDeps deps

  transDeps [] = M.empty
  transDeps ((x,ys):rst) =
    let mp = transDeps rst
        deps' = S.unions
                [ case M.lookup y mp of
                    Nothing -> S.empty
                    Just s  -> s
                | y <- S.toList ys ]
    in M.insert x deps' mp
  deps :: [(TName, (S.Set TName))]
  deps = [ (tyName, gatherDeps dd) | dd@DDef{tyName} <- ddefs ]

  -- Does the definition violate our consvervative rules?
  chkDDef :: DDef -> Bool
  chkDDef DDef{cases} = L.all chkCase cases

  chkCase KCons {outputs} = L.all chkOutput outputs

  -- The basic rule here is that ONLY type variables are allowed on GADT RHS:
  chkOutput (VarTy _) = True
  chkOutput _         = False

gatherDeps :: DDef -> S.Set TName
gatherDeps DDef{cases} = S.unions
  [ S.unions (map gatherTypesMentioned fields ++
              map gatherTypesMentioned outputs)
  | KCons{fields,outputs} <- cases ]