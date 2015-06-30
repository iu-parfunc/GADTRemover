{-# LANGUAGE NamedFieldPuns #-}

-- | Conservative estimate of whether a type is Showable.

module Ghostbuster.Showable (showableDefs) where

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
  chkDDef DDef{cases} =
    -- Can't derive show for empty data types:
    not (null cases) &&
    L.all chkCase cases

  chkCase KCons {fields,outputs} =
    -- First criterion: only vars on the RHS:
    L.all isVar outputs &&
    -- And must be unique vars:
    (L.length outputs == S.size (S.fromList outputs)) &&
    -- Second criterion: no existentials
    S.null (S.difference (ftv fields) (ftv outputs))


-- The basic rule here is that ONLY type variables are allowed on GADT RHS:
isVar :: MonoTy -> Bool
isVar (VarTy _) = True
isVar _         = False

gatherDeps :: DDef -> S.Set TName
gatherDeps DDef{cases} = S.unions
  [ S.unions (map gatherTypesMentioned fields ++
              map gatherTypesMentioned outputs)
  | KCons{fields,outputs} <- cases ]
