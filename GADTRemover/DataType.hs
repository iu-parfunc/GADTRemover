module DataType where

import qualified Data.Map as HM

type CastsToDo = (HM.Map String [(Int, TypeExpr)])

data DataType = DataType TypeExpr [String] [Clause]
				deriving (Show, Eq, Ord)


data Clause = Clause String [TypeExpr]
				deriving (Show, Eq, Ord)
				
data TypeExpr = 
			Constructor String [TypeExpr]
			| Var String
			deriving (Show, Eq, Ord)


{- Auxiliary -}

fst3 :: (a, b, c) -> a
fst3 (x,_,_) = x

snd3 :: (a, b, c) -> b
snd3 (_,x,_) = x

thd3 :: (a, b, c) -> c
thd3 (_,_,x) = x

principalType :: TypeExpr -> String
principalType (Var variable) = variable
principalType (Constructor c types) = c