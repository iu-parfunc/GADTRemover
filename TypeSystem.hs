module TypeSystem where
import Data.String.Utils

data Term = VarT String
			| Term String [Term]
			deriving (Show, Eq, Ord)


data Premise = Formula String [String] [Term]
			deriving (Show, Eq, Ord)
				
data Rule = Rule [Premise] Term Term
			deriving (Show, Eq, Ord)
			

data TypeSystem = Ts [Rule] 
				  deriving (Show, Eq, Ord)


