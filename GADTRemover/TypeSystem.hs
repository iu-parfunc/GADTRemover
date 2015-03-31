module TypeSystem where
import Data.String.Utils

data Term = VarT String
			| Term String [Term]
			deriving (Show, Eq, Ord)

data Premise = Formula String [String] [Term] [Term]
			deriving (Show, Eq, Ord)
				
data Rule = Rule [Premise] Term Term
			deriving (Show, Eq, Ord)
			

data TypeSystem = Ts [Rule] 
				  deriving (Show, Eq, Ord)

typePrefix :: String
typePrefix = "T"

outputTypePrefix :: String
outputTypePrefix = "O"

pmTypePrefix :: String
pmTypePrefix = "PM"

termPrefix :: String
termPrefix = "E"

toStringT :: Term -> String
toStringT (VarT variable) = variable
toStringT term = error "Error: toStringT is used for a complex term. Probably outputs does not contain variables."

sig :: String -> String -> Bool
sig c kind = if (kind == "type") && (c == "arrow") then True else False

isType :: Term -> Bool
isType (VarT variable) = not ((startswith termPrefix variable) || (startswith pmTypePrefix variable))
isType (Term c terms) = (sig c "type")
