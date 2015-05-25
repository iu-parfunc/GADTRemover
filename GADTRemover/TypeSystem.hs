module TypeSystem where

import Data.String.Utils
import Data.List
import Data.Char


data Term = VarT String
			| Term String [Term]
			deriving (Show, Eq, Ord)

data Premise = Formula String [String] [Term] [Term]
			deriving (Show, Eq, Ord)
				
data Rule = Rule [Premise] Premise
			deriving (Show, Eq, Ord)

data SignatureEntry = Decl String String [String] 
			deriving (Show, Eq, Ord)			

data TypeSystem = Ts [SignatureEntry] [Rule] 
				  deriving (Show, Eq, Ord)

typePrefix :: String
typePrefix = "T"

outputTypePrefix :: String
outputTypePrefix = "O"

pmTypePrefix :: String
pmTypePrefix = "PM"

termPrefix :: String
termPrefix = "E"

typecheckPrefix :: String
typecheckPrefix = "typecheck"

toStringT :: Term -> String
toStringT (VarT variable) = variable
toStringT term = error "Error: toStringT is used for a complex term. Probably outputs does not contain variables."

sig :: String -> String -> Bool
sig c kind = if (kind == "type") && ((c == "arrow")) then True else False

isType :: Term -> Bool
isType (VarT variable) = not ((startswith termPrefix variable) || (startswith pmTypePrefix variable))
isType (Term c terms) = (sig c "type")

predicateOfPremise :: Premise -> String
predicateOfPremise (Formula pred strings interms outterms) = pred

extractTermFromConcl :: Premise -> Term 
extractTermFromConcl (Formula pred strings interms outterms) = head interms

injectTermInConcl :: Term -> Premise -> Premise 
injectTermInConcl term (Formula pred strings interms outterms) = (Formula pred strings (term:(tail interms)) outterms)

extractTypeFromConcl :: Premise -> Term 
extractTypeFromConcl (Formula pred strings interms outterms) = head outterms

injectTypeInConcl :: Term -> Premise -> Premise 
injectTypeInConcl term (Formula pred strings interms outterms) = (Formula pred strings interms (outtermsMinusLast ++ [term]))
				where
				outtermsMinusLast = drop ((length outterms) -1) outterms

toUpLowFirst :: String -> String -> String 
toUpLowFirst mode [] = []
toUpLowFirst mode (cc:rest) = cc':rest
							where 
							cc' = if mode == "up" then (toUpper cc) else (toLower cc)

