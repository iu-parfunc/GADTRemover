module GADTCreator where

import System.IO.Unsafe 
import Data.Unique
import Data.String.Utils
import qualified Data.Map as HM
import DataType
import TypeSystem

gadtCreator :: TypeSystem -> [DataType]
gadtCreator (Ts sig rules) = map (toDataType rules) gadtNames 
					where
					gadtNames = (filter filterByGadt sig)
					filterByGadt = \entry -> case entry of (Decl c output types) -> (startswith typecheckPrefix c) 


toDataType :: [Rule] -> SignatureEntry -> DataType
toDataType rules (Decl c output types) = (DataType (Constructor c' newvars) signature clauses)
				where
					rulesForC = filter onlyThoseForC rules
					clauses = map toClause rulesForC
					signature = types
					onlyThoseForC = \rule -> case rule of (Rule premises conclusion) -> (predicateOfPremise conclusion) == c
					c' = minusTypecheckPrefix c
					newvars = map (\n -> (Var ("a" ++ (show n)))) [1 .. (length types)]
					
minusTypecheckPrefix :: String -> String
minusTypecheckPrefix c = let len = length "typecheck" in if (startswith "typecheck" c) then drop len c else error "Error: expected predicate typecheckNAME"
					
toClause :: Rule -> Clause
toClause (Rule premises conclusion) = (Clause c typexprs)
									where
									term = extractTermFromConcl conclusion
									c = case term of (Term c' terms) -> c'
									typexprs = map entryTEXp premises

entryTEXp :: Premise -> TypeExpr
entryTEXp (Formula pred strings interms outterms) = if pred == "typeOf" then (Constructor "Expr" [termTOtexpr (last outterms)])
										 else error "ERROR: found a premise that I cannot process"

termTOtexpr :: Term -> TypeExpr
termTOtexpr (VarT variable) = (Var (toUpLowFirst "low" variable))
termTOtexpr (Term c terms) = (Constructor (toUpLowFirst "up" c) (map termTOtexpr terms))

