module GADTCreator where

import System.IO.Unsafe 
import Data.Unique
import qualified Data.Map as HM
import Data.List
import Data.Char
import DataType
import TypeSystem

gadtCreator :: TypeSystem -> DataType
gadtCreator (Ts rules) = (DataType (Constructor "Expr" [(Var "a")]) clauses)
				where
					clauses = map toClause rules 
					
toClause :: Rule -> Clause
toClause (Rule premises term typ) = (Clause c typexprs)
									where
									c = case term of (Term c' terms) -> c'
									typexprs = map entryTEXp premises

entryTEXp :: Premise -> TypeExpr
entryTEXp (Formula pred strings terms) = if pred == "typeOf" then (Constructor "Expr" [termTOtexpr (last terms)])
										 else error "ERROR: found a premise that I cannot process"

termTOtexpr :: Term -> TypeExpr
termTOtexpr (VarT variable) = (Var (toUpLowFirst "low" variable))
termTOtexpr (Term c terms) = (Constructor (toUpLowFirst "up" c) (map termTOtexpr terms))

toUpLowFirst :: String -> String -> String 
toUpLowFirst mode [] = []
toUpLowFirst mode (cc:rest) = cc':rest
							where 
							cc' = if mode == "up" then (toUpper cc) else (toLower cc)

