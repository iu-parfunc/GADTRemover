module Examples where

import DataType
import TypeSystem
import GADTRemover
import GADTCreator
import ToHaskell
import RetrieveCasts
import ToLambdaProlog
import FromTypeSystemToHaskell
import UpToConsistency


int :: TypeExpr
int = Constructor "Int" []

bool :: TypeExpr
bool = Constructor "Bool" []

arrowWithVars :: String -> String -> TypeExpr
arrowWithVars a b = Constructor "Arrow" [(Var a), (Var b)]

expSignature :: TypeExpr
expSignature = Constructor "Exp" [(Var "a")] 

gadt_exp :: DataType
gadt_exp = (DataType expSignature [plusClause, ifClause, appClause])

plusClause :: Clause
plusClause = (Clause "add" [
				(Constructor "Exp" [int]),
				(Constructor "Exp" [int]),
				(Constructor "Exp" [int])
			])

ifClause :: Clause
ifClause = (Clause "if" [
				(Constructor "Exp" [bool]),
				(Constructor "Exp" [(Var "a")]),
				(Constructor "Exp" [(Var "a")]),
				(Constructor "Exp" [(Var "a")])
			])


appClause :: Clause
appClause = (Clause "app" [
			(Constructor "Exp" [arrowWithVars "a" "b"]),
			(Constructor "Exp" [(Var "a")]),
			(Constructor "Exp" [(Var "b")])
			])
