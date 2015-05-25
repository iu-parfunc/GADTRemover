module Examples
(
  module DataType,
  module TypeSystem,
  module GADTRemover,
  module GADTCreator,
  module ToHaskell,
  module RetrieveCasts,
  module ToLambdaProlog,
  module FromTypeSystemToHaskell,
--  module UpToConsistency,
  int, bool, arrowWithVars, gadt_exp
 )
 where

import DataType
import TypeSystem
import GADTRemover
import ToLambdaProlog
import FromTypeSystemToHaskell
import ToHaskell
import RetrieveCasts
import UpToConsistency
import GADTCreator

import ResolutionAndStatic
import PatternMatching

int :: TypeExpr
int = Constructor "Int" []

bool :: TypeExpr
bool = Constructor "Bool" []

arrowWithVars :: String -> String -> TypeExpr
arrowWithVars a b = Constructor "Arrow" [(Var a), (Var b)]

expSignature :: TypeExpr
expSignature = Constructor "Exp" [(Var "e"), (Var "a")]

typedSignature :: [String]
typedSignature = ["Env", "*"]

gadt_exp :: DataType
gadt_exp = (DataType expSignature typedSignature [plusClause, ifClause, varClause, appClause])

plusClause :: Clause
plusClause = (Clause "Add" [
				(Constructor "Exp" [(Var "env"), int]),
				(Constructor "Exp" [(Var "env"), int]),
				(Constructor "Exp" [(Var "env"), int])
			])

ifClause :: Clause
ifClause = (Clause "If" [
				(Constructor "Exp" [(Var "env"), bool]),
				(Constructor "Exp" [(Var "env"), (Var "a")]),
				(Constructor "Exp" [(Var "env"), (Var "a")]),
				(Constructor "Exp" [(Var "env"), (Var "a")])
			])

varClause :: Clause
varClause = (Clause "VarE" [
				(Constructor "Var" [(Var "env"), (Var "a")]),
				(Constructor "Exp" [(Var "env"), (Var "a")])
			])


appClause :: Clause
appClause = (Clause "App" [
			(Constructor "Exp" [(Var "env"), (arrowWithVars "a" "b")]),
			(Constructor "Exp" [(Var "env"), (Var "a")]),
			(Constructor "Exp" [(Var "env"), (Var "b")])
			])

gadt_env :: DataType
gadt_env = (DataType (Constructor "Env" [(Var "e")]) ["Pair"] [emptyClause, extendClause])

emptyClause :: Clause
emptyClause = (Clause "Emp" [
			(Constructor "Env" [(Constructor "pair" [])])
			])

extendClause :: Clause
extendClause = (Clause "Ext" [
			(Constructor "Env" [(Var "e")]),
			(Var "a"),
			(Constructor "Env" [(Constructor "pair" [(Var "e"), (Var "a")])])
			])

definitions :: [DataType]
definitions = [gadt_exp, gadt_env]

tsexample :: TypeSystem
tsexample = Ts [Decl "typecheckExp" "o" ["Exp","Env","*"]] [Rule [Formula "typecheckExp" [] [VarT "E1",VarT "Env"] [Term "bool" []],Formula "typecheckExp" [] [VarT "E2",VarT "Env"] [VarT "A"],Formula "typecheckExp" [] [VarT "E3",VarT "Env"] [VarT "A"]] (Formula "typecheckExp" [] [Term "if" [VarT "E1",VarT "E2",VarT "E3"],VarT "Env"] [VarT "A"]),Rule [Formula "typecheckExp" [] [VarT "E1",VarT "Env"] [VarT "A"]] (Formula "typecheckExp" [] [Term "vare" [VarT "E1"],VarT "Env"] [VarT "A"]),Rule [Formula "typecheckExp" [] [VarT "E1",VarT "Env"] [Term "arrow" [VarT "A",VarT "B"]],Formula "typecheckExp" [] [VarT "E2",VarT "Env"] [VarT "A"]] (Formula "typecheckExp" [] [Term "app" [VarT "E1",VarT "E2"],VarT "Env"] [VarT "B"])]

{-
Rule [Formula "typecheckExp" [] [VarT "E1",VarT "Env"] [Term "int" []],Formula "typecheckExp" [] [VarT "E2",VarT "Env"] [Term "int" []]] (Formula "typecheckExp" [] [Term "add" [VarT "E1",VarT "E2"],VarT "Env"] [Term "int" []]),
-}
