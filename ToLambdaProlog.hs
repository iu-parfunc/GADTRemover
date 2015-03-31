module ToLambdaProlog where

import Data.List
import Data.Char
import TypeSystem

typeOf :: String
typeOf = "typeOf"

toLambdaPrologIO :: TypeSystem -> IO ()
toLambdaPrologIO ts = putStrLn (toLambdaProlog_ ts)

toLambdaProlog_ :: TypeSystem -> String
toLambdaProlog_ (Ts rules) = unlines (map toLambdaPrologR rules)
						
toLambdaPrologR :: Rule -> String 
toLambdaPrologR (Rule premises term typ) = 
			typeOf ++ " " ++ toLambdaPrologTerm term ++ " " ++ toLambdaPrologTerm typ ++ premisesIfAny ++ "."
			where 
			premisesIfAny = if (premisesWithComma == "") then "" else  " :- " ++ premisesWithComma
			premises' = (map toLambdaPrologPr premises)
			premisesWithComma = intercalate ", " premises'
			 
toLambdaPrologPr :: Premise -> String
toLambdaPrologPr (Formula pred info interms outterms) = pred ++ (concat info) ++ displayInputs ++ displayOutputs
											where
											displayInputs = if calculatedIn == "" then "" else " " ++ calculatedIn
											displayOutputs = if calculatedOut == "" then "" else " " ++ calculatedOut
											calculatedIn = (intercalate " " (map toLambdaPrologTerm interms)) 
											calculatedOut = (intercalate " " (map toLambdaPrologTerm outterms)) 

toLambdaPrologTerm :: Term -> String
toLambdaPrologTerm (VarT varterm) = varterm
toLambdaPrologTerm (Term c terms) = "(" ++ c ++ displayTerms ++ ")"
													where 
													displayTerms = if calculated == "" then "" else " " ++ calculated
													calculated = (intercalate " " (map toLambdaPrologTerm terms)) 

{-
toLambdaPrologPr mode (Match c typ types) = if (mode == "CI") then toLambdaPrologPr "Gr" (Match c typ types) else "match" ++ mode ++ c ++ " " ++ (intercalate " " ((toLambdaPrologType typ):(map toLambdaPrologType types)))
toLambdaPrologPr mode (Subtyping type1 type2) = if (mode == "CI") then toLambdaPrologPr "Gr" (Subtyping type1 type2) else "subtype" ++ mode ++ " " ++ toLambdaPrologType type1 ++ " " ++ toLambdaPrologType type2
toLambdaPrologPr mode (Flow type1 type2) = "flow " ++ toLambdaPrologType type1 ++ " " ++ toLambdaPrologType type2
toLambdaPrologPr mode (Join types typ) = "join" ++ (show (length types)) ++ " " ++ (intercalate " " ((map toLambdaPrologType types) ++ [toLambdaPrologType typ])) 
-}