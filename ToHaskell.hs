{- 
This file is part of the GADTRemover.
Author: Matteo Cimini
-}

module ToHaskell where

import Data.List
import Data.Char
import DataType
import GADTRemover

toHaskellIO :: DataType -> IO ()
toHaskellIO gadt = putStrLn (toHaskell gadt)

toHaskell :: DataType -> String
toHaskell (DataType txpr clauses) = "Data " ++ toHaskell_TE txpr ++ " where\n" ++ (concat (map toHaskell_CL clauses))

toHaskell_CL :: Clause -> String
toHaskell_CL (Clause c texprs) = "    " ++ c ++ " :: " ++ texprsAddedArrows ++ "\n"
			where
			texprsAddedArrows = intercalate " -> " (map toHaskell_TE texprs)

toHaskell_TE :: TypeExpr -> String
toHaskell_TE (Var variable) = " " ++ variable
toHaskell_TE (Constructor c texprs) =  if (null texprs) then " " ++ c else " (" ++ c ++ (concat (map toHaskell_TE texprs)) ++ ")"



{-
toLambdaProlog_ mode' ts' where 
					(mode', ts') = case mode of 
						"Original" -> ("", ts)
						"Gradual" -> ("Gr", (toGradual ts))
						"CC" -> ("CC", toTypeSystemForCC ts)
						"CI" -> ("CI", (castInsertion ts))

toLambdaProlog_ :: String -> TypeSystem -> String
toLambdaProlog_ mode (Ts sig rules) = unlines (map (toLambdaPrologR mode) rules)
						
toLambdaPrologR :: String -> Rule -> String 
toLambdaPrologR mode (Rule premises term typ) = 
			typeOf ++ mode ++ " " ++ toLambdaPrologTerm term ++ " " ++ toLambdaPrologTerm typ ++ premisesIfAny ++ "."
			where 
			premisesIfAny = if (premisesWithComma == "") then "" else  " :- " ++ premisesWithComma
			premises' = (map (toLambdaPrologPr mode) premises)
			premisesWithComma = intercalate ", " premises'
			 
toLambdaPrologPr :: String -> Premise -> String
toLambdaPrologPr mode (Formula pred info interms outterms) = let pred' = (if (isUserPredicate pred) then pred ++ mode else pred) in 
												pred' ++ (concat info) ++ displayInputs ++ displayOutputs
												where
												displayInputs = if calculatedIn == "" then "" else " " ++ calculatedIn
												displayOutputs = if calculatedOut == "" then "" else " " ++ calculatedOut
												calculatedIn = (intercalate " " (map toLambdaPrologTerm interms)) 
												calculatedOut = (intercalate " " (map toLambdaPrologTerm outterms)) 
												
toLambdaPrologPr mode (Hypothetical bound term1 type1 term2 type2) = "(pi " ++ bound ++ "\\ (" ++ hypothetical ++ " => " ++ body ++ "))" where
												hypothetical = toLambdaPrologPr mode (Formula typeOf []  [term1] [type1])
												{- term1'= if (mode == "CI") then (Encode term1 term1) else term1 -}
												body = toLambdaPrologPr mode (Formula typeOf [] [term2] [type2])


toLambdaPrologTerm :: Term -> String
toLambdaPrologTerm (Var varterm) = varterm
toLambdaPrologTerm (Constructor c interms outterms) = "(" ++ c ++ displayInputs ++ displayOutputs ++ ")"
													where 
													displayInputs = if calculatedIn == "" then "" else " " ++ calculatedIn
													displayOutputs = if calculatedOut == "" then "" else " " ++ calculatedOut
													calculatedIn = (intercalate " " (map toLambdaPrologTerm interms)) 
													calculatedOut = (intercalate " " (map toLambdaPrologTerm outterms)) 

toLambdaPrologTerm (Application term1 term2) = "(" ++ toLambdaPrologTerm term1 ++ " " ++ toLambdaPrologTerm term2 ++ ")"
toLambdaPrologTerm (Bound x) = x
toLambdaPrologTerm (Encode term1 term2) = toLambdaPrologTerm term1 ++ " " ++ toLambdaPrologTerm term2
toLambdaPrologTerm (Lambda boundvar term) = "(" ++ boundvar ++ "\\ " ++ toLambdaPrologTerm term ++ ")"


toLambdaPrologPr mode (Match c typ types) = if (mode == "CI") then toLambdaPrologPr "Gr" (Match c typ types) else "match" ++ mode ++ c ++ " " ++ (intercalate " " ((toLambdaPrologType typ):(map toLambdaPrologType types)))
toLambdaPrologPr mode (Subtyping type1 type2) = if (mode == "CI") then toLambdaPrologPr "Gr" (Subtyping type1 type2) else "subtype" ++ mode ++ " " ++ toLambdaPrologType type1 ++ " " ++ toLambdaPrologType type2
toLambdaPrologPr mode (Flow type1 type2) = "flow " ++ toLambdaPrologType type1 ++ " " ++ toLambdaPrologType type2
toLambdaPrologPr mode (Join types typ) = "join" ++ (show (length types)) ++ " " ++ (intercalate " " ((map toLambdaPrologType types) ++ [toLambdaPrologType typ])) 
-}