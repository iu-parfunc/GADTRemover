module FromTypeSystemToHaskell where

import Data.List
import Data.Char
import TypeSystem
import GADTRemover
import GADTCreator
import ToHaskell
import PatternMatching
import UpToConsistency
import ResolutionAndStatic

fromTStoHaskellIO :: TypeSystem -> IO ()
fromTStoHaskellIO ts = putStrLn (fromTStoHaskell ts)

fromTStoHaskellIO_ :: TypeSystem -> IO ()
fromTStoHaskellIO_ ts = putStrLn (fromTStoHaskell (Ts rules'))
						where
						((Ts rulesUP), equatedByRules) = (upToConsistencyEqualities (patternMatches ts))
						rules' = zipWith toGradualR rulesUP equatedByRules
						

fromTStoHaskell :: TypeSystem -> String
fromTStoHaskell (Ts rules) = "typechecker :: Expr -> * \n" ++ "typechecker term = case term of \n" ++ (concat (map fromTStoHaskell_Rule rules))

fromTStoHaskell_Rule :: Rule -> String
fromTStoHaskell_Rule (Rule premises term typ) = "\t" ++ (toHaskell_Trm term) ++ " -> \n\t\t" ++ letList ++ (concat caseOfs) ++ "   (if" ++ conditions ++ " then" ++ (toHaskell_Trm typ) ++ " else error \"Error: term does not typecheck\")\n" ++ otherwises 
							where
							letList = (concat (map toTypeCheckCalculate typeOfPremises))
							conditions = if (null conditions1) then " True" else intercalate " && " conditions1
							conditions1 = (map toEqualityTest equalityPremises)
							caseOfs = (map toCaseForPatternMatching matchPremises)
							otherwises = (concat (replicate (length caseOfs) "\t\totherwise -> error \"Error: term does not typecheck\"\n"))
							typeOfPremises = filter filterByTypeOf premises
							matchPremises = filter filterByMatch premises
							equalityPremises = filter filterByEqual premises
							filterByTypeOf = \premise -> case premise of (Formula pred strings interms outterms) -> if pred == "typeOf" then True else False
							filterByMatch = \premise -> case premise of (Formula pred strings interms outterms) -> if pred == "match" then True else False
							filterByEqual = \premise -> case premise of (Formula pred strings interms outterms) -> if pred == "equal" then True else False


toTypeCheckCalculate :: Premise -> String
toTypeCheckCalculate (Formula pred strings interms outterms) = "let" ++ (toHaskell_Trm (last outterms)) ++ " = " ++ "(typechecker" ++ (toHaskell_Trm (head interms)) ++ ")" ++ " in \n\t\t"

toEqualityTest :: Premise -> String
toEqualityTest (Formula pred strings interms outterms) = (toHaskell_Trm (head outterms)) ++ "==" ++ (toHaskell_Trm (last outterms))
												
toCaseForPatternMatching :: Premise -> String
toCaseForPatternMatching (Formula pred strings interms outterms) = "case" ++ (toHaskell_Trm (head interms)) ++ " of" ++ (toHaskell_Trm (Term (head strings) (outterms))) ++ " -> \n\t\t"

toHaskell_Trm :: Term -> String 
toHaskell_Trm term = toHaskell_TE (termTOtexpr term)

