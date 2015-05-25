module FromTypeSystemToHaskell where

import Data.List
import Data.Char
import Data.String.Utils
import TypeSystem
import GADTRemover
import GADTCreator
import ToHaskell
import PatternMatching
import UpToConsistency
import ResolutionAndStatic

sealedPrefix :: String
sealedPrefix = "Sealed"

sealedType :: String -> String
sealedType name = sealedPrefix ++ name

sealedInterface :: String -> [String] -> String
sealedInterface name vars = (sealedType name) ++ " " ++ (intercalate " " vars)

downcastPrefix :: String
downcastPrefix = "downcast"

downcastFunction :: String -> String
downcastFunction name = downcastPrefix ++ name

encodingClassOfG :: String
encodingClassOfG = "G"

conventionNameForArguments :: String
conventionNameForArguments = "arg"

conventionNameForOutput :: String
conventionNameForOutput = "out"



fromTStoHaskellIO :: TypeSystem -> IO ()
fromTStoHaskellIO ts = putStrLn (fromTStoHaskell ts)

fromTStoHaskellIO_ :: TypeSystem -> IO ()
fromTStoHaskellIO_ ts = putStrLn (fromTStoHaskell (Ts sig rulesUP))
						where
						((Ts sig rulesUP), equatedByRules) = (upToConsistency (patternMatches ts))
						{- rules' = zipWith toGradualR rulesUP equatedByRules -}
						
fromTStoHaskell :: TypeSystem -> String
fromTStoHaskell (Ts sig rules) = unlines (map fromSignatureToSealed sig) ++ unlines (map (fromTStoDowncast rules) sig)

fromSignatureToSealed :: SignatureEntry -> String
fromSignatureToSealed (Decl c output signature) = "Data " ++ sealed ++ " where \n\t" ++ singleClause
                                                        where
                                                        sealed = (sealedInterface nameOfMainType inputarguments)
                                                        nameOfMainType = (signature !! 0)
                                                        inputarguments = (map (\n -> conventionNameForArguments ++ (show n)) [1 .. ((length signature) - 2)])
                                                        singleClause = (sealedType nameOfMainType) ++ " :: " ++ typeableForOutputVar ++ " => " ++ encodedTypeInG ++ " -> " ++ (sealedInterface nameOfMainType inputarguments)
                                                        typeableForOutputVar = "Typeable " ++ conventionNameForOutput
                                                        allArguments = intercalate " " (inputarguments ++ [conventionNameForOutput])
                                                        encodedTypeInG = encodingClassOfG ++ "." ++ nameOfMainType ++ " " ++ allArguments


fromTStoDowncast :: [Rule] -> SignatureEntry -> String
fromTStoDowncast rules (Decl c output signature) = if output == "o" && (startswith typecheckPrefix c) then (preamble ++ (intercalate "\n" (map (fromTStoHaskell_Rule nameOfMainType inputarguments) (filter onlyTheOnesForC rules)))) else ""
							where
							onlyTheOnesForC = \rule -> case rule of (Rule premises conclusion) -> (predicateOfPremise conclusion) == (c)
                                                        nameOfMainType = (signature !! 0)
							preamble = (downcastFunction nameOfMainType) ++ " :: " ++ foralls ++ constraints ++ " => " ++ functionsig ++ "\n"
							inputarguments = map (\n -> conventionNameForArguments ++ (show n)) [1 .. ((length signature) - 2)]
                                                        concatenatedInputarguments = intercalate " " inputarguments
                                                        foralls = "forall " ++ concatenatedInputarguments ++ " . "
                                                        constraints = intercalate " => " generatedConstraints
                                                        generatedConstraints = map (\e -> "Typeable " ++ e) inputarguments
                                                        functionsig = nameOfMainType ++ " -> " ++ outputSig
                                                        outputSig = "Maybe (" ++ (sealedInterface nameOfMainType inputarguments) ++ ")"


						
fromTStoHaskell_Rule :: String -> [String] -> Rule -> String
fromTStoHaskell_Rule nameOfMainType inputarguments (Rule premises conclusion) =  (downcastFunction nameOfMainType) ++ " " ++ (toHaskell_Trm term) ++ " = do \n" ++ instructionsFromPremises ++ "\n \t" ++ returnInstruction 
							where
							term = extractTermFromConcl conclusion
                                                        instructionsFromPremises = intercalate "\n" (map (fromPremisesToHaskell nameOfMainType inputarguments) premises)
                                                        returnInstruction = "return " ++ (sealedType nameOfMainType) ++ " " ++ (returnType typ)
                                                        typ = extractTypeFromConcl conclusion
                                                        returnType = \typ -> (toHaskell_Trm typ) -- to be changed. 


fromPremisesToHaskell :: String -> [String] -> Premise -> String
fromPremisesToHaskell nameOfMainType inputarguments (Formula pred strings interms outterms) = "\t" ++ instruction
                                                        where
                                                        input = drop 1 (toHaskell_Trm (interms !! 0))   -- drop the first " " 
                                                        output = drop 1 (toHaskell_Trm (outterms !! 0))
                                                        instruction = if (startswith typecheckPrefix pred) then downcastInstruction else other
                                                        whichTypeForRecursiveCall = drop (length typecheckPrefix) pred 
                                                        downcastInstruction = (sealedType whichTypeForRecursiveCall) ++ " (" ++ feedFromG ++ ")" ++ " <- " ++ recursiveCall
                                                        feedFromG = output ++ "::" ++ encodingClassOfG ++ "." ++ whichTypeForRecursiveCall ++ concatenatedInputarguments ++ " " ++ internalOutput
                                                        internalOutput = "t" ++ output
                                                        internalIntput = "t" ++ input
                                                        concatenatedInputarguments = " " ++ (intercalate " " inputarguments)
                                                        recursiveCall = (downcastFunction whichTypeForRecursiveCall) ++ " " ++ input
                                                        other = case pred of
                                                              "match" -> "Refl <- unify (unused :: " ++ internalIntput ++ " ) (unused::" ++ (strings !! 0) ++ ")"
                                                              "equal" -> "equal, to be defined"
                                                              otherwise -> "some other call, like constraint (Num a) "
                                                        
{-
case pred of 
                                                             "match" ->
                                                             "equal" -> 
conditions = if (null conditions1) then " True" else intercalate " && " conditions1
							conditions1 = (map toEqualityTest equalityPremises)
							caseOfs = (map toCaseForPatternMatching matchPremises)
							otherwises = (concat (replicate (length caseOfs) "\t\totherwise -> error \"Error: term does not typecheck\"\n"))
							typeOfPremises = filter filterByTypeOf premises
							matchPremises = filter filterByMatch premises
							equalityPremises = filter filterByEqual premises
							filterByTypeOf = \premise -> case premise of (Formula pred strings interms outterms) -> if pred == c then True else False
							filterByMatch = \premise -> case premise of (Formula pred strings interms outterms) -> if pred == "match" then True else False
							filterByEqual = \premise -> case premise of (Formula pred strings interms outterms) -> if pred == "equal" then True else False

-}

toTypeCheckCalculate :: String -> [String] -> Premise -> String
toTypeCheckCalculate c newarguments (Formula pred strings interms outterms) = "let" ++ (toHaskell_Trm (last outterms)) ++ " = (" ++ c ++ (toHaskell_Trm (head interms)) ++ " " ++ (intercalate " " newarguments) ++ ")" ++ " in \n\t\t"

toEqualityTest :: Premise -> String
toEqualityTest (Formula pred strings interms outterms) = (toHaskell_Trm (head outterms)) ++ "==" ++ (toHaskell_Trm (last outterms))
												
toCaseForPatternMatching :: Premise -> String
toCaseForPatternMatching (Formula pred strings interms outterms) = "case" ++ (toHaskell_Trm (head interms)) ++ " of" ++ (toHaskell_Trm (Term (head strings) (outterms))) ++ " -> \n\t\t"

toHaskell_Trm :: Term -> String 
toHaskell_Trm term = toHaskell_TE (termTOtexpr term)

{-
termTOhaskellTerm :: Term -> Term 
termTOhaskellTerm (VarT variable) = (VarT (toUpLowFirst "up" variable))
termTOhaskellTerm (Term c terms) = (Term (map toLower c) (map termTOhaskellTerm terms))
-}

