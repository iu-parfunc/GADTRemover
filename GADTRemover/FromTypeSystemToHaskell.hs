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
fromTStoHaskellIO_ ts = putStrLn (fromTStoHaskell (Ts sig rules))
						where
						((Ts sig rulesUP), equatedByRules) = (upToConsistency (patternMatches ts))
                                                rules = map eliminateDuplicatePremises rulesUP
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
                                                        returnInstruction = "return $ " ++ (sealedType nameOfMainType) ++ " $ " ++ (returnType term premises)
                                                        typ = extractTypeFromConcl conclusion
                                                        returnType = \term -> \premises -> case term of (Term c terms) -> encodingClassOfG ++ "." ++ (toUpLowFirst "up" c) ++ " " ++ (intercalate " " (map toHaskell_Trm (map (lookupTheVarForTerm premises) terms)))

lookupTheVarForTerm :: [Premise] -> Term -> Term
lookupTheVarForTerm [] term = error "Not all the arguments of an operator are typed-checked."
lookupTheVarForTerm (premise:rest) term = case premise of (Formula pred strings interms outterms) -> if (startswith typecheckPrefix pred) && ((interms !! 0) == term) then (outterms !! 0) else lookupTheVarForTerm rest term

fromPremisesToHaskell :: String -> [String] -> Premise -> String
fromPremisesToHaskell nameOfMainType inputarguments (Formula pred strings interms outterms) = "\t" ++ instruction
                                                        where
                                                        input = toHaskell_Trm (interms !! 0)   -- notice: it uses the _ version for dropping the beginning " " 
                                                        output = toHaskell_Trm (outterms !! 0)  -- drop the beginning " " 
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
                                                              "equal" -> let internalIntput2 = "t" ++ (toHaskell_Trm (interms !! 1)) in
                                                                      "Refl <- unify (unused :: " ++ internalIntput ++ " ) (unused::" ++ internalIntput2 ++ ")"
                                                              otherwise -> "some other call, like constraint (Num a) "
                                                        
{-

let internalIntput2 = "t" ++ (drop 1 (toHaskell_Trm (interms !! 1))) in 

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
toHaskell_Trm term = drop 1 (toHaskell_TE (termTOtexpr term))

{-
termTOhaskellTerm :: Term -> Term 
termTOhaskellTerm (VarT variable) = (VarT (toUpLowFirst "up" variable))
termTOhaskellTerm (Term c terms) = (Term (map toLower c) (map termTOhaskellTerm terms))
-}

