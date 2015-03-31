module UpToConsistency where

import System.IO.Unsafe 
import Data.Unique
import qualified Data.Map as HM
import Data.List
import TypeSystem
import PatternMatching 

type TrackOfVars = (HM.Map Term [Term])

{- Instead of generating a type sytem with binary equalities, an hashmap TrackOfVars will keep track of the equated types. 
-}

gensymTT :: IO String
gensymTT = do 
			sym <- newUnique
			return (outputTypePrefix ++ show (hashUnique sym))

upToConsistency :: TypeSystem -> TypeSystem
upToConsistency ts = (Ts rules')
				where
					((Ts rules), equatedByRules) = (upToConsistencyEqualities (patternMatches ts))
					rules' = insertJoinAndConsistency equatedByRules rules

insertJoinAndConsistency :: [TrackOfVars] -> [Rule] -> [Rule] 
insertJoinAndConsistency equatedByRules rules = zipWith insertJoin rules newPremises
									where
									newPremises = map equalityPremise equatedByRules
									insertJoin = (\x -> \y -> case x of 
											(Rule premises term typ) -> (Rule (premises ++ y) term typ)) 

		
equalityPremise :: TrackOfVars -> [Premise]
equalityPremise equated = concat (map snd (HM.toList addedPremises)) where
						addedPremises = HM.map (wrappingEquation equated) (HM.delete (VarT "TYPEINPUTS") equated)


wrappingEquation :: TrackOfVars -> [Term] -> [Premise]
wrappingEquation equated [] = []
wrappingEquation equated (type1:rest) = if (null rest) then [] else (Formula "equal" [] [] [type1, (head rest)]):(wrappingEquation equated rest)

upToConsistencyEqualities :: TypeSystem -> (TypeSystem, [TrackOfVars])
upToConsistencyEqualities (Ts rules) = ((Ts rules'), outputs)
						where
							setOfPairs = (map upToConsistencyR rules)
							rules1 = map fst setOfPairs
							outputs = map snd setOfPairs
							rules' = insertJoinAndConsistency outputs rules1

upToConsistencyR :: Rule -> (Rule , TrackOfVars)
upToConsistencyR (Rule premises term typ) = ((Rule (premises') term' typ) , outputs)
									where 
										(premises', outputs1) = upToConsistencyPr premises HM.empty 
										(term', outputs) = upToConsistencyTrmOne term outputs1 

										
upToConsistencyPr :: [Premise] -> TrackOfVars -> ([Premise], TrackOfVars)
upToConsistencyPr [] outputs =  ([], outputs)
upToConsistencyPr (premise:rest) outputs =  (premise':rest', outputs')
									where
										(premise', outputs1) = upToConsistencyPrOne premise outputs 
										(rest', outputs') = upToConsistencyPr rest outputs1 

upToConsistencyPrOne :: Premise -> TrackOfVars -> (Premise, TrackOfVars)
upToConsistencyPrOne (Formula pred strings interms outterms) outputs = ((Formula pred strings interms outterms'), outputs')
									where 
										(outterms', outputs1) = upToConsistencyTrm outterms outputs
										outputs' = if (pred == "match") && ((length interms) >= 2) then (trackOfTypeInputs outputs1 (drop 1 interms)) else outputs1
									
trackOfTypeInputs :: TrackOfVars -> [Term] -> TrackOfVars
trackOfTypeInputs equated typeinputs = insertTypeInputs inputsRecorded typeinputs
										where inputsRecorded = let tmp = (HM.lookup (VarT "TYPEINPUTS") equated) in
												case tmp of 
													Just values -> (HM.adjust (++ typeinputs) (VarT "TYPEINPUTS") equated)
													Nothing -> (HM.insert (VarT "TYPEINPUTS") typeinputs equated)
														
insertTypeInputs :: TrackOfVars -> [Term] -> TrackOfVars
insertTypeInputs outputs [] = outputs
insertTypeInputs outputs (typ:rest) = (insertTypeInputs outputs' rest)
									where outputs' = (let tmp = (HM.lookup typ outputs) in
														(case tmp of 
															Just values -> outputs
										  					Nothing -> (HM.insert typ [typ] outputs)))


upToConsistencyTrm :: [Term] -> TrackOfVars -> ([Term], TrackOfVars)
upToConsistencyTrm [] outputs = ([], outputs)
upToConsistencyTrm (term:rest) outputs = (term':rest', outputs')
									where
										(term', outputs1) = upToConsistencyTrmOne term outputs
										(rest', outputs') = upToConsistencyTrm rest outputs1

upToConsistencyTrmOne :: Term -> TrackOfVars -> (Term, TrackOfVars)
upToConsistencyTrmOne (VarT variable) outputs = if (isType (VarT variable)) then (let tmp = (HM.lookup (VarT variable) outputs) in
													(case tmp of 
														Just values -> ((VarT freshVar), (HM.adjust (++ [(VarT freshVar)]) (VarT variable) outputs))
										  				Nothing -> ((VarT freshVar), (HM.insert (VarT variable) [(VarT freshVar)] outputs))))											
												else ((VarT variable), outputs)
												where 
													freshVar = (unsafePerformIO gensymTT)
upToConsistencyTrmOne (Term c terms) outputs = ((Term c terms'), outputs1)
												where 
												(terms', outputs1) = upToConsistencyTrm terms outputs

{-
upToConsistencyTrmOne term outputs = error "Error: Unexpected form in output position: Encode"
-}

