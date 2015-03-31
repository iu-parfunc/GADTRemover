module ResolutionAndStatic where

import System.IO.Unsafe 
import Data.Unique
import qualified Data.Map as HM
import Data.List
import TypeSystem
import PatternMatching 
import UpToConsistency 

suffixGr :: String
suffixGr = "Gr"

toGradual :: TypeSystem -> TypeSystem
toGradual ts = (Ts rules') 
				where
					((Ts rulesUP), equatedByRules) = (upToConsistencyEqualities (patternMatches ts))
					rules' = zipWith toGradualR rulesUP equatedByRules

toGradualR :: Rule -> TrackOfVars -> Rule
toGradualR (Rule premises term typ) outputs = (Rule premises term (toGradualTrOne outputs typ))

toGradualPr :: TrackOfVars -> Premise -> Premise
toGradualPr outputs (Formula pred strings interms outterms) = (Formula pred strings (map (toGradualTrOne outputs) interms) outterms)

toGradualTrOne :: TrackOfVars -> Term -> Term
toGradualTrOne outputs (VarT variable) = let tmp = (HM.lookup (VarT variable) outputs) in
											case tmp of 
												Just values -> (head values)
										  		Nothing -> (VarT variable)
toGradualTrOne outputs (Term c terms) = (Term c (map (toGradualTrOne outputs) terms))

