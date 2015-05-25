module ResolutionAndStatic where

import System.IO.Unsafe 
import Data.Unique
import qualified Data.Map as HM
import Data.List
import TypeSystem
import PatternMatching 

{- 
import UpToConsistency 


toGradual :: TypeSystem -> TypeSystem
toGradual ts = (Ts sig rules') 
				where
					((Ts sig rulesUP), equatedByRules) = (upToConsistencyEqualities (patternMatches ts))
					rules' = zipWith toGradualR rulesUP equatedByRules

toGradualR :: Rule -> TrackOfVars -> Rule
toGradualR (Rule premises conclusion) outputs = (Rule premises conclusion')
				where
				typ = extractTypeFromConcl conclusion
				conclusion' = injectTypeInConcl (toGradualTrOne outputs typ) conclusion

toGradualPr :: TrackOfVars -> Premise -> Premise
toGradualPr outputs (Formula pred strings interms outterms) = (Formula pred strings (map (toGradualTrOne outputs) interms) outterms)


toGradualTrOne :: TrackOfVars -> Term -> Term
toGradualTrOne outputs (VarT variable) = let tmp = (HM.lookup (VarT variable) outputs) in
											case tmp of 
												Just values -> (head (tail values))
										  		Nothing -> (VarT variable)
toGradualTrOne outputs (Term c terms) = (Term c (map (toGradualTrOne outputs) terms))

-}

