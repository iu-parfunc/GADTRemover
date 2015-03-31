module PatternMatching where

import System.IO.Unsafe 
import Data.Unique
import TypeSystem


gensymPM :: IO String
gensymPM = do 
			sym <- newUnique
			return (pmTypePrefix ++ show (hashUnique sym))
			
patternMatches :: TypeSystem -> TypeSystem
patternMatches (Ts rules) = (Ts (map patternMatchesR rules))

patternMatchesR :: Rule -> Rule 
patternMatchesR (Rule premises term typ) = (Rule (concat (map patternMatchesPr premises)) term typ) 
{-											where 
												([term'], fromConclusion) = patternMatchesTrms [term]
-}	

patternMatchesPr :: Premise -> [Premise]
patternMatchesPr (Formula pred strings terms types) = (Formula pred strings terms types'):pmPremises
									where 
									(types', pmPremises) = (patternMatchesTrms types)

patternMatchesTrms :: [Term] -> ([Term], [Premise])
patternMatchesTrms [] = ([],[])
patternMatchesTrms (typ:rest) = let (typesRest, pmPremisesRest) = (patternMatchesTrms rest) in
								 (case typ of 
									(VarT var) -> ((VarT var):typesRest, pmPremisesRest)
									(Term c terms) -> 
										let (outputsInner, outPremisesInner) = (patternMatchesTrms terms) in
										((VarT freshVar):typesRest, ((patternMatchesPr (Formula "match" [c] [(VarT freshVar)] outputsInner)) ++ pmPremisesRest)))
							where 
								freshVar = (unsafePerformIO gensymPM)

