module GADTRemover where

import System.IO.Unsafe 
import Data.Unique
import Data.Char
import qualified Data.Map as HM
import DataType
import TypeSystem

gensymTT :: IO String
gensymTT = do 
			sym <- newUnique
			return ("T" ++ show (hashUnique sym))

fromGDTAtoADT :: DataType -> DataType 
fromGDTAtoADT gadt = fst3 (fromGDTAtoAll gadt)

fromGDTAtoTypeSystem :: DataType -> TypeSystem 
fromGDTAtoTypeSystem gadt = snd3 (fromGDTAtoAll gadt)

fromGDTAtoCasts :: DataType -> CastsToDo 
fromGDTAtoCasts gadt = thd3 (fromGDTAtoAll gadt)

fromGDTAtoAll :: DataType -> (DataType, TypeSystem, CastsToDo)
fromGDTAtoAll (DataType cdef signature clauses) = 
						(case cdef of 
						 (Constructor c args) -> (adt, ts, trackOfCasts)
						 	where
						 	adt = (DataType (Constructor c []) signature clauses')
						 	clauses' = map (stripArgs c) clauses
						 	allMappings = getCasts c clauses
							trackOfCasts = onlyCastsIn allMappings
						 	rules = createRules (typecheckPrefix ++ c) clauses allMappings
							ts = (Ts [signatureTS] rules)
							signatureTS = createSignature cdef signature) 
						
stripArgs :: String -> Clause -> Clause
stripArgs cdef (Clause c texprs) = (Clause c (map (stripArgs_TE cdef) texprs))

stripArgs_TE :: String -> TypeExpr -> TypeExpr
stripArgs_TE cdef (Constructor c texpr) = (Constructor c [])
{- if c == cdef then (Constructor c []) else (Constructor c texpr) -}

getCasts :: String -> [Clause] -> CastsToDo
getCasts cdef [] = HM.empty
getCasts cdef (clause:rest) = (case clause of 
								(Clause c texprs) -> HM.union currentCast (getCasts cdef rest)
									where 
									currentCast = (HM.insert c castsByPositon HM.empty)
									castsByPositon = zip [1 .. ((length texprs) -1)] texprs)
									

onlyCastsIn :: CastsToDo -> CastsToDo
onlyCastsIn trackOfCasts = HM.map (filter onlyComplexFilter) trackOfCasts
						where
						onlyComplexFilter = (\pair -> case pair of 
								(n, (Constructor cdef' otherTexprs)) -> checkComplex (last otherTexprs)
								otherwise -> False)
						checkComplex = (\entry -> case entry of 
								(Constructor cdef' otherTexprs) -> True
								otherwise -> False)

createRules :: String -> [Clause] -> CastsToDo -> [Rule]
createRules pred clauses trackOfCasts = (map (createRule pred trackOfCasts) clauses)

createRule :: String -> CastsToDo -> Clause -> Rule 
createRule pred trackOfCasts (Clause c texprs) = (Rule (map (createPremise pred trackOfCasts c) numOfArguments) (Formula pred [] ((Term (map toLower c) newvars):conclInps) conclOut))
					where 
					numOfArguments = [1 .. ((length texprs) -1)]
					newvars = map (\n -> (VarT ("E" ++ (show n)))) numOfArguments
					concltypes = (extractType (last texprs))
					(conclInps, conclOut) = splitAt ((length concltypes) -1) concltypes

createPremise :: String -> CastsToDo -> String -> Int -> Premise
createPremise pred trackOfCasts c n = let tmp = HM.lookup c trackOfCasts in 
								case tmp of 
									Just pairs -> (let tmp2 = HM.lookup n (HM.fromList pairs) in 
											case tmp2 of
												Just realtype -> let concltypes = (extractType realtype) in 
													let (conclInps, conclOut) = splitAt ((length concltypes) -1) concltypes in 
														(Formula pred [] ((VarT ("E" ++ (show n))):conclInps) conclOut)
												Nothing -> (Formula pred [] [(VarT ("E" ++ (show n)))] [newvar]))
									Nothing -> (Formula pred [] [(VarT ("E" ++ (show n)))] [newvar])
								where 
								newvar = (VarT (unsafePerformIO gensymTT))

convertType :: TypeExpr -> Term
convertType (Var variable) = (VarT (toUpLowFirst "up" variable))
convertType (Constructor c tss) = (Term c (map convertType tss)) -- it was (map toLower c) instead of c when you targeted lambda-prolog
extractType :: TypeExpr -> [Term]
extractType (Var variable) = [(convertType (Var variable))]
extractType (Constructor c tss) = map convertType (tss)

createSignature :: TypeExpr -> [String] -> SignatureEntry
createSignature cdef signature = (Decl (typecheckPrefix ++ expre) "o" (expre:signature))
								where
								expre = (principalType cdef)