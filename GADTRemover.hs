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
fromGDTAtoAll (DataType cdef clauses) = 
						(case cdef of 
						 (Constructor c args) -> (adt, ts, trackOfCasts)
						 	where
						 	adt = (DataType (Constructor c []) clauses')
						 	clauses' = map (stripArgs c) clauses
						 	allMappings = getCasts c clauses
							trackOfCasts = onlyCastsIn allMappings
						 	ts = createTypeSystem clauses allMappings)
						
stripArgs :: String -> Clause -> Clause
stripArgs cdef (Clause c texprs) = (Clause c (map (stripArgs_TE cdef) texprs))

stripArgs_TE :: String -> TypeExpr -> TypeExpr
stripArgs_TE cdef (Constructor c texpr) = if c == cdef then (Constructor c []) else (Constructor c texpr)

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

createTypeSystem :: [Clause] -> CastsToDo -> TypeSystem
createTypeSystem clauses trackOfCasts = (Ts (map (createRule trackOfCasts) clauses))

createRule :: CastsToDo -> Clause -> Rule 
createRule trackOfCasts (Clause c texprs) = (Rule (map (createPremise trackOfCasts c) numOfArguments) (Term c newvars) (extractType (last texprs)))
					where 
					numOfArguments = [1 .. ((length texprs) -1)]
					newvars = map (\n -> (VarT ("E" ++ (show n)))) numOfArguments

createPremise :: CastsToDo -> String -> Int -> Premise
createPremise trackOfCasts c n = let tmp = HM.lookup c trackOfCasts in 
								case tmp of 
									Just pairs -> (let tmp2 = HM.lookup n (HM.fromList pairs) in 
											case tmp2 of
												Just realtype -> (Formula "typeOf" [] [(VarT ("E" ++ (show n)))] [(extractType realtype)])
												Nothing -> (Formula "typeOf" [] [(VarT ("E" ++ (show n)))] [newvar]))
									Nothing -> (Formula "typeOf" [] [(VarT ("E" ++ (show n)))] [newvar])
								where 
								newvar = (VarT (unsafePerformIO gensymTT))
								

convertType :: TypeExpr -> Term
convertType (Var string) = (VarT (map toUpper string))
convertType (Constructor c tss) = (Term (map toLower c) (map convertType tss))

extractType :: TypeExpr -> Term
extractType (Var string) = (VarT (map toUpper string))
extractType (Constructor c tss) = convertType (last tss)


{-
getCasts_TE c cdef texprs)

getCasts_TE :: String -> String -> [TypeExpr] -> CastsToDo
getCasts_TE c cdef [] = HM.empty
getCasts_TE c cdef (texpr:rest) = (case texpr of
(Constructor f texprs) -> HM.unionWith (++) currentCast (getCasts_TE c cdef rest)
where
currentCast = if (f == cdef) then (HM.insert c castsByPositon HM.empty) else HM.empty
onlyComplexTExprs = filter onlyComplexFilter texprs
castsByPositon = zip [1 .. (length onlyComplexTExprs)] onlyComplexTExprs
onlyComplexFilter = \entry -> case entry of
(Var string) -> False
(Constructor string otherTexpr) -> True)

					-}