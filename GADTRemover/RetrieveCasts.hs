module RetrieveCasts where

import Data.List
import Data.Char
import DataType
import qualified Data.Map as HM
import GADTRemover
import ToHaskell


retrieveCastsIO :: DataType -> IO ()
retrieveCastsIO gadt = putStrLn (retrieveCasts trackOfCasts)
					where 
					trackOfCasts = fromGDTAtoCasts gadt

retrieveCasts :: CastsToDo -> String
retrieveCasts trackOfCasts = concat (map (retrieveCasts_CL trackOfCasts) (HM.keys trackOfCasts))

retrieveCasts_CL :: CastsToDo -> String -> String
retrieveCasts_CL trackOfCasts c = let tmp = HM.lookup c trackOfCasts in 
										case tmp of
										 Just casts -> "Constructor " ++ c ++ " needs the following casts:\n" ++ (concat (map retrieveCasts_PAIRS casts))
										 Nothing -> error "Error, I did not retrieve what you gave me."

retrieveCasts_PAIRS :: (Int, TypeExpr) -> String
retrieveCasts_PAIRS (n, texpr) = "   For argument " ++ (show n) ++ " - cast to" ++ toHaskell_TE texpr ++ "\n"

