module ToHaskell where

import Data.List
import Data.Char
import DataType
import GADTRemover

toHaskellIO :: DataType -> IO ()
toHaskellIO gadt = putStrLn (toHaskell gadt)

toHaskell :: DataType -> String
toHaskell (DataType txpr signature clauses) = "Data " ++ toHaskell_TE txpr ++ " where\n" ++ (concat (map toHaskell_CL clauses))

toHaskell_CL :: Clause -> String
toHaskell_CL (Clause c texprs) = "    " ++ c ++ " :: " ++ texprsAddedArrows ++ "\n"
			where
			texprsAddedArrows = intercalate " -> " (map toHaskell_TE texprs)

toHaskell_TE :: TypeExpr -> String
toHaskell_TE (Var variable) = " " ++ variable
toHaskell_TE (Constructor c texprs) =  if (null texprs) then " " ++ c else " (" ++ c ++ (concat (map toHaskell_TE texprs)) ++ ")"

