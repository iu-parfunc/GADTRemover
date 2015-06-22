-- |

module Ghostbuster.TypeCheck
      (typeExp, typeDef, typeProg) where

import Ghostbuster.Types

-- | Type check a value definition given a set of in-scope data type
-- definitions.
typeDef :: [DDef] -> VDef -> Maybe TypeError
typeDef = undefined

typeExp :: [DDef] -> Exp -> Maybe TypeError
typeExp = undefined

typeProg :: Prog -> Maybe TypeError
typeProg = undefined
