-- |

module Ghostbuster.Ambiguity where

import Ghostbuster.Types


-- | Do a set of data type definitions, with their
-- keep/check/synthesize specifications meet the ambiguity
-- requirements?
ambCheck :: [DDef] -> Either TypeError ()
ambCheck = undefined
