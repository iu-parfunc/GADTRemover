{-# LANGUAGE GADTs     #-}
{-# LANGUAGE MagicHash #-}

import Ghostbuster
import Data.Word
import qualified GHC.Exts

-- {-# ANN HashMap (Ghostbust [k,v] [] []) #-}
-- | A map from keys to values.  A map cannot contain duplicate keys;
-- each key can map to at most one value.
data HashMap k v
    = Empty
    | BitmapIndexed !Bitmap !(Array (HashMap k v))
    | Leaf !Hash !(Leaf k v)
    | Full !(Array (HashMap k v))
    | Collision !Hash !(Array (Leaf k v))

-- {-# ANN Leaf (Ghostbust [] [] [k,v]) #-}
data Leaf k v = L !k v

-- {-# ANN Array (Ghostbust [] [] [a]) #-}
data Array a = Array
    { unArray :: !(Array# a)
    , length  :: !Int
    }

type Hash   = Word
type Bitmap = Word
-- data Hash
-- data Bitmap

-- GHC.Exts
-- data Array# a
type Array# a = GHC.Exts.Array# a

