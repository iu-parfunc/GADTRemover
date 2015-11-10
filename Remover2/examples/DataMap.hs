
import Ghostbuster.Parser.Prog

-- {-# ANN Map (Ghostbust [] [k,v] []) #-}
-- data Map k v where
--   Bin :: Size -> k -> a -> (Map k a) -> (Map k a) -> Map k a
--   Tip :: Map k a

{-# ANN Map (Ghostbust [] [k,a] []) #-}
data Map k a  = Bin {-# UNPACK #-} !Size !k a !(Map k a) !(Map k a)
              | Tip

-- type Size     = Int

data Size = Size Int


type Foo = Int

x = "hello"
