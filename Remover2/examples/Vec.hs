{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

-- A test for ghostbusting length-indexed lists down to (essentially)
-- regular lists. Common example in the Ornaments work.

import Ghostbuster

-- We can't handle promoted kinds, at least in the parser.
--
-- data Nat = Z | S Nat

-- data Vec a (n :: Nat) where
--   Nil  :: Vec a 'Z
--   Cons :: a -> Vec a n -> Vec a ('S n)

data Z
data S n

{-# ANN Vec (Ghostbust [a] [] [n]) #-}
data Vec a n where
  Nil  :: Vec a Z
  Cons :: a -> Vec a n -> Vec a (S n)


