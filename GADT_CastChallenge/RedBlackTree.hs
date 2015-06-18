{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

module RedBlackTree where

import Data.Typeable

-- Original, simple version:
-- data RBT a = E | N Color (RBT a) a (RBT a)

-- GADT
--------------------------------------------------------------------------------

data Color = Red | Black deriving (Eq, Show)

data RBT a where
  Root :: (CT n Black a) -> RBT a

-- A singleton type for colors.
data SColor (c :: Color) where
  R :: SColor Red
  B :: SColor Black

data CT (n :: Nat) (c :: Color) a where
  E  :: CT (S Z) Black a
  N  :: Valid c c1 c2 => SColor c
     -> (CT n c1 a) -> a -> (CT n c2 a)
     -> CT (Incr c n) c a

class Valid (c :: Color)
            (c1 :: Color)
            (c2 :: Color) where
instance Valid Red Black Black
instance Valid Black c1 c2

data Nat = Z | S Nat

type family Incr (c :: Color) (n :: Nat)
             :: Nat
type instance Incr Black n = S n
type instance Incr Red   n = n

--------------------------------------------------------------------------------
-- Ghostbuster:

-- SColor: strip c, synthesized
-- CT: strip n,c; both synth

-- Ambiguity analysis:
--   E: n,c are constant
--   N: c is determined by field1, n is determined by both sub-trees

--------------------------------------------------------------------------------
-- Stripped ADT
--------------------------------------------------------------------------------

data SColor'  where
  R' :: SColor'
  B' :: SColor'

-- data RBT' where Root :: (CT n Black a) -> RBT'

data CT' a where
  E'  :: CT' a
  N'  :: -- Valid' c c1 c2 -> -- ????
         SColor'
      -> (CT' a) -> a -> (CT' a)
      -> CT' a

data Valid' -- ??

downSColor :: SColor c -> SColor'
downSColor R = R'
downSColor B = B'

downCT :: CT c n a  -> CT' a
downCT E = E'
downCT (N c l a r) =
  N' (downSColor c) (downCT l) a (downCT r)

data SealedCT a =
     forall n c . SealedCT (CT n c a)

data SealedSColor =
     forall c . SealedSColor (SColor c)

-- If our translation were smart, we could take this out of Maybe:
upSColor :: SColor' -> Maybe SealedSColor
upSColor R' = Just $ SealedSColor R
upSColor B' = Just $ SealedSColor B

upCT :: forall a . CT' a -> Maybe (SealedCT a)
upCT E' = Just $ SealedCT E
upCT (N' c l a r) =
  do SealedSColor (c' :: SColor c') <- upSColor c
     SealedCT (l' :: CT ln lc a) <- upCT l
     SealedCT (r' :: CT rn rc a) <- upCT r

     -- FINISHME: we need eqT for the new kinds:
     -- Refl <- eqT (unused::ln) (unused::rn)
     let n :: CT (Incr c' ln) c' a
         n = undefined -- (N c' l' a r')
     return $ SealedCT undefined

unused = error "this is never used"
