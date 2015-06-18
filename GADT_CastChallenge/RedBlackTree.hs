{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

module RedBlackTree where

-- import Data.Typeable
import GHC.Prim (Constraint)

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

deriving instance Show (SColor c)

data CT (n :: Nat) (c :: Color) a where
  E  :: CT (S Z) Black a
  N  :: Valid c c1 c2 => SColor c
     -> (CT n c1 a) -> a -> (CT n c2 a)
     -> CT (Incr c n) c a

deriving instance Show a => Show (CT n c a)

class Valid (c :: Color)
            (c1 :: Color)
            (c2 :: Color) where
instance Valid Red Black Black
instance Valid Black c1 c2

data Nat = Z | S Nat

-- Count the number of blacks:
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
 deriving Show

-- data RBT' where Root :: (CT n Black a) -> RBT'

data CT' a where
  E'  :: CT' a
  N'  :: -- Valid' c c1 c2 -> -- ????
         SColor'
      -> (CT' a) -> a -> (CT' a)
      -> CT' a
 deriving Show

data Valid' -- ??

downSColor :: SColor c -> SColor'
downSColor R = R'
downSColor B = B'

downCT :: CT c n a  -> CT' a
downCT E = E'
downCT (N c l a r) =
  N' (downSColor c) (downCT l) a (downCT r)

data SealedCT a =
     forall n c . SealedCT (NatDict n) (SColor c) (CT n c a)

deriving instance Show a => Show (SealedCT a)

data SealedSColor =
     forall c . SealedSColor (SColor c)

-- If our translation were smart, we could take this out of Maybe:
upSColor :: SColor' -> Maybe SealedSColor
upSColor R' = Just $ SealedSColor R
upSColor B' = Just $ SealedSColor B

upCT :: forall a . CT' a -> Maybe (SealedCT a)
upCT E' = Just $ SealedCT (SD ZD) B E
upCT (N' c l a r) =
  do SealedSColor (c' :: SColor c') <- upSColor c
     SealedCT lndict c1 (l' :: CT ln lc a) <- upCT l
     SealedCT rndict c2 (r' :: CT rn rc a) <- upCT r

     -- We need an eqT analog for the new kinds:
     ReflNat <- eqNat lndict rndict

     -- Finally must prove that Valid c c1 c2:
     case testValid c' c1 c2 of
       Nothing -> Nothing
       Just ReifyDict ->
         do let n :: CT (Incr c' ln) c' a
                n = (N c' l' a r')
            return $ SealedCT (incrDict c' lndict) c' n

unused :: t
unused = error "this is never used"

data NatEq :: Nat -> Nat -> * where
 ReflNat :: NatEq a a

-- Singleton:
data NatDict (m :: Nat) where
  ZD :: NatDict Z
  SD :: NatDict n -> NatDict (S n)

deriving instance Show (NatDict m)

incrDict :: SColor c -> NatDict n -> NatDict (Incr c n)
incrDict B nd = SD nd
incrDict R nd = nd

eqNat :: NatDict m -> NatDict n -> Maybe (NatEq m n)
eqNat ZD ZD = Just ReflNat
eqNat (SD n) (SD m) =
  case eqNat n m of
    Nothing -> Nothing
    Just ReflNat -> Just ReflNat
eqNat _ _ = Nothing

testValid :: SColor c -> SColor c1 -> SColor c2 ->
             Maybe (ReifyDict (Valid c c1 c2))
testValid R B B = Just $ ReifyDict
testValid B _ _ = Just $ ReifyDict
testValid _ _ _ = Nothing

data ReifyDict (c::Constraint) where
   ReifyDict :: c => ReifyDict c

--------------------------------------------------------------------------------
-- A version without the Valid type class:

-- Hopefully the ghostbuster approach will work directly on this one:
data CT2 (n :: Nat) (c :: Color) a where
  E2  :: CT2 (S Z) Black a
  NR2 :: SColor Red
      -> (CT2 n Black a) -> a -> (CT2 n Black a)
      -> CT2 (Incr c n) c a
  NB2 :: SColor Black
      -> (CT2 n c1 a) -> a -> (CT2 n c2 a)
      -> CT2 (Incr c n) c a

--------------------------------------------------------------------------------

ct1 :: CT (S Z) Black Int
ct1 = E

ct2 :: CT (S Z) Red Int
ct2 = N R ct1 33 ct1

ct2' :: CT' Int
ct2' = downCT ct2

ct3 :: CT (S (S Z)) Black Int
ct3 = N B ct2 44 ct1

ct3' :: CT' Int
ct3' = downCT ct3

ct3'' :: Maybe (SealedCT Int)
ct3'' = upCT ct3'
