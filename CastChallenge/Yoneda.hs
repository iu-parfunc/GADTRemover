{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE Rank2Types     #-}

-- http://www.haskellforall.com/2012/06/gadts.html
--

module Yoneda where

-- The standard example of type-indexed lists using GADTs
-- ------------------------------------------------------

-- data Nat = Z | S Nat

-- TLM: Can't use the definition of Nat above, because we will require the
--      _types_ Z and S in the ADT version below.
--
data Z
data S n

data SNat n where
  Zero :: SNat Z
  Succ :: SNat n -> SNat (S n)

data List a n where
  Nil  :: List a Z
  Cons :: a -> List a n -> List a (S n)

instance Show a => Show (List a n) where
  show Nil         = "Nil"
  show (Cons x xs) = "Cons " ++ show x ++ " (" ++ show xs ++ ")"

instance Functor (List a)       -- TLM: makes no sense!

vhead :: List a (S n) -> a
vhead (Cons x _) = x


-- Encoding to ADTs using the Yoneda Lemma
-- ---------------------------------------

-- The Yoneda lemma from category theory provides the following trick to convert
-- a GADT to an ordinary data type. Namely, it says that if 'f' is a functor,
-- than the following two types are isomorphic:
--
--   forall b. (a -> b) -> f b   ~   f a
--
-- Which means we can define the following two functions to convert back and
-- forth between the two types:
--
fw :: Functor f => (forall b. (a -> b) -> f b) -> f a
fw f = f id

bw :: Functor f => f a -> (forall b. (a -> b) -> f b)
bw x f = fmap f x


-- TLM: Note the slight-of-hand here. We must make 'n' the final parameter so
--      that we can write a Functor instance. Can we extend this to more
--      parameters?
--
data List' a n
  = Nil' (Z -> n)
  | forall m. Cons' a (List' a m) (S m -> n)

instance Show a => Show (List' a n) where
  show (Nil' _)       = "Nil'"
  show (Cons' x xs _) = "Cons' " ++ show x ++ " (" ++ show xs ++ ")"

instance Functor (List' a) where
  fmap f (Nil' k)       = Nil' (f . k)
  fmap f (Cons' x xs k) = Cons' x xs (f . k)


-- Conversion
-- ----------

down :: List a n -> List' a n
down Nil         = fw Nil'
down (Cons x xs) = fw (Cons' x (down xs))

up :: List' a n -> List a n
up (Nil' k)       = bw Nil k
up (Cons' x xs k) = bw (Cons x (up xs)) k


-- Tests
-- -----

p0 :: List Int (S (S (S Z)))
p0 = Cons 1 (Cons 2 (Cons 3 Nil))

