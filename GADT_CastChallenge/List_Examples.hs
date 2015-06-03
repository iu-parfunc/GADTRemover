{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}

module List_Examples where

import Data.Dynamic
import Data.Typeable
import Text.Printf

-- Version 1: the most basic list example:
--------------------------------------------------------------------------------
data List a = Nil | Cons a (List a)
  deriving (Show,Eq,Read,Ord)

-- Ghostbust List with 'a' in "checked" mode
data List' = Nil' | Cons' Dynamic List'
deriving instance Show List'

strip :: Typeable a => List a -> List'
strip Nil = Nil'
strip (Cons a l) = Cons' (toDyn a) (strip l)

restore :: forall a . Typeable a => List' -> Maybe (List a)
restore Nil' = Just (Nil :: List a)
restore (Cons' d l) =
  case fromDynamic d :: Maybe a of
    Nothing -> Nothing
    Just x  -> do l' <- restore l
                  return $ Cons x l'

-- Version 2:  What about kinds other than '*'
--------------------------------------------------------------------------------

data List2 f = Nil2 | Cons2 (f Int) (List2 f)

deriving instance Show (f Int) => Show (List2 f)

-- Ghostbust List with 'a' in "checked" mode
data List2' = Nil2' | Cons2' Dynamic List2'

strip2 :: Typeable f => List2 f -> List2'
strip2 Nil2 = Nil2'
strip2 (Cons2 a l) = Cons2' (toDyn a) (strip2 l)

restore2 :: forall f . Typeable f => List2' -> Maybe (List2 f)
restore2 Nil2' = Just (Nil2 :: List2 f)
restore2 (Cons2' d l) =
  case fromDynamic d :: Maybe (f Int) of
    Nothing -> Nothing
    Just x  -> do l' <- restore2 l
                  return $ Cons2 x l'

data Tup2 x = Tup2 x x
 deriving (Typeable, Show)

test2 :: Maybe (List2 Tup2)
test2 = restore2 (strip2 (Cons2 (Tup2 3 4) Nil2))

-- Version3:
--------------------------------------------------------------------------------

data List3 (f :: * -> *) a where
   Nil3  :: List3 f a
   Cons3 ::  (f a) -> (List3 f a) -> List3 f a
 deriving Show

-- Erase f only, checked:

-- data List3' a = Nil3 | Cons3 (f a) (List3 f a)

--------------------------------------------------------------------------------
typeError :: forall s t a. (Typeable s, Typeable t) => s -> t -> a
typeError _ _
  = error
  $ printf "Couldn't match expected type `%s' with actual type `%s'"
           (show (typeOf (undefined::s)))
           (show (typeOf (undefined::t)))

inconsistent :: String -> a
inconsistent s = error (s ++ ": inconsistent valuation")

-- Gain some type-level knowledge when two value-level types match
--
unify :: (Typeable s, Typeable t) => s -> t -> Maybe (s :~: t)
unify s t =
  case eqT of
    Nothing   -> typeError s t
    refl      -> refl
