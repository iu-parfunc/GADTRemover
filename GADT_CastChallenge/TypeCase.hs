{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, Rank2Types, MagicHash #-}

-- | Exposes a safe interface for deconstructing typeable *instances*.
--   This module only performs this trick for arrows and 2-tuples, but
--   the Ghostbuster tool will need to generate these for all
--   non-nullary type constructors mentioned in erased types.

module TypeCase
  ( typeCaseArrow
  , TypeCaseArrow(..)
  , typeCaseTuple
  , TypeCaseTuple(..)
  ) where

import Data.Typeable
import TypeableMagic

_main :: IO ()
_main = do
  print (example1 (length :: String -> Int) "abc") -- Just 3
  print (example1 (length :: [Int]  -> Int) "abc") -- Nothing

example1 :: forall arr a. (Typeable arr, Typeable a) => arr -> a -> Maybe Int
example1 arr a = do
  -- Check that "arr" is a function from the type of "a" to Int
  TypeCaseArrow (Refl :: arr :~: (b -> c)) <- typeCaseArrow
  Refl                :: b   :~: a         <- gcast Refl
  Refl                :: c   :~: Int       <- gcast Refl
  return (arr a)

-- | Witness the arrow-ness of a type.
data TypeCaseArrow a where
  TypeCaseArrow :: (Typeable b, Typeable c) =>
                   (a :~: (b -> c)) -> TypeCaseArrow a

-- | Witness the tuple-ness of a type.
data TypeCaseTuple a where
  TypeCaseTuple :: (Typeable b, Typeable c) =>
                   (a :~: (b,c)) -> TypeCaseTuple a

-- | Test a Typeable type to see if it is an arrow.  If so, return a
-- data structure capable of witnessing that fact for the GHC type checker.
typeCaseArrow :: forall arr. (Typeable arr) => Maybe (TypeCaseArrow arr)
typeCaseArrow = case splitTyConApp (typeRep (Proxy :: Proxy arr)) of
  (op, [b,c]) | op == typeRepTyCon (typeRep (Proxy :: Proxy (->)))
              -> recoverTypeable b (\(_ :: Proxy b) ->
                 recoverTypeable c (\(_ :: Proxy c) ->
                 fmap TypeCaseArrow (gcast Refl :: Maybe (arr :~: (b -> c)))))
  _ -> Nothing

-- | Ditto for tuples.
typeCaseTuple :: forall arr. (Typeable arr) => Maybe (TypeCaseTuple arr)
typeCaseTuple = case splitTyConApp (typeRep (Proxy :: Proxy arr)) of
  (op, [b,c]) | op == typeRepTyCon (typeRep (Proxy :: Proxy (->)))
              -> recoverTypeable b (\(_ :: Proxy b) ->
                 recoverTypeable c (\(_ :: Proxy c) ->
                 fmap TypeCaseTuple (gcast Refl :: Maybe (arr :~: (b,c)))))
  _ -> Nothing
