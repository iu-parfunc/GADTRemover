{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, Rank2Types, MagicHash #-}

module TypeCase where

import Data.Typeable
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace
import GHC.Prim (Proxy#)

pr1 :: (Int,Int)
pr1 = (1,2)

pr2 :: (String, String)
pr2 = ("hello","world")

main :: IO ()
main = do
  print (example1 (length :: String -> Int)    "abc")         -- Just 3
  print (example1 (length :: [Int]  -> Int)    "abc")         -- Nothing
  print (example1 (length :: [Int]  -> Int)    ([] :: [Int])) -- Just 0
  print (example2 pr1 (1  :: Int)    (2   :: Int))            -- Just (1,2)
  print (example2 pr1 ("" :: String) (2   :: Int))            -- Nothing
  print (example2 pr2 (4  :: Int)    (2   :: Int))            -- Nothing
  print (example2 pr2 ("" :: String) (""  :: String))         -- Just ("hello", "world")

example1 :: forall arr a. (Typeable arr, Typeable a) => arr -> a -> Maybe Int
example1 arr a = do
  -- Check that "arr" is a function from the type of "a" to Int
  TypeCaseArrow (Refl :: arr :~: (b -> c)) <- typeCaseArrow
  Refl                :: b   :~: a         <- gcast Refl
  Refl                :: c   :~: Int       <- gcast Refl
  return (arr a)

data TypeCaseArrow a where
  TypeCaseArrow :: (Typeable b, Typeable c) =>
                   (a :~: (b -> c)) -> TypeCaseArrow a

typeCaseArrow :: forall arr. (Typeable arr) => Maybe (TypeCaseArrow arr)
typeCaseArrow = case splitTyConApp (typeRep (Proxy :: Proxy arr)) of
  (op, [b,c]) | op == typeRepTyCon (typeRep (Proxy :: Proxy (->)))
              -> unsafeTypeable b (\(_ :: Proxy b) ->
                 unsafeTypeable c (\(_ :: Proxy c) ->
                 fmap TypeCaseArrow (gcast Refl :: Maybe (arr :~: (b -> c)))))
  _ -> Nothing

-- Pairs
example2 :: forall arr a b. (Typeable arr, Typeable a, Typeable b) => arr -> a -> b -> Maybe (a , b)
example2 arr a b = do
  -- Check that "arr" is a pair
  -- TZ: The kinding here is kinda weird: arr needs to be of kind * but we
  -- really want to say that arr :~: (,) which would mean that arr has kind
  -- * -> * -> *. I don't see a way (currently) to get around this, so we can't actually apply 'arr' to anything in the end
  TypeCasePair (Refl :: arr :~: (c1 , c2)) <- typeCasePair -- Would seem to be that we would like to do:
  Refl                :: c1   :~: a        <- gcast Refl
  Refl                :: c2   :~: b        <- gcast Refl
  return arr

data TypeCasePair a where
  TypeCasePair :: (Typeable b, Typeable c) =>
                   (a :~: (b , c)) -> TypeCasePair a

typeCasePair :: forall arr. (Typeable arr) => Maybe (TypeCasePair arr)
typeCasePair = case splitTyConApp (typeRep (Proxy :: Proxy arr)) of
  (op, [b,c]) | op == typeRepTyCon (typeRep (Proxy :: Proxy (,)))
              -> unsafeTypeable b (\(_ :: Proxy b) ->
                 unsafeTypeable c (\(_ :: Proxy c) ->
                 fmap TypeCasePair (gcast Refl :: Maybe (arr :~: (b , c)))))
  _ -> Nothing

newtype Magic ans = Magic (forall a. (Typeable a) => Proxy a -> ans)
newtype Voodoo = Voodoo (forall a. Proxy# a -> TypeRep)

unsafeTypeable :: TypeRep -> (forall a. (Typeable a) => Proxy a -> ans) -> ans
unsafeTypeable rep f = unsafeCoerce (Magic f) (Voodoo (\_ -> rep)) Proxy






-- Add :: Exp e Int -> Exp e Int -> Exp e Int
-- Sum :: [Exp e Int] -> Exp e Int
-- Lit :: Integer -> Exp e Int
-- HO  :: (Exp e Int -> Exp e Int) -> Exp e Int

