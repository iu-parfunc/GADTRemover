{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, Rank2Types, MagicHash #-}

module TypeCase where

import Data.Typeable
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace
import GHC.Prim (Proxy#)

main :: IO ()
main = do
  print (example1 (length :: String -> Int) "abc") -- Just 3
  print (example1 (length :: [Int]  -> Int) "abc") -- Nothing

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

newtype Magic ans = Magic (forall a. (Typeable a) => Proxy a -> ans)
newtype Voodoo = Voodoo (forall a. Proxy# a -> TypeRep)

unsafeTypeable :: TypeRep -> (forall a. (Typeable a) => Proxy a -> ans) -> ans
unsafeTypeable rep f = unsafeCoerce (Magic f) (Voodoo (\_ -> rep)) Proxy






-- Add :: Exp e Int -> Exp e Int -> Exp e Int
-- Sum :: [Exp e Int] -> Exp e Int
-- Lit :: Integer -> Exp e Int
-- HO  :: (Exp e Int -> Exp e Int) -> Exp e Int
