{-# OPTIONS_GHC -fdefer-type-errors #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Ghostbuster where
import Prelude hiding (Int, Maybe(..), Bool(..))

data TypeDict a where
        ArrowTyDict :: TypeDict a -> TypeDict b -> TypeDict (ArrowTy a b)
        IntDict :: TypeDict Int

data TyEquality a b where
        Refl :: TyEquality a a

data ArrowTy a b where

data Int where
        One :: Int
        Two :: Int
        Three :: Int
  deriving Show

data Maybe a where
        Just :: a -> Maybe a
        Nothing :: Maybe a

data Bool where
        True :: Bool
        False :: Bool

data Tup2 a b where
        Tup2 :: a -> b -> Tup2 a b

checkTEQ :: TypeDict t -> TypeDict u -> Maybe (TyEquality t u)
checkTEQ x y
  = case x of
        ArrowTyDict a1 b1 -> case y of
                                 ArrowTyDict a2 b2 -> case checkTEQ a1 a2 of
                                                          Just Refl -> case checkTEQ b1 b2 of
                                                                           Just Refl -> Just Refl
                                                                           Nothing -> Nothing
                                                          Nothing -> Nothing
                                 IntDict -> Nothing
        IntDict -> case y of
                       ArrowTyDict a2 b2 -> Nothing
                       IntDict -> Just Refl
ghostbuster
  = (\ ltmp ->
       case ltmp of
           ArrowTyDict a b -> (\ ltmp2 ->
                                 case ltmp2 of
                                     -- IntDict -> One
                                     -- ArrowTyDict a b -> Two
                                     _ -> undefined
                              )
                                a
           -- IntDict -> Three
           _ -> undefined -- Wait ltmp shoudl NOT be ArrowTyDict here but it is!
           )
      (ArrowTyDict IntDict IntDict)
--------------------------------------------------------------------------------
-- Manually trying some alternatives:

ghostbuster2 :: Int
ghostbuster2
  = foo (ArrowTyDict IntDict IntDict)
 where
  -- Uncommenting this type sig givse us errors.
  -- In fact we even hit that error with deferred type error:
  foo :: TypeDict a -> Int
  foo ltmp  = case ltmp of
                  ArrowTyDict a _b -> bar  a
                  IntDict -> Three
  -- RRN: In fact this looks like a type checker bug.
  -- It infers a BOGUS type for foo, and gives an error from it:
  --   foo :: TypeDict t1 -> t


  bar :: TypeDict b -> Int
  bar ltmp2  = case ltmp2 of
                   IntDict -> One
                   ArrowTyDict _a _b -> Two



main :: IO ()
main = putStrLn "Hello"
