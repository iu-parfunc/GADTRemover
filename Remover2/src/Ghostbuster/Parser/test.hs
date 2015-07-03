{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Ghostbuster where
import Prelude hiding (Int, Maybe(..), Bool(..))

-- for the Ghostbust data type that we use in the annotations
import Ghostbuster.Parser.Prog

{-# ANN Foo (Ghostbust [] [a] []) #-}
data Foo a = Nerf | GOOO (Foo a)

data Nat' = Zero | Suc Nat

data Int' = One | Two | Three

data Maybe' a = Just a | Nothing 

data Tup2 a b = Tup2 a b

data Nat where
        Zero :: Nat
        Suc :: Nat -> Nat
        Add :: Nat -> Nat -> Nat
 
data Int where
        One :: Int
        Two :: Int
        Three :: Int
 
data Maybe a where
        Just :: a -> Maybe a
        Nothing :: Maybe a
 
data Bool where
        True :: Bool
        False :: Bool
 
data Tup2 a b where
        Tup2 :: a -> b -> Tup2 a b

{-# ANN Exp (Ghostbust [] [a] []) #-}
data Exp e a where
  Con :: Int -> Exp e Int
  Add :: Exp e Int -> Exp e Int -> Exp e Int
  Mul :: Exp e Int -> Exp e Int -> Exp e Int
  Var :: Var e a -> Exp e a
  Abs :: Typ a -> Exp (e,a) b -> Exp e (a -> b)
  App :: Exp e (a -> b) -> Exp e a -> Exp e b
 
-- myEven :: Nat -> Bool
-- myEven Zero = True
-- myEven (Suc n) = myOdd n
--  
-- myOdd :: Nat -> Bool
-- myOdd Zero = False
-- myOdd (Suc n) = myEven n
-- ghostbuster
--   = myEven
--       (Suc
--          (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))))))
-- main = print (seq ghostbuster ())
