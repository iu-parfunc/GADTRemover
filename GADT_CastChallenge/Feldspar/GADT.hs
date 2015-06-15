{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Mini feldspar GADT, copied from:
--     https://github.com/shayan-najd/MiniFeldspar/

module Feldspar.GADT where

-- GADT representation.
-- Simply-typed lambda calculus with de Bruijn indices,
-- with integer constants, and addition.
-- Philip Wadler and Shayan Najd, November 2013

-- ERASER: Exp, e: checked, a: synthesized
-- ERASER: Var, e: checked, a: synthesized
-- ERASER: Typ, a: synthesized

-- Variables
type role Var nominal nominal
data Var e a where
  Zro :: Var (e,a) a  -- This requires role nominal for the environment param.
  Suc :: Var e a -> Var (e,b) a -- So does this

type role Exp nominal nominal
data Exp (e :: *) (a :: *) where
  Con :: Int -> Exp e Int
  Add :: Exp e Int -> Exp e Int -> Exp e Int
  Var :: Var e a -> Exp e a
  Abs :: Typ a -> Exp (e,a) b -> Exp e (a -> b)
  App :: Exp e (a -> b) -> Exp e a -> Exp e b

-- Types (Singleton)
data Typ a where
  Int :: Typ Int
  Arr :: Typ a -> Typ b -> Typ (a -> b)

-- Environment (Singleton)
data Env e where
  Emp :: Env ()
  Ext :: Env e -> Typ a -> Env (e,a)
