{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs         #-}

-- | Handwritten version of the feldspar ADT, copied from:
--     https://github.com/shayan-najd/MiniFeldspar/

module Feldspar.ADT1 where

import Control.DeepSeq
import GHC.Generics
import Prelude

-- ADT representation.
-- Simply-typed lambda calculus with de Bruijn indices,
-- with integer constants, and addition.
-- Philip Wadler and Shayan Najd, November 2013

-- import ErrorMonad

{--
data Exp
  = Con Int
  | Var Var
  | Abs Typ Exp
  | App Exp Exp
  | Add Exp Exp
  deriving (Eq, Generic)
--}

data Exp where
  Con :: Int -> Exp
  Var :: Var -> Exp
  Abs :: Typ -> Exp -> Exp
  App :: Exp -> Exp -> Exp
  Add :: Exp -> Exp -> Exp
  Mul :: Exp -> Exp -> Exp
  deriving (Eq, Generic)

instance NFData Exp


-- Equality on expressions is always up to alpha equivalence
-- (thanks to Debruijn indices)

-- Variables are represented as natural numbers
data Var
  = Zro
  | Suc Var
  deriving (Eq, Generic)

instance Show Var where
  show = show . natToInt

instance NFData Var

natToInt :: Var -> Int
natToInt Zro     = 0
natToInt (Suc n) = (natToInt n) + 1


-- Types
data Typ
  = Int
  | Arr Typ Typ
  deriving (Eq, Generic)

instance NFData Typ

-- Equality between types
(===) :: Typ -> Typ -> Eval ()
Int         === Int           = return ()
(Arr t1 t2) === (Arr t1' t2') = do t1 === t1'
                                   t2 === t2'
_           === _             = throwError "Type Error!"

-- Extraction of values form environment
get :: Var -> [a] -> Eval a
get Zro     (x:_)  = return x
get (Suc n) (_:xs) = get n xs
get _       []     = throwError "Scope Error!"

-- Values
data Val
  = Num Int
  | Fun (Val -> Val)

instance Eq Val where
  Num i == Num j = i == j
  _     == _     = False


-- Application of two values
app :: Val -> Val -> Eval Val
app (Fun f) v  = return (f v)
app _       _  = throwError "Type Error!"

-- Addition of two values
add :: Val -> Val -> Eval Val
add (Num i) (Num j) = return (Num (i + j))
add _       (_    ) = throwError "Type Error!"

-- Multiplication of two values
mul :: Val -> Val -> Eval Val
mul (Num x) (Num y) = return $ Num (x * y)
mul _       _       = throwError "Type Error!"

-- Evaluation of expressions under specific environment of values
run :: Exp -> [Val] -> Eval Val
run (Var x)     env     = get x env
run (Con i)     _       = return $ Num i
run (Abs _ f)   env     = return $ Fun (\v -> either error id (run f (v : env)))
run (App ef ea) env = do vf <- run ef env
                         va <- run ea env
                         vf `app` va
run (Add el er) env = do vl <- run el env
                         vr <- run er env
                         vl `add` vr
run (Mul el er) env = do vl <- run el env
                         vr <- run er env
                         vl `mul` vr

-- Typechecking and returning the type, if successful
chk :: Exp -> [Typ] -> Eval Typ
chk (Con _)     _ = return Int
chk (Var x)     env = get x env
chk (Abs ta eb) env = do tr <- chk eb (ta : env)
                         return (ta `Arr` tr)
chk (App ef ea) env = do ta `Arr` tr <- chk ef env
                         ta'         <- chk ea env
                         ta === ta'
                         return tr
chk (Add el er) env = do tl <- chk el env
                         tr <- chk er env
                         tl === Int
                         tr === Int
                         return Int
chk (Mul el er) env = do tl <- chk el env
                         tr <- chk er env
                         tl === Int
                         tr === Int
                         return Int

-- An example expression doubling the input number
dbl :: Exp
dbl = Abs Int (Var Zro `Add` Var Zro)

-- An example expression composing two types
compose :: Typ -> Typ -> Typ -> Exp
compose s t u = Abs (Arr t u)
                (Abs (Arr s t)
                 (Abs s
                  (Var (Suc (Suc Zro)) `App` (Var (Suc Zro) `App` Var Zro))))

-- An example expression representing the Integer 4
four :: Exp
four = (compose Int Int Int `App` dbl `App` dbl) `App` (Con 1)


-- Two test cases
test :: Bool
test =
  return Int     == chk four [] `catchError` error
  &&
  return (Num 4) == run four [] `catchError` error


--------------------------------------------------------------------------------
-- Helpers for basic error monad

type Eval = Either String

throwError :: String -> Eval a
throwError = Left

catchError :: Eval a -> (String -> Eval a) -> Eval a
catchError (Left err)  handle = handle err
catchError (Right val) _      = Right val

