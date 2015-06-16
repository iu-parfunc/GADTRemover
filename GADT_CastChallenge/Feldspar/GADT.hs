{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE RoleAnnotations   #-}
{-# OPTIONS_GHC -Wall #-}

-- | Mini feldspar GADT, copied from:
--     https://github.com/shayan-najd/MiniFeldspar/

module Feldspar.GADT where

import Text.PrettyPrint.Leijen

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
  Mul :: Exp e Int -> Exp e Int -> Exp e Int
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

-- Extraction of values form environment
get :: Var e a -> e -> a
get Zro     (_ ,x)      = x
get (Suc n) (xs,_)      = get n xs

-- Extraction of values form environment with singletons
gets :: Var e a -> Env e -> Typ a
gets Zro     (Ext _  x) = x
gets (Suc n) (Ext xs _) = gets n xs
gets _       Emp        = error "Impossible!"

-- Evaluation of expressions under specific environment of values
run :: Exp e a -> e -> a
run (Con i)     _ = i
run (Var x)     r = get x r
run (Abs _  eb) r = \v -> run eb (r,v)
run (App ef ea) r = run ef r $ run ea r
run (Add el er) r = run el r + run er r
run (Mul el er) r = run el r * run er r

-- Typechecking and returning the type, if successful
chk :: Exp e a -> Env e -> Typ a
chk (Con _)     _ = Int
chk (Var x)     r = gets x r
chk (Abs ta eb) r = ta `Arr` chk eb (r `Ext` ta)
chk (App ef _ ) r = case chk ef r of
                      Arr _ tr -> tr
chk (Add _  _ ) _ = Int
chk (Mul _  _ ) _ = Int

-- An example expression doubling the input number
dbl :: Exp env (Int -> Int)
dbl = Abs Int (Var Zro `Add` Var Zro)

-- An example expression composing two types
compose :: (Elt a, Elt b, Elt c) => Exp env ((b -> c) -> (a -> b) -> (a -> c))
compose
  = Abs eltType
  $ Abs eltType
  $ Abs eltType (Var (Suc (Suc Zro)) `App` (Var (Suc Zro) `App` Var Zro))

-- An example expression representing the Integer 4
four :: Exp () Int
four = (compose `App` dbl `App` dbl) `App` Con 1

-- Two test cases
test :: Bool
test = (case chk four Emp of
          Int -> True)
       &&
       (run four () == 4)


let_ :: Elt a => Exp env a -> Exp (env,a) b -> Exp env b
let_ bnd body = (Abs eltType body) `App` bnd

constant :: Int -> Exp env Int
constant = Con

class Elt a where
  eltType :: Typ a

instance Elt Int where
  eltType = Int

instance (Elt a, Elt b) => Elt (a -> b) where
  eltType = Arr eltType eltType


-- Pretty printer
-- --------------

instance Num (Exp env Int) where
  x + y         = Add x y
  x * y         = Mul x y
  fromInteger   = Con . fromInteger
  --
  (-)           = error "Exp.(-)"
  abs           = error "Exp.abs"
  signum        = error "Exp.signum"

idxToInt :: Var env t -> Int
idxToInt Zro      = 0
idxToInt (Suc ix) = idxToInt ix + 1

prettyOpenExp :: (Doc -> Doc) -> Int -> Exp env a -> Doc
prettyOpenExp wrap lvl = pp
  where
    ppE :: Exp env a -> Doc
    ppE = prettyOpenExp parens lvl

    ppF :: Exp env a -> Doc
    ppF fun =
      let
          (n, body) = count n fun

          count :: Int -> Exp env f -> (Int, Doc)
          count l (Abs _ f) = let (i,b) = count l f in (i+1, b)
          count l other     = (lvl-1, prettyOpenExp id (l+1) other)
      in
      parens $ sep [ char 'λ' <> hsep [ char 'x' <> int idx | idx <- [lvl .. n] ] <+> char '→'
                   , hang 2 body ]

    pp :: Exp env a -> Doc
    pp (Con i)          = int i
    pp (Var ix)         = char 'x' <> int (lvl - idxToInt ix - 1)
    pp (Add x y)        = wrap $ ppE x <+> char '+' <+> ppE y
    pp (Mul x y)        = wrap $ ppE x <+> char '*' <+> ppE y
    pp (App f x)        = wrap $ sep [ ppE f, hang 2 (ppE x) ]
    pp f@Abs{}          = ppF f


prettyType :: Typ a -> Doc
prettyType Int       = text "Int"
prettyType (Arr a b) = parens (prettyType a <+> char '→' <+> prettyType b)

instance Show (Exp env a) where
  show = show . prettyOpenExp id 0

instance Show (Typ a) where
  show = show . prettyType

