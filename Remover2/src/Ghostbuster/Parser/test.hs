{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
module Ghostbuster where
import Prelude hiding (Int, Maybe(..), Bool(..))
-- for the Ghostbust data type that we use in the annotations
import Ghostbuster.Parser.Prog

{-# ANN Var (Ghostbust [] [env] [arg]) #-}
data Var env arg where
  Zro :: Var (e,a) a  -- This requires role nominal for the environment param.
  Suc :: Var e a -> Var (e,b) a -- So does this

{-# ANN Exp (Ghostbust [] [env] [arg]) #-}
data Exp env arg where
  Con :: Int -> Exp e Int
  Add :: Exp e Int -> Exp e Int -> Exp e Int
  Mul :: Exp e Int -> Exp e Int -> Exp e Int
  Var :: Var e a -> Exp e a
  Abs :: Typ a -> Exp (e,a) b -> Exp e (a -> b)
  App :: Exp e (a -> b) -> Exp e a -> Exp e b

{-# ANN Typ (Ghostbust [] [] [arg]) #-}
data Typ arg where
  Int :: Typ Int
  Arr :: Typ a -> Typ b -> Typ (a -> b)
