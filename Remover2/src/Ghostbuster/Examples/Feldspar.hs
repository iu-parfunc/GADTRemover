{-# LANGUAGE OverloadedStrings #-}

-- | The mini-feldspar language

module Ghostbuster.Examples.Feldspar where

import Ghostbuster.Types
import           Prelude hiding (exp)


{-
data Exp (e :: *) (a :: *) where
  Con :: Int -> Exp e Int
  Add :: Exp e Int -> Exp e Int -> Exp e Int
  Mul :: Exp e Int -> Exp e Int -> Exp e Int
  Var :: Var e a -> Exp e a
  Abs :: Typ a -> Exp (e,a) b -> Exp e (a -> b)
  App :: Exp e (a -> b) -> Exp e a -> Exp e b
-}
dd1 :: DDef
dd1 = DDef "Exp" [] [("e",Star)] [("a",Star)]
      [ KCons "Con" [int]                          ["e",int]
      , KCons "Add" [exp "e" int, exp "e" int]     ["e",int]
      , KCons "Mul" [exp "e" int, exp "e" int]     ["e",int]
      , KCons "Var" [ConTy "Var" ["e","a"]]        ["e","a"]
      , KCons "Abs" [ConTy "Typ" ["a"], exp (tup "e" "a") "b"]
                                                   (["e",arr "a" "b"])
      , KCons "App" [exp "e" (arr "a" "b"), exp "e" "a"]
                                                   (["e","b"])
      ]
  where
  exp a b = ConTy "Exp"   [a,b]

tup :: MonoTy -> MonoTy -> MonoTy
tup a b = ConTy ","  [a,b]

arr :: MonoTy -> MonoTy -> MonoTy
arr a b = ConTy "->" [a,b]

int :: MonoTy
int = ConTy "Int" []

-- | Var is also ghostbusted with e=checked, a=synth:
dd2 :: DDef
dd2 = DDef "Var" [] [("e",Star)] [("a",Star)]
      [ KCons "Zro" [] (["e","a"])
      , KCons "Suc" [ConTy "Var" ["e","a"]] ([tup "e" "b", "a"])
      ]

dd3 :: DDef
dd3 = DDef "Typ" [] [] [("a",Star)]
      [ KCons "Int" [] ([int])
      , KCons "Arr" [ConTy "Typ" ["a"], ConTy "Typ" ["b"]]
                    ([arr "a" "b"])
      ]

feldspar :: [DDef]
feldspar = [dd1,dd2,dd3]
