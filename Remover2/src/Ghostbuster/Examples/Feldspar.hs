{-# LANGUAGE OverloadedStrings #-}

-- | The mini-feldspar language

module Ghostbuster.Examples.Feldspar where

import Ghostbuster.Types
import           Prelude hiding (exp)
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)


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

feldspar_gadt :: [DDef]
feldspar_gadt = [dd1,dd2,dd3]

--------------------------------------------------------------------------------

-- And here's a manual version of the ghostbusted types:

-- data Exp where
--   Con :: Int -> Exp
--   Add :: Exp -> Exp -> Exp
--   Mul :: Exp -> Exp -> Exp
--   Var :: Var -> Exp
--   Abs :: Typ -> Exp -> Exp
--   App :: Exp -> Exp -> Exp
--  deriving (Show, Generic)

dd1' :: DDef
dd1' = DDef "Exp" [] [] []
       [ KCons "Con'" [int]            []
       , KCons "Add'" [exp', exp']     []
       , KCons "Mul'" [exp', exp']     []
       , KCons "Var'" [ConTy "Var'" []]       []
       , KCons "Abs'" [ConTy "Typ'" [], exp'] []
       , KCons "App'" [exp', exp'] []
       ]
  where
  exp' = ConTy "Exp'" []


dd2' :: DDef
dd2' = DDef "Var'" [] [] []
       [ KCons "Zro'" [] []
       , KCons "Suc'" [ConTy "Var'" []] []
       ]

dd3' :: DDef
dd3' = DDef "Typ'" [] [] []
       [ KCons "Int'" [] []
       , KCons "Arr'" [ConTy "Typ'" [], ConTy "Typ'" []] []
       ]

feldspar_adt :: [DDef]
feldspar_adt = [dd1',dd2',dd3']

--------------------------------------------------------------------------------

-- Testing: Manually written up-function:

sealedExp :: DDef
sealedExp = DDef "SealeExp" [("e",Star)] [] []
            [ KCons "SealeExp" [(TypeDict "a"), ConTy "Exp" ["e","a"]] ["e"] ]

-- Oops, can't get this to typecheck unless we have Int lits:
exp1 :: Exp
exp1 = EApp (EApp (EK "Add") (EApp (EK "Con") "1")) (EApp (EK "Con") "2")

upExp :: VDef
upExp = VDef "upExp" (ForAll [] (arr exp' (mayb (ConTy "SealeExp" ["e"])))) $
        ELam ("x", exp') $
          ECase "x" $
           [ (Pat "Add'" ["e1", "e2"],
              ECase (EApp "upExp" "e1")
               [ (Pat "SealedExp" ["dict1", "e1'"],
                  ECaseDict undefined undefined)
               ])
           ]
 where
   exp' = ConTy "Exp'" []
   exp  = ConTy "Exp" []



mayb :: MonoTy -> MonoTy
mayb a = ConTy "Maybe" [a]
