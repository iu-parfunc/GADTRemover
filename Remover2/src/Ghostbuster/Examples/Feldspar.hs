{-# LANGUAGE OverloadedStrings #-}

-- | The mini-feldspar language

module Ghostbuster.Examples.Feldspar where

import Ghostbuster.Interp
import Ghostbuster.Types
import Prelude hiding (exp)

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
      [ KCons "Con" [int]                               [exp ["e",int]]
      , KCons "Add" [ exp ["e", int]
                    , exp ["e", int]]                   [exp ["e",int]]
      , KCons "Mul" [ exp ["e", int]
                    , exp ["e", int]]                   [exp ["e",int]]
      , KCons "Var" [ ConTy "Var" ["e","a"]]            [exp ["e","a"]]
      , KCons "Abs" [ ConTy "Typ" ["a"]
                    , exp [tup2 "e" "a", "b"]]          [exp ["e",arr "a" "b"]]
      , KCons "App" [ exp ["e", arr "a" "b"]
                    , exp ["e", "a"]]                   [exp ["e","b"]]
      ]
  where
  exp ts = ConTy "Exp" ts

tup2 :: MonoTy -> MonoTy -> MonoTy
tup2 a b = TupleTy [a,b]

arr :: MonoTy -> MonoTy -> MonoTy
arr = ArrowTy

int :: MonoTy
int = ConTy "Int" []

-- | Var is also ghostbusted with e=checked, a=synth:
dd2 :: DDef
dd2 = DDef "Var" [] [("e",Star)] [("a",Star)]
      [ KCons "Zro" []                      [ConTy "Var" ["e","a"]]
      , KCons "Suc" [ConTy "Var" ["e","a"]] [ConTy "Var" [tup2 "e" "b", "a"]]
      ]

dd3 :: DDef
dd3 = DDef "Typ" [] [] [("a",Star)]
      [ KCons "Int" []                          [ConTy "Typ" [int]]
      , KCons "Arr" [ ConTy "Typ" ["a"]
                    , ConTy "Typ" ["b"]]        [ConTy "Typ" [arr "a" "b"]]
      ]

feldspar_gadt :: [DDef]
feldspar_gadt = [ints,dd1,dd2,dd3]

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
            [ KCons "SealeExp" [(TypeDictTy "a"), ConTy "Exp" ["e","a"]] ["e"] ]

-- Can't get this to typecheck unless we have Int lits:
exp1 :: Exp
exp1 = EApp (EApp (EK "Add") (EApp (EK "Con") (EK "One")))
                             (EApp (EK "Con") (EK "Two"))


mayb :: MonoTy -> MonoTy
mayb a = ConTy "Maybe" [a]

upExp :: VDef
upExp =
     VDef "upExp" (ForAll [] (arr exp' (mayb (ConTy "SealeExp" ["e"])))) $
      ELam ("x", exp') $
       ECase "x" $
        [ (Pat "Add'" ["e1", "e2"],
           ECase (EApp "upExp" "e1")
            [ (Pat "SealedExp" ["dict1", "e1'"],
               ECaseDict undefined undefined undefined)
            ])
        ]
 where
   exp' = ConTy "Exp'" []


-- | Test: run the upExp conversion against the sample value.
upProg :: Prog
upProg = Prog [ints, maybeD] [upExp]
         (EApp "upExp" exp1)

ex0 :: Val
ex0 = interp $ Prog feldspar_gadt [] (EK "One")

ex1 :: Val
ex1 = interp $ Prog feldspar_gadt [] (EApp (EK "Con") (EK "One"))

ex2 :: Val
ex2 = interp $ Prog feldspar_gadt [] exp1
