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
dd1 = DDef "Exp" [] [("env",Star)] [("ans",Star)]
      [ KCons "Con" [int]                               ["e1",int]
      , KCons "Add" [ exp ["e2", int]
                    , exp ["e2", int]]                  ["e2",int]
      , KCons "Mul" [ exp ["e3", int]
                    , exp ["e3", int]]                  ["e3",int]
      , KCons "Var" [ ConTy "Var" ["e4","u"]]           ["e4","u"]
      , KCons "Abs" [ ConTy "Typ" ["r"]
                    , exp [tup "e5" "r", "s"]]          ["e5",arr "r" "s"]
      , KCons "App" [ exp ["e6", arr "x" "y"]
                    , exp ["e6", "x"]]                  ["e6","y"]
      ]
  where
  exp ts = ConTy "Exp" ts

tup :: MonoTy -> MonoTy -> MonoTy
tup a b = ConTy "Tup2" [a,b]

arr :: MonoTy -> MonoTy -> MonoTy
arr = ArrowTy

int :: MonoTy
int = ConTy "Int" []

-- | Var is also ghostbusted with e=checked, a=synth:
dd2 :: DDef
dd2 = DDef "Var" [] [("env",Star)] [("ans",Star)]
      [ KCons "Zro" []                      [tup "e1" "a", "a"]
      , KCons "Suc" [ConTy "Var" ["e2","x"]] [tup "e2" "y", "x"]
      ]

dd3 :: DDef
dd3 = DDef "Typ" [] [] [("arr",Star)]
      [ KCons "Int" []                          [int]
      , KCons "Arr" [ ConTy "Typ" ["v"]
                    , ConTy "Typ" ["w"]]        [arr "v" "w"]
      ]

feldspar_gadt :: [DDef]
feldspar_gadt = [dd3,dd2,dd1]

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
dd1' = DDef "Exp'" [] [] []
       [ KCons "Con'" [int]                     []
       , KCons "Add'" [exp', exp']              []
       , KCons "Mul'" [exp', exp']              []
       , KCons "Var'" [ConTy "Var'" []]         []
       , KCons "Abs'" [ConTy "Typ'" [], exp']   []
       , KCons "App'" [exp', exp']              []
       ]
  where
  exp' = ConTy "Exp'" []


dd2' :: DDef
dd2' = DDef "Var'" [] [] []
       [ KCons "Zro'" []                []
       , KCons "Suc'" [ConTy "Var'" []] []
       ]

dd3' :: DDef
dd3' = DDef "Typ'" [] [] []
       [ KCons "Int'" []                        []
       , KCons "Arr'" [ ConTy "Typ'" []
                      , ConTy "Typ'" []]        []
       ]

feldspar_adt :: [DDef]
feldspar_adt = [dd1',dd2',dd3']

--------------------------------------------------------------------------------

-- Testing: Manually written up-function:

sealedExp :: DDef
sealedExp =
  DDef "SealedExp" [("e",Star)] [] []
    [ KCons "SealedExp"
            [TypeDictTy "a", ConTy "Exp" ["e","a"]]
            ["e"]
    ]

-- Can't get this to typecheck unless we have Int lits:
exp1 :: Exp
exp1 = EApp (EApp (EK "Add") (EApp (EK "Con") (EK "One")))
                             (EApp (EK "Con") (EK "Two"))


mayb :: MonoTy -> MonoTy
mayb a = ConTy "Maybe" [a]

upExp :: VDef
upExp =
     VDef "upExp" (ForAll [("e", Star)] (arr exp' (mayb (ConTy "SealeExp" ["e"])))) $
      ELam ("x", exp') $
       ECase "x" $
        [ (Pat "Add'" ["e1", "e2"]
          ,ECase (EApp "upExp" "e1")
            [ (Pat "SealedExp" ["dict1", "e1'"],
               ECaseDict undefined undefined undefined)
            ]
          )
        ]
 where
   exp' = ConTy "Exp'" []

upTyp :: VDef
upTyp
  = VDef "upTyp" (ForAll [] (ConTy "Typ'" [] `ArrowTy` ConTy "SealedTyp" []))
  $ ELam ("x", ConTy "Typ'" [])
  $ ECase "x"
  [ ( Pat "Int'" []
    , EApp (EK "SealedTyp") (EK "Int")
    )
  , ( Pat "Arr'" ["x1", "x2"]
    , ECase (EApp "upTyp" "x1") [ (Pat "SealedTyp" ["a"],
      ECase (EApp "upTyp" "x2") [ (Pat "SealedTyp" ["b"],
        (EApp "SealedTyp" (EApp (EApp "Arr" "a") "b" )))])]
    )
  ]


-- | Test: run the upExp conversion against the sample value.
upProg :: Prog
upProg
  = Prog [ints, maybeD] [upExp]
  $ VDef "upProg" (ForAll [] (ConTy "Int" [])) (EApp "upExp" exp1)

ex0 :: Val
ex0 = interp
    $ Prog feldspar_gadt []
    $ VDef "ex0" undefined (EK "One")

ex1 :: Val
ex1 = interp
    $ Prog feldspar_gadt []
    $ VDef "ex1" undefined (EApp (EK "Con") (EK "One"))

ex2 :: Val
ex2 = interp
    $ Prog feldspar_gadt []
    $ VDef "ex2" undefined exp1
