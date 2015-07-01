{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp  #-}

-- | Very small example programs for testing purposes.

module Ghostbuster.Examples.Tiny where

import Ghostbuster.Types
import Ghostbuster.Utils

--------------------------------------------------------------------------------
-- Just expressions:

e02 :: Exp
e02 = (ECase (EK "One") [(Pat "One" [], EK "Two")])

v02 :: VDef
v02 = VDef "e02" (ForAll [] "Int") e02

e03 :: Exp
e03 = EDict ("Int")

v03 :: VDef
v03 = VDef "e03" (ForAll [] (ConTy "TypeDict" ["Int"])) e03

-- | Construct arrow dictionary
e04 :: Exp
e04 = EApp (EApp (EDict ("ArrowTy")) e03) e03

v04 :: VDef
v04 = VDef "e04" (ForAll [] (ConTy "TypeDict" [ConTy "ArrowTy" ["Int", "Int"]])) e04

e05 :: Exp
e05 = ECaseDict e04
       ("ArrowTy",["a","b"],
        ECaseDict "a" ("Int", [], EK "One")
                  (EK "Two")
       ) (EK "Three")

v05 :: VDef
v05 = VDef "e05" (ForAll [] "Int") e05

-- | Perform a BAD caseDict to take a false branch.  Returns "Three"
e06 :: Exp
e06 = ECaseDict e03
        ("ArrowTy",["a","b"],
         ECaseDict "a" ("Int", [], EK "One")
                   (EK "Two")
        ) (EK "Three")

v06 :: VDef
v06 = VDef "e06" (ForAll [] "Int") e06

-- | True dict comparison
e07 :: Exp
e07 = EIfTyEq (e04,e04) (EK "True") (EK "False")

v07 :: VDef
v07 = VDef "e07" (ForAll [] "Bool") e07

-- | False dict comparison
e08 :: Exp
e08 = EIfTyEq (e03,e04) (EK "True") (EK "False")

v08 :: VDef
v08 = VDef "e08" (ForAll [] "Bool") e08

e09 :: Exp
e09 = ELet ("ttt", ForAll [] (ConTy "Int" [])
              , EK "One")
      "ttt"

v09 :: VDef
v09 = VDef "e09" (ForAll [] "Int") e09

e10 :: Exp
e10 = EApp (ELam ("v",intTy) "v") (EK "Three")

v10 :: VDef
v10 = VDef "e10" (ForAll [] "Int") e10

-- | Let-bind "id" and then run the body
letId :: Exp -> Exp
letId ex = ELet ("id",
           ForAll [("a",Star)]
             (ArrowTy (VarTy "a") (VarTy "a")),
             (ELam ("x", VarTy "b") (EVar "x")))
                ex

e11 :: Exp
e11  =  letId (EVar "id")

v11 :: VDef
v11 = VDef "e11" (ForAll [("a",Star)] (ArrowTy "a" "a")) e11

-- | Apply identity to itself.
e12 :: Exp
e12  =  letId (EApp "id" "id")

v12 :: VDef
v12 = VDef "e12" (ForAll [("a",Star)] (ArrowTy "a" "a")) e12

-- | Apply to a number:
e13 :: Exp
e13  =  letId (EApp "id" (EK "One"))

v13 :: VDef
v13 = VDef "e13" (ForAll [] "Int") e13

e14 :: Exp
e14 = (ECase (EK "One") [(Pat "One" [], EK "Two")])

v14 :: VDef
v14 = VDef "e14" (ForAll [] "Int") e14

e15 :: Exp
e15 = ELam ("x", ConTy "Maybe" [ConTy "Int" []]) $
       ECase "x"
       [ (Pat "Just" ["y"], EVar "y")
       , (Pat "Nothing" [], EK "One")
       ]

v15 :: VDef
v15 = VDef "e15" (ForAll [] (ConTy "Maybe" ["Int"])) e15


intTy :: MonoTy
intTy = ConTy "Int" []

-- | All expressions so that we can test them uniformly.
allExprs :: [Exp]
allExprs = [e02, e03, e04, e05, e06, e07, e08, e09, e10, e11, e12, e13]

allMain :: [VDef]
allMain = [v02, v03, v04, v05, v06, v07, v08, v09, v10, v11, v12, v13]

-- | The subset of expressions whose `lowerDicts` output value should
-- be exactly the same as the original output value.
allExprsSameLowered :: [Exp]
allExprsSameLowered = [e02, e05, e06, e07, e08, e09, e10, e11, e12, e13]

allMainSameLowered :: [VDef]
allMainSameLowered = [v02, v05, v06, v07, v08, v09, v10, v11, v12, v13]


--------------------------------------------------------------------------------
-- Whole programs:

-- | Loop program where omega is present but not called
p8_unusedLoop :: Prog
p8_unusedLoop
  = Prog [] [VDef "loop" (ForAll [("a",Star)] "a") "loop"]
  $ VDef "diverge"
         (ForAll [("a",Star)] (ConTy "Maybe" ["a"]))
         (EK "Nothing")

(==>) :: MonoTy -> MonoTy -> MonoTy
(==>) = ArrowTy

p9_append :: Prog
p9_append = Prog
  [DDef "List" [("a", Star)] [] []
      [ KCons "Nil" [] ["a"]
      , KCons "Cons" ["a", listy "a"] ["a"]
      ]
    ]
  [VDef "append" (ForAll [("a", Star)] (listy "a" ==> (listy "a" ==> listy "a")))
        (ELam ("ls1", listy "a") $
          ELam ("ls2", listy "a") $
            ECase "ls1"
              [(Pat "Nil" [], EVar "ls2"),
               (Pat "Cons" ["y", "ys"], consy (EVar "y") (EApp (EApp (EVar "append") (EVar "ys")) (EVar "ls2")))])
  ]
  (VDef "p9"
        (ForAll [] (listy "Int"))
        (EApp (EApp (EVar "append") (toListy [EK "One", EK "One", EK "One", EK "One", EK "One", EK "One", EK "One", EK "One", EK "One"]))
              (toListy [EK "Two", EK "Two", EK "Two", EK "Two", EK "Two", EK "Two", EK "Two", EK "Two", EK "Two"])))
  where
    listy :: MonoTy -> MonoTy
    listy a = ConTy "List" [a]

    consy :: Exp -> Exp -> Exp
    consy x xs = EApp (EApp (EK "Cons") x) xs

    toListy :: [Exp] -> Exp
    toListy = foldr consy (EK "Nil")


p10_mut_add_even :: Prog
p10_mut_add_even = Prog
  [ DDef "Nat" [] [] []
    [ KCons "Zero" [] [],
      KCons "Suc"  [naty] []
    ]
  ]
  [ VDef "myEven" (ForAll [] (naty ==> booly))
         (ELam ("x", naty) $
           ECase "x"
             [ (Pat "Zero" [], EK "True"),
               (Pat "Suc" ["n"], (EApp (EVar "myOdd") (EVar "n")))
             ])
  , VDef "myOdd" (ForAll [] (naty ==> booly))
         (ELam ("x", naty) $
           ECase "x"
             [ (Pat "Zero" [], EK "False")
             , (Pat "Suc" ["n"], (EApp (EVar "myEven") (EVar "n")))
             ])
  ]
  (VDef "p10"
        (ForAll [] "Bool")
        (EApp (EVar "myEven") (toNaty 11)))
  where
    naty :: MonoTy
    booly :: MonoTy
    suc :: Exp -> Exp
    toNaty :: Int -> Exp

    naty = ConTy "Nat" []
    booly = ConTy "Bool" []
    suc = EApp (EK "Suc")
    toNaty 0 = EK "Zero"
    toNaty n = suc (toNaty (n - 1))


p11_bustedList :: Prog
p11_bustedList = Prog
  [DDef "List" [] [("a", Star)] []
      [ KCons "Nil" [] ["a"]
      , KCons "Cons" ["a", ConTy "List" ["a"]] ["a"]
      ]
  ]
  []
  (VDef "p11"
       (ForAll [] (ConTy "List" ["Int"]))
       (appLst (EK "Cons") [(EK "One"),(EK "Nil")]))

-- | All type-correct runnable progs.
allProgs :: [Prog]
allProgs
  -- The naked expression tests should only depend on types in the "Prelude"
  = [ Prog [] [] v | v <- allMain ]
 ++ [ p8_unusedLoop
    , existential1
    , p9_append
    , p10_mut_add_even
    , p11_bustedList
    ]

-- | Analogous to (and including) allExprsSameLowered
allProgsSameLowered :: [Prog]
allProgsSameLowered
  = [ Prog [] [] v | v <- allMainSameLowered ]
 ++ [ p8_unusedLoop
    , p9_append
    , p10_mut_add_even
    , p11_bustedList
    , existential1
    ]

-- Programs which are valid programs in the core language but NOT valid inputs
-- to Ghostbuster.
test_p11 :: [TyVar]
test_p11 =
  let Prog d _ _ = p11_bustedList
  in getKConsDicts d "Nil"

--------------------------------------------------------------------------------
-- Tests for the type checker

uselessExistential :: DDef
uselessExistential = DDef "Foo" [] [] [] [KCons "Foo" ["a"] []]

-- | Construct useless existential
existential1 :: Prog
existential1 =
  Prog [uselessExistential] []
       (VDef "existential1" (ForAll [] "Foo") (EApp (EK "Foo") (EK "One")))

-- | Skolem type variable error.
existential2_err :: Prog
existential2_err
  = Prog [uselessExistential] []
  $ VDef "existential2"
         (ForAll [] "Foo")
         (ECase (EApp (EK "Foo") (EK "One")) [ (Pat "Foo" ["x"], "x") ])

