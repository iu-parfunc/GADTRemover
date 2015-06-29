{-# LANGUAGE OverloadedStrings #-}

-- | Very small example programs for testing purposes.

module Ghostbuster.Examples.Tiny where

import Ghostbuster.Types

--------------------------------------------------------------------------------
-- Just expressions:

e02 :: Exp
e02 = (ECase (EK "One") [(Pat "One" [], EK "Two")])

e03 :: Exp
e03 = EDict ("Int")

-- | Construct arrow dictionary
e04 :: Exp
e04 = EApp (EApp (EDict ("ArrowTy")) e03) e03

e05 :: Exp
e05 = ECaseDict e04
       ("ArrowTy",["a","b"],
        ECaseDict "a" ("Int", [], EK "One")
                  (EK "Two")
       ) (EK "Three")

-- | Take a false branch
e06 :: Exp
e06 = ECaseDict e03
        ("->",["a","b"],
         ECaseDict "a" ("Int", [], EK "One")
                   (EK "Two")
        ) (EK "Three")

-- | True dict comparison
e07 :: Exp
e07 = EIfTyEq (e04,e04) (EK "True") (EK "False")

-- | False dict comparison
e08 :: Exp
e08 = EIfTyEq (e03,e04) (EK "True") (EK "False")

e10 :: Exp
e10 = EApp (ELam ("v",intTy) "v") (EK "Three")

intTy :: MonoTy
intTy = ConTy "Int" []

-- | All expressions so that we can test them uniformly.
allExprs :: [Exp]
allExprs = [e02, e03, e04, e05, e06, e07, e08, e10]

-- | The subset of expressions whose `lowerDicts` output value should
-- be exactly the same as the original output value.
allExprsSameLowered :: [Exp]
allExprsSameLowered = [e02, e05, e06, e07, e08, e10]

--------------------------------------------------------------------------------
-- Whole programs:


-- | Loop program where omega is present but not called
p8_unusedLoop :: Prog
p8_unusedLoop = Prog [] [VDef "loop" (ForAll [("a",Star)] "a") "loop"]
                     (EK "Nothing")

-- | All type-correct runnable progs.
allProgs :: [Prog]
allProgs =
  -- The naked expression tests should only depend on types in the "Prelude"
  [ Prog [] [] e | e <- allExprs] ++
  [ p8_unusedLoop, existential1 ]

-- | Analogous to (and including) allExprsSameLowered
allProgsSameLowered :: [Prog]
allProgsSameLowered =
  [ Prog [] [] e | e <- allExprsSameLowered ] ++
  [ p8_unusedLoop, existential1 ]

--------------------------------------------------------------------------------
-- Tests for the type checker

uselessExistential :: DDef
uselessExistential = DDef "Foo" [] [] [] [KCons "Foo" ["a"] []]

-- | Construct useless existential
existential1 :: Prog
existential1 =
  Prog [uselessExistential] []
       (EApp (EK "Foo") (EK "One"))

-- | Skolem type variable error.
existential2_err :: Prog
existential2_err =
  Prog [uselessExistential] [] $
    ECase (EApp (EK "Foo") (EK "One"))
          [ (Pat "Foo" ["x"], "x") ]
