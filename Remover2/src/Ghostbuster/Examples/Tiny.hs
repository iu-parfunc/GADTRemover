{-# LANGUAGE OverloadedStrings #-}

-- | Very small example programs for testing purposes.

module Ghostbuster.Examples.Tiny where

import Ghostbuster.Types

--------------------------------------------------------------------------------
-- Just expressions:

p2 :: Exp
p2 = (ECase (EK "One") [(Pat "One" [], EK "Two")])

p3 :: Exp
p3 = EDict ("Int")

p4 :: Exp
p4 = EApp (EApp (EDict ("ArrowTy")) p3) p3

p5 :: Exp
p5 = ECaseDict p4
      ("ArrowTy",["a","b"],
       ECaseDict "a" ("Int", [], EK "One")
                 (EK "Two")
      ) (EK "Three")

-- | Take a false branch
p6 :: Exp
p6 = ECaseDict p3
      ("->",["a","b"],
       ECaseDict "a" ("Int", [], EK "One")
                 (EK "Two")
      ) (EK "Three")

p7 :: Exp
p7 = EApp (ELam ("v",intTy) "v") (EK "Three")

intTy :: MonoTy
intTy = ConTy "Int" []


--------------------------------------------------------------------------------
-- Whole programs:


-- | Loop program where omega is present but not called
p8_unusedLoop :: Prog
p8_unusedLoop = Prog [] [VDef "loop" (ForAll [("a",Star)] "a") "loop"]
                     (EK "Nothing")
