{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}

module GADTRemover.CastChallenge.DeferredErrors where

data Exp t where
  Const :: t -> Exp t
  Add   :: Exp Int -> Exp Int -> Exp Int
  If    :: Exp Bool -> Exp a -> Exp a -> Exp x

instance Show (Exp t) where
  show (Const t) = "Const"
  show (Add a b) = "Add  ("++show a++") ("++show b++")"
  show (If a b c) = "If ("++show a++") ("++show b++") ("++show c++")"


walk1 :: Exp t -> Exp t
walk1 e =
  case e of
   Const t   -> Const t
   Add e1 e2 -> Add (walk1 e1) (walk1 e2)
   If a b c  -> If (walk1 a) (walk1 b) (walk1 c)

walk2 :: Exp Int -> Exp Int
walk2 e =
  case e of
   Const t   -> Const t
   Add e1 e2 -> Add (walk2 e1) (walk2 e2)
   If a b c  -> If (walk2 a) (walk2 b) (walk2 c)


x :: Exp Bool
x = Const True

demo :: IO ()
demo =
  do putStrLn "First walk:"
     print (walk1 x)
     putStrLn "Second walk:"
     print (walk2 x)
     putStrLn "Done."
