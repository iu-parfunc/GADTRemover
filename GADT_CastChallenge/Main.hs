{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad (forM_)
import Data.Maybe
import Debug.Trace

import GADT
import qualified ADT1 as ADT1
import qualified ADT2 as ADT2

--------------------------------------------------------------------------------
-- Test programs:

p0 :: Exp EmptyEnv IntTy
p0 = If T (Lit 3) (Lit 4)

t_p0 :: Exp EmptyEnv IntTy
t_p0 = fromJust $ ADT1.upcast (ADT1.downcast p0)

p1 :: Exp EmptyEnv IntTy
p1 = Let (Lit 5) (Var Zero)

p2 :: Exp EmptyEnv IntTy
p2 = (If T (Lit 11) p1)

p3 :: Exp EmptyEnv IntTy
p3 = Let (Lit 5)
      (If T (Var Zero) (Lit 4))

p3b :: ADT1.Exp
p3b =
  ADT1.Let
    (ADT1.Lit 5)
    (ADT1.If ADT1.T
             (ADT1.Var (ADT1.Zero IntTy))
             (ADT1.Lit 4))

-- An Add with different envs:
p4 :: Exp EmptyEnv IntTy
p4 = Let (Lit 4)
   $ Let (Lit 5)
   $ Add (Var Zero)
         (Var (Succ Zero))


i0 :: Idx (Extend IntTy (Extend BoolTy EmptyEnv)) BoolTy
i0 = Succ Zero

t_i0 :: IO ()
t_i0 = print $ ADT1.upcastIdx $ ADT1.downcastIdx i0

--------------------------------------------------------------------------------

-- FinishMe: test more uniformly:
--
tests_adt1 :: [(String, ADT1.Sealed)]
tests_adt1 =
  [("p0", ADT1.Sealed p0)
  ,("p1", ADT1.Sealed p1)
  ,("p2", ADT1.Sealed p2)
  ,("p3", ADT1.Sealed p3)
  ,("p4", ADT1.Sealed p4)
  ]

main :: IO ()
main = do
  putStrLn "\nTest i0:"
  t_i0

  forM_ tests_adt1 $ \ (name, ADT1.Sealed (expr :: Exp env a)) -> do
    putStrLn$ "\nTest "++name++":"
    putStrLn$ "  Orig: "++show expr
    putStrLn$ "  Down: "++show (ADT1.downcast expr)
    putStrLn$ "  BkUp: "++maybe "<failed>" show (ADT1.upcast (ADT1.downcast expr) :: Maybe (Exp EmptyEnv a))

