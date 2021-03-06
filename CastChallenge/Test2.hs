{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test2 where

import Text.Printf
import Control.Exception
import Prelude                  hiding ( exp )

import qualified ADT2           as ADT
import qualified GADT2          as GADT


-- Test cases that should result in type errors
--
f1 :: ADT.Exp
f1 = ADT.Const (ADT.BVal True)                -- Test harness expects integer expressions

f2 :: ADT.Exp
f2 = ADT.If (ADT.Const$ ADT.IVal 0)           -- incorrect type
            (ADT.Const$ ADT.IVal 1)
            (ADT.Const$ ADT.IVal 2)

f3 :: ADT.Exp
f3 = ADT.If (ADT.Const$ ADT.BVal True)
            (ADT.Const$ ADT.BVal False)       -- alternatives don't match
            (ADT.Const$ ADT.IVal 42)

f4 :: ADT.Exp
f4 = ADT.Let (ADT.Const$ ADT.BVal True)
   $ ADT.Var ADT.TInt 0         -- incorrect variable

f5 :: ADT.Exp
f5 = ADT.Var ADT.TInt 0        -- unbound variable


-- Test harness

roundtrip :: forall t. GADT.Elt t => String -> GADT.Exp '[] t -> IO ()
roundtrip name gadt = do
  let adt       = ADT.upcast gadt
      gadt'     = ADT.downcast adt                :: GADT.Exp '[] t

  printf "Test %s:\n"     name
  printf "  Orig: %s\n"   (show gadt)
  printf "  Evaled: %s\n" (show (GADT.eval gadt))
  printf "  Upcast: %s\n"   (show adt)
  printf "  Evaled: %s\n" (show (ADT.eval adt))
  printf "  BkDown: %s\n\n" (show gadt')


shouldFail :: String -> ADT.Exp -> IO ()
shouldFail name adt = do
  -- TLM: This identifies a possible pain point. In order to do the upcast, we
  --      need to give the upcast function a concrete return type. This
  --      (probably) means that when we get an ADT from the client (e.g. over
  --      the FFI) we'll need to call a _monomorphic_ version of 'upcast'
  --      specialised to the type we expect ):
  --
  let gadt      = ADT.downcast adt      :: GADT.Exp '[] Int

  printf "Test %s:\n" name
  printf "  Orig:    %s\n" (show adt)

  r <- try (evaluate $ let e = show gadt in length e `seq` e)
  case r of
    Left e  -> printf "  Success: %s\n\n" (show (e :: SomeException))
    Right a -> printf "  Failed:  %s\n\n" a


runTests :: IO ()
runTests = do
  roundtrip "p0" GADT.p0
  roundtrip "p1" GADT.p1
  roundtrip "p2" GADT.p2
  roundtrip "p3" GADT.p3
  roundtrip "p4" GADT.p4
  roundtrip "p5" GADT.p5
  roundtrip "p6" GADT.p6

  shouldFail "f1" f1
  shouldFail "f2" f2
  shouldFail "f3" f3
  shouldFail "f4" f4
  shouldFail "f5" f5
