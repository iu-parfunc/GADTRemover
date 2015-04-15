{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test2 where

import Text.Printf
import Prelude                  hiding ( exp )

import qualified ADT2           as ADT
import qualified GADT2          as GADT

test :: forall t. GADT.Elt t => String -> GADT.Exp '[] t -> IO ()
test name gadt = do
  let adt       = ADT.downcast gadt
      gadt'     = ADT.upcast adt                :: GADT.Exp '[] t

  printf "Test %s:\n" name

  printf "  Orig: %s\n"   (show gadt)
  printf "  Down: %s\n"   (show adt)
  printf "  BkUp: %s\n\n" (show gadt')

runTests :: IO ()
runTests = do
  test "p0" GADT.p0
  test "p1" GADT.p1
  test "p2" GADT.p2
  test "p3" GADT.p3
  test "p4" GADT.p4

