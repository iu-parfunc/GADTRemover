{-# LANGUAGE ScopedTypeVariables #-}

module Feldspar.Benchmark
  where

import Feldspar.Example
import qualified Feldspar.InterpGADT                    as GADT
import qualified Feldspar.Hint                          as Hint
import qualified Feldspar.ADT2                          as ADT2

import Data.Typeable
import Criterion.Main


main :: IO ()
main =
  let fib_10            = fib 10
      fib_20            = fib 20
      pascal_10_5       = pascal 10 5

      testADT :: ADT2.Exp -> Int
      testADT adt =
        case ADT2.upcastExp adt of
          Right (ADT2.SealedExp e)
            | Just gadt <- gcast e      -> GADT.run gadt ()
          Right _                       -> error "Upcast failed: type-mismatch"
          Left err                      -> error $ unlines ["Upcast failed:", err]

      testHint :: ADT2.Exp -> IO Int
      testHint adt = do
        gadt   <- Hint.downcastExp adt
        return $! GADT.run gadt ()

  in
  defaultMain
    [ env (return (ADT2.upcastExp fib_10)) $ \adt ->
        bgroup "fib.10"
          [ bench "run"   $ whnf (GADT.run fib_10) ()
          , bench "adt2"  $ whnf testADT adt
          , bench "hint"  $ whnfIO (testHint adt)
          ]

    , env (return (ADT2.upcastExp fib_20)) $ \adt ->
        bgroup "fib.20"
          [ bench "run"   $ whnf (GADT.run fib_20) ()
          , bench "adt2"  $ whnf testADT adt
          , bench "hint"  $ whnfIO (testHint adt)
          ]

    , env (return (ADT2.upcastExp pascal_10_5)) $ \adt ->
        bgroup "pascal.10.5"
          [ bench "run"   $ whnf (GADT.run pascal_10_5) ()
          , bench "adt2"  $ whnf testADT adt
          , bench "hint"  $ whnfIO (testHint adt)
          ]
    ]

