
module Feldspar.Hint
  where

import qualified Feldspar.GADT                  as GADT
import Language.Haskell.Interpreter


say :: String -> Interpreter ()
say = liftIO . putStrLn

printInterpreterError :: InterpreterError -> IO ()
printInterpreterError err =
  case err of
    UnknownError s      -> putStrLn s
    NotAllowed s        -> putStrLn s
    GhcException s      -> putStrLn s
    WontCompile ss      -> putStrLn . unlines $ map errMsg ss


_let :: String -> String -> String -> String
_let var bnd body
  = parens
  $ concat [ "let ", var, " = ", parens bnd, " in ", parens body ]

test :: Interpreter ()
test = do
  loadModules ["Feldspar.GADT"]
  setImportsQ [ ("Prelude",             Nothing)
              , ("Feldspar.GADT",       Nothing)
              ]

  say "Query the type of an expression:"
  let double    = "Abs Int (Var Zro `Add` Var Zro)"
      quadruple = _let "double" double
                  "(compose Int Int Int `App` double `App` double) `App` (Con 1)"

  say =<< typeOf double
  say =<< typeOf quadruple

  say "Try to evaluate the interpreter:"
  run <- interpret ("flip run ()") (as :: GADT.Exp () Int -> Int)       -- must be monomorphic
  q   <- interpret quadruple       infer                                -- we can just infer this type

  say . show $ run q


main :: IO ()
main = do
  r <- runInterpreter test
  case r of
    Left err -> printInterpreterError err
    Right () -> putStrLn "Ok!"

