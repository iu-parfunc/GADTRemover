
module Feldspar.Hint
  where

import System.Environment
import Data.Typeable
import Text.PrettyPrint.Leijen                  as PP
import Language.Haskell.Interpreter             as Hint
import Language.Haskell.Interpreter.Unsafe      as Hint

import qualified Feldspar.ADT2                  as ADT
import qualified Feldspar.GADT                  as GADT


ppExp :: ADT.Exp -> String
ppExp = show . ppE
  where
    ppE (ADT.Con i)   = PP.parens (text "Con" <+> int i)
    ppE (ADT.Var v)   = PP.parens (text "Var" <+> ppV v)
    ppE (ADT.Abs t e) = PP.parens (text "Abs" <+> ppT t <+> ppE e)
    ppE (ADT.App f x) = PP.parens (text "App" <+> ppE f <+> ppE x)
    ppE (ADT.Add x y) = PP.parens (text "Add" <+> ppE x <+> ppE y)
    ppE (ADT.Mul x y) = PP.parens (text "Mul" <+> ppE x <+> ppE y)

    ppV ADT.Zro       = text "Zro"
    ppV (ADT.Suc v)   = PP.parens (text "Suc" <+> ppV v)

    ppT ADT.Int       = text "Int"
    ppT (ADT.Arr a b) = PP.parens (text "Arr" <+> ppT a <+> ppT b)


interpreterError :: InterpreterError -> a
interpreterError e
  = error
  $ case e of
    UnknownError s      -> s
    NotAllowed s        -> s
    GhcException s      -> s
    WontCompile ss      -> unlines $ map errMsg ss

downcastExp :: (Typeable env, Typeable a) => ADT.Exp -> IO (GADT.Exp env a)
downcastExp adt
  = fmap (either interpreterError id)
  $ do
        args <- lookupEnv "HINT_ARGS"

        unsafeRunInterpreterWithArgs (maybe [] read args) $ do
          loadModules ["Feldspar.GADT"]
          setImportsQ [ ("Prelude",             Nothing)
                      , ("Feldspar.GADT",       Nothing) ]
          --
          interpret (ppExp adt) infer


{--
say :: String -> Interpreter ()
say = liftIO . putStrLn

_let :: String -> String -> String -> String
_let var bnd body
  = Hint.parens
  $ concat [ "let ", var, " = ", Hint.parens bnd
           , " in ", Hint.parens body ]

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

  say "Try using the pretty-printer:"
  let four' = ppExp ADT.four
  say four'
  r    <- interpret four' infer
  say . show $ run r

  gadt <- interpret four' (as :: GADT.Exp () Int)
  say . show $ GADT.run gadt ()



main :: IO ()
main = do
  r <- runInterpreter test
  case r of
    Left err -> printInterpreterError err
    Right () -> putStrLn "Ok!"
--}

