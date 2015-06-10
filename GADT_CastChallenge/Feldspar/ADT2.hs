{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

-- | An attempt to simulate the ghostbuster algorithm by hand,
-- mechanically translating from the GADT to this version.
--   (written during a meeting w/ Ken, Matteo, & Ryan)

module Feldspar.ADT2 where

import           Data.Typeable
import           Debug.Trace
import qualified Feldspar.GADT as G
import           Text.Printf


data Exp where
  Con :: Int -> Exp
  Add :: Exp -> Exp -> Exp
  Var :: Var -> Exp
  Abs :: Typ -> Exp -> Exp
  App :: Exp -> Exp -> Exp

data Var where
  Zro :: Var
  Suc :: Var -> Var

data Typ where
  Int :: Typ
  Arr :: Typ -> Typ -> Typ

-- Because I was told to synthesize "a", I must hide it in the sealed
-- result type here:
data SealedExp e where
  SealedExp :: Typeable a => G.Exp e a -> SealedExp e

data SealedVar e where
  SealedVar :: Typeable a => G.Var e a -> SealedVar e

data SealedTyp where
  SealedTyp :: Typeable a => G.Typ a -> SealedTyp

-- Because "e" is checked, it is a "parameter" here:
downcastExp :: forall e . Typeable e => Exp -> Maybe (SealedExp e)
downcastExp (Con e)     = error $ "downcastExp (Con " ++ show e ++ ")"
downcastExp (Add e1 e2) =
  -- We know the "e" in the output is the same as the inputs.
  -- That lets us know what "e" to ask for in our recursive calls here.
  do SealedExp (a::G.Exp e ta) <- (downcastExp e1)
     SealedExp (b::G.Exp e tb) <- (downcastExp e2)
     Refl <- unify (unused :: ta) (unused::Int)
     Refl <- unify (unused :: tb) (unused::Int)
     return $ SealedExp $ G.Add a b
downcastExp (Var e)     = error "downcastExp/Var"
downcastExp (Abs t e)   =
  do SealedTyp (t' :: G.Typ tt) <- downcastTyp t
     SealedExp (e' :: G.Exp (e,tt) b) <- downcastExp e
     return $ SealedExp $ G.Abs t' e'
downcastExp (App e1 e2)  =
  do SealedExp (a::G.Exp e tarr) <- (downcastExp e1)
     SealedExp (b::G.Exp e ta)   <- (downcastExp e2)

     let typ = typeOf (unused :: tarr)
     trace (show typ) $ return ()
     -- let (e' :: G.Exp e tb) = G.App a b
     -- let Just Refl = unify (unused :: tarr) (unused:: ta -> tb)
     -- return $ SealedExp e'

     -- splitTyConApp $ typeOf

     -- return $ SealedExp $ G.App undefined undefined
     error "downcastExp/App"

-- test = downcastExp (App (Abs ))

downcastVar :: Typeable e => Var  -> Maybe (SealedVar e)
downcastVar Zro = undefined
downcastVar (Suc v) = undefined

downcastTyp :: Typ -> Maybe (SealedTyp)
downcastTyp Int = Just (SealedTyp G.Int)
downcastTyp (Arr x1 x2) =
  do SealedTyp a <- downcastTyp x1
     SealedTyp b <- downcastTyp x2
     -- No constraints on a/b.  How do we ensure (a->b) on the result though?
     -- Goal: call G.Arr
     -- Reasoning: why do we not need a cast?
     return $ SealedTyp $ G.Arr a b


--------------------------------------------------------------------------------

unify :: (Typeable s, Typeable t) => s -> t -> Maybe (s :~: t)
unify s t =
  case eqT of
    Nothing   -> typeError s t
    refl      -> refl

unused :: t
unused = error "this is never used"


typeError :: forall s t a. (Typeable s, Typeable t) => s -> t -> a
typeError _ _
  = error
  $ printf "Couldn't match expected type `%s' with actual type `%s'"
           (show (typeOf (unused::s)))
           (show (typeOf (unused::t)))
