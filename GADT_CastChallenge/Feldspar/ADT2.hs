{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MagicHash #-}

-- | An attempt to simulate the ghostbuster algorithm by hand,
-- mechanically translating from the GADT to this version.
--   (written during a meeting w/ Ken, Matteo, & Ryan)

module Feldspar.ADT2 where

import           Data.Typeable
import           Debug.Trace
import qualified Feldspar.GADT as G
import           Text.Printf

import Unsafe.Coerce (unsafeCoerce)
import GHC.Prim (Proxy#)

------------------------------ From Ken's Example -------------------------

-- TODO: We need to make this so that we can use this with polymorphic
-- function types. e.g., (Int -> a), (a -> Int), (a -> b)

data TypeCaseArrow a where
  TypeCaseArrow :: (Typeable b, Typeable c) =>
                   (a :~: (b -> c)) -> TypeCaseArrow a

typeCaseArrow :: forall arr. (Typeable arr) => Maybe (TypeCaseArrow arr)
typeCaseArrow = case splitTyConApp (typeRep (Proxy :: Proxy arr)) of
  (op, [b,c]) | op == typeRepTyCon (typeRep (Proxy :: Proxy (->)))
              -> unsafeTypeable b (\(_ :: Proxy b) ->
                 unsafeTypeable c (\(_ :: Proxy c) ->
                 fmap TypeCaseArrow (gcast Refl :: Maybe (arr :~: (b -> c)))))
  _ -> Nothing

newtype Magic ans = Magic (forall a. (Typeable a) => Proxy a -> ans)
newtype Voodoo = Voodoo (forall a. Proxy# a -> TypeRep)

unsafeTypeable :: TypeRep -> (forall a. (Typeable a) => Proxy a -> ans) -> ans
unsafeTypeable rep f = unsafeCoerce (Magic f) (Voodoo (\_ -> rep)) Proxy

---------------------------------------------------------------------------


data Exp where
  Con :: Int -> Exp
  Add :: Exp -> Exp -> Exp
  Var :: Var -> Exp
  Abs :: Typ -> Exp -> Exp
  App :: Exp -> Exp -> Exp
 deriving Show

-- This one is subtle.  Why is the "a" param not ambiguous?  We're
-- deleting it with "synthesized" mode, but the synthesized param is
-- __determined__ by the checked param, so this should pass muster.
data Var where
  Zro :: Var
  Suc :: Var -> Var
  deriving Show

data Typ where
  Int :: Typ
  Arr :: Typ -> Typ -> Typ
 deriving Show

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
-- This works, but I feel as though we're cheating here since we
-- instantiate with Int and we can't deduce that e ~ Int
downcastExp (Con i)     = Just $ SealedExp (G.Con i :: G.Exp i Int)
-- Why was this here before?
-- Question (TZ): How do we recover e?
-- error $ "downcastExp (Con " ++ show e ++ ")"
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
downcastExp (App e1 e2) =
  do SealedExp (a::G.Exp e tarr) <- (downcastExp e1)
     SealedExp (b::G.Exp e ta)   <- (downcastExp e2)

     let typ = typeOf (unused :: tarr)
     trace (show typ) $ return ()

-- Algorithm:
-- 1. get type of a (t1)
-- 2. get type of b (t2)
-- 3. Ensure that t1 unifies with (t2 -> t')
--    where t' is determined by ??

     -- let (e' :: G.Exp e tb) = G.App a b
     -- let Just Refl = unify (unused :: tarr) (unused:: ta -> tb)
     -- return $ SealedExp e'

     -- splitTyConApp $ typeOf

     -- return $ SealedExp $ G.App undefined undefined
     error "downcastExp/App"

-- test = downcastvarstExp (App (Abs ))

-- Typechecks, but we run into problems with Typeable and guaranteeing that it's a tuple when calling this.
downcastVar :: forall a b. (Typeable a, Typeable b) => Var  -> Maybe (SealedVar (a,b))
downcastVar Zro =  Just $ SealedVar (G.Zro :: G.Var (a,b) b)
-- Why do we get that a and b are out of scope here?!? Shouldn't they be in
-- scope since we are using ScopedTypeVariables?
downcastVar (Suc v) =
  do SealedVar (foo :: G.Var a a') <- (downcastVar v)
     return $ SealedVar ((G.Suc foo b) :: G.Var (a,b) a)


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
