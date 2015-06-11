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

import           TypeCase (typeCaseTuple, TypeCaseTuple(..))

import           Unsafe.Coerce (unsafeCoerce)
import           GHC.Prim (Proxy#)

------------------------------ From Ken's Example -------------------------

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

--------------------------- Downcasting -----------------------------------

-- Because "e" is checked, it is a "parameter" here:
downcastExp :: forall e . Typeable e => Exp -> Maybe (SealedExp e)
downcastExp (Con i)     = Just $ SealedExp (G.Con i :: G.Exp e Int)
downcastExp (Add e1 e2) =
  -- We know the "e" in the output is the same as the inputs.
  -- That lets us know what "e" to ask for in our recursive calls here.
  do SealedExp (a::G.Exp e ta) <- (downcastExp e1)
     SealedExp (b::G.Exp e tb) <- (downcastExp e2)
     Refl <- unify (unused :: ta) (unused::Int)
     Refl <- unify (unused :: tb) (unused::Int)
     return $ SealedExp $ G.Add a b
downcastExp (Var e)     =
  do SealedVar (v :: G.Var e a) <- (downcastVar e)
     return $ SealedExp $ G.Var v
downcastExp (Abs t e)   =
  do SealedTyp (t' :: G.Typ tt) <- downcastTyp t
     SealedExp (e' :: G.Exp (e,tt) b) <- downcastExp e
     return $ SealedExp $ G.Abs t' e'
downcastExp (App e1 e2) =
  do SealedExp (a::G.Exp e tarr) <- (downcastExp e1)
     SealedExp (b::G.Exp e ta)   <- (downcastExp e2)
     case typeCaseArrow :: Maybe (TypeCaseArrow tarr) of
       Nothing -> Nothing
       Just (TypeCaseArrow (Refl :: tarr :~: (ta' -> tb))) ->
         do Refl <- unify (unused :: ta') (unused :: ta)
            return $ SealedExp $ G.App a b

-- test = downcastvarstExp (App (Abs ))

-- Typechecks, but we run into problems with Typeable and guaranteeing that it's a tuple when calling this.
-- downcastVar :: forall a b. (Typeable a, Typeable b) => Var  -> Maybe (SealedVar (a,b))

downcastVar :: forall e . (Typeable e) => Var  -> Maybe (SealedVar e)
downcastVar Zro =
  case typeCaseTuple :: Maybe (TypeCaseTuple e) of
    Nothing -> Nothing
    Just (TypeCaseTuple (Refl :: e :~: (x,y))) ->
      return $ SealedVar (G.Zro :: G.Var (x,y) y)
downcastVar (Suc v) =
  -- problems with unification of types here
  case typeCaseTuple :: Maybe (TypeCaseTuple e) of
    Nothing -> Nothing
    Just (TypeCaseTuple (Refl :: e :~: (e1,b))) ->
     do SealedVar (v' :: G.Var e1 a) <- (downcastVar v)
        return $ SealedVar ((G.Suc v') :: G.Var e a)

downcastTyp :: Typ -> Maybe (SealedTyp)
downcastTyp Int = Just (SealedTyp G.Int)
downcastTyp (Arr x1 x2) =
  do SealedTyp a <- downcastTyp x1
     SealedTyp b <- downcastTyp x2
     -- No constraints on a/b.  How do we ensure (a->b) on the result though?
     -- Goal: call G.Arr
     -- Reasoning: why do we not need a cast?
     return $ SealedTyp $ G.Arr a b

--------------------------- Upcasting ------------------------------------------

upcastExp :: G.Exp e a -> Exp
upcastExp (G.Con i) = Con i
upcastExp (G.Var e) = Var $ upcastVar e
upcastExp (G.Add e1 e2) = let e1' = upcastExp e1
                              e2' = upcastExp e2
                          in Add e1' e2'
upcastExp (G.Abs typ e) = let typ' = upcastTyp typ
                              e'   = upcastExp e
                          in Abs typ' e'
upcastExp (G.App e1 e2) = let e1' = upcastExp e1
                              e2' = upcastExp e2
                          in App e1' e2'

upcastTyp :: G.Typ a -> Typ
upcastTyp G.Int = Int
upcastTyp (G.Arr t1 t2) = let t1' = upcastTyp t1
                              t2' = upcastTyp t2
                          in Arr t1' t2'

upcastVar :: G.Var e a -> Var
upcastVar G.Zro = Zro
upcastVar (G.Suc v) = let v'= upcastVar v
                      in Suc v'

---------------------------------------------------------------------------

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
