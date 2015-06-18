{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

-- | An attempt to simulate the ghostbuster algorithm by hand,
-- mechanically translating from the GADT to this version.
--   (written during a meeting w/ Ken, Matteo, & Ryan)
--
module Feldspar.ADT2 where


import Data.Typeable
import Control.DeepSeq
import Text.Printf

import Unsafe.Coerce                    ( unsafeCoerce )
import GHC.Generics                     ( Generic )
import GHC.Prim                         ( Proxy# )

import TypeCase                         ( typeCaseTuple, TypeCaseTuple(..) )
import qualified Feldspar.GADT          as G

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
  Mul :: Exp -> Exp -> Exp
  Var :: Var -> Exp
  Abs :: Typ -> Exp -> Exp
  App :: Exp -> Exp -> Exp
 deriving (Show, Generic)

-- This one is subtle.  Why is the "a" param not ambiguous?  We're
-- deleting it with "synthesized" mode, but the synthesized param is
-- __determined__ by the checked param, so this should pass muster.
data Var where
  Zro :: Var
  Suc :: Var -> Var
  deriving (Show, Generic)

data Typ where
  Int :: Typ
  Arr :: Typ -> Typ -> Typ
 deriving (Eq, Show, Generic)

-- Because I was told to synthesize "a", I must hide it in the sealed
-- result type here:
data SealedExp e where
  SealedExp :: forall a e . Typeable a =>
               G.Exp e a -> SealedExp e

data SealedVar e where
  SealedVar :: Typeable a => G.Var e a -> SealedVar e

data SealedTyp where
  SealedTyp :: Typeable a => G.Typ a -> SealedTyp

instance NFData Exp
instance NFData Var
instance NFData Typ

--------------------------- Restoring types -----------------------------------

-- Because "e" is checked, it is a "parameter" here:
upExp :: forall e . Typeable e => Exp -> Maybe (SealedExp e)
upExp (Con i)     = Just $ SealedExp (G.Con i)
upExp (Add e1 e2) =
  -- We know the "e" in the output is the same as the inputs.
  -- That lets us know what "e" to ask for in our recursive calls here.
  do SealedExp (a::G.Exp e ta) <- (upExp e1)
     SealedExp (b::G.Exp e tb) <- (upExp e2)
     Refl <- unify (unused :: ta) (unused::Int)
     Refl <- unify (unused :: tb) (unused::Int)
     return $ SealedExp $ G.Add a b
upExp (Mul e1 e2) =       -- exactly same as Add case
  do SealedExp (a::G.Exp e ta) <- (upExp e1)
     SealedExp (b::G.Exp e tb) <- (upExp e2)
     Refl <- unify (unused :: ta) (unused::Int)
     Refl <- unify (unused :: tb) (unused::Int)
     return $ SealedExp $ G.Mul a b
upExp (Var e)     =
  do SealedVar (v) <- (upVar e)
     return $ SealedExp $ G.Var v
upExp (Abs t e)   =
  do SealedTyp (t' :: G.Typ tt) <- upTyp t
     SealedExp (e' :: G.Exp (e,tt) b) <- upExp e
     return $ SealedExp $ G.Abs t' e'
upExp (App e1 e2) =
  do SealedExp (a::G.Exp e tarr) <- (upExp e1)
     SealedExp (b::G.Exp e ta)   <- (upExp e2)
     case typeCaseArrow :: Maybe (TypeCaseArrow tarr) of
       Nothing -> Nothing
       Just (TypeCaseArrow (Refl :: tarr :~: (ta' -> tb))) ->
         do Refl <- unify (unused :: ta') (unused :: ta)
            return $ SealedExp $ G.App a b


-- Typechecks, but we run into problems with Typeable and guaranteeing that it's a tuple when calling this.
-- upVar :: forall a b. (Typeable a, Typeable b) => Var  -> Maybe (SealedVar (a,b))

upVar :: forall e . (Typeable e) => Var  -> Maybe (SealedVar e)
upVar Zro =
  case typeCaseTuple :: Maybe (TypeCaseTuple e) of
    Nothing -> Nothing
    Just (TypeCaseTuple (Refl :: e :~: (x,y))) ->
      return $ SealedVar (G.Zro :: G.Var (x,y) y)
upVar (Suc v) =
  -- problems with unification of types here
  case typeCaseTuple :: Maybe (TypeCaseTuple e) of
    Nothing -> Nothing
    Just (TypeCaseTuple (Refl :: e :~: (e1,b))) ->
     do SealedVar (v' :: G.Var e1 a) <- (upVar v)
        return $ SealedVar ((G.Suc v') :: G.Var e a)

upTyp :: Typ -> Maybe (SealedTyp)
upTyp Int = Just (SealedTyp G.Int)
upTyp (Arr x1 x2) =
  do SealedTyp a <- upTyp x1
     SealedTyp b <- upTyp x2
     -- No constraints on a/b.  How do we ensure (a->b) on the result though?
     -- Goal: call G.Arr
     -- Reasoning: why do we not need a cast?
     return $ SealedTyp $ G.Arr a b

--------------------------- Stripping ------------------------------------------

downExp :: G.Exp e a -> Exp
downExp (G.Con i) = Con i
downExp (G.Var e) = Var $ downVar e
downExp (G.Add e1 e2) = let e1' = downExp e1
                            e2' = downExp e2
                        in Add e1' e2'
downExp (G.Mul e1 e2) = let e1' = downExp e1
                            e2' = downExp e2
                        in Mul e1' e2'
downExp (G.Abs typ e) = let typ' = downTyp typ
                            e'   = downExp e
                        in Abs typ' e'
downExp (G.App e1 e2) = let e1' = downExp e1
                            e2' = downExp e2
                        in App e1' e2'

downTyp :: G.Typ a -> Typ
downTyp G.Int = Int
downTyp (G.Arr t1 t2) = let t1' = downTyp t1
                            t2' = downTyp t2
                        in Arr t1' t2'

downVar :: G.Var e a -> Var
downVar G.Zro = Zro
downVar (G.Suc v) = Suc $ downVar v

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
