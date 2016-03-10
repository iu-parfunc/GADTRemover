
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE InstanceSigs #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Ghostbuster where
import Prelude
       hiding (Char, Float, Double, Int, Word, Integer, String, FilePath,
               IO, IOError, Ordering, Rational, Real, ShowS, String, Bool(..),
               Maybe(..), Either(..))
import Prelude as P

import Data.Maybe
import Data.Typeable
-- import Data.Type.Equality

data Vec a n where
  Nil :: Vec a ZZ
  Cons :: a -> Vec a n -> Vec a (S n)

deriving instance Show a => Show (Vec a n)
deriving instance Eq a => Eq (Vec a n)
deriving instance Ord a => Ord (Vec a n)

-- Ghostbusted data type 'Vec a_k0  n_s0':
--    kept        : a_k0
--    checked     :
--    synthesised : n_s0
--
data Vec' a where
   Nil' :: Vec' a
   Cons' :: a -> Vec' a -> Vec' a
 deriving (Show, Read, Eq, Ord)


-- deriving instance Read a => Read (Vec a n)
{-
    Couldn't match type ‘n’ with ‘S n0’
      ‘n’ is a rigid type variable bound by
          the instance declaration at Busted_Vec.hs:36:1
    Expected type: Vec a n
      Actual type: Vec a (S n0)
-}

--  readsPrec :: forall a n . P.Int -> P.String -> [(Vec a n, P.String)]
instance (Read a, Typeable a, Typeable n0) => Read (Vec a n0) where
  readsPrec i s =

  -- Huh, not sure why this version doesn't work:
  --   [ (v,s)
  --   | (v',s) <- ls
  --   , SealedVec (v :: Vec a n2) <- upVec v'
  --   , Just Refl <- eqT :: Maybe (n0 :~: n2)
  --   ]
    catMaybes $
     map (\(v',s) ->
          case upVec v' of
            SealedVec (v :: Vec a n2) ->
              case eqT :: Maybe (n0 :~: n2) of
                Just Refl -> Just (v,s)
                Nothing   -> Nothing)
        ls
   where
    ls :: [(Vec' a, P.String)]
    ls = readsPrec i s


data ZZ where
data S n where

data SealedVec a_k0 where
  SealedVec :: Typeable n => Vec a n -> SealedVec a


-- data TypeCaseSucc t where
--   TypeCaseSucc :: forall a b c . TypeDict b -> TypeDict c ->
--                    (a :~: (b -> c)) -> TypeCaseArrow a
-- typeCaseArrow :: forall arr. (TypeDict arr) -> Maybe (TypeCaseArrow arr)

typeCaseSucc :: forall a n . Typeable (S n) =>
                Proxy (S n) -> (Typeable n => () -> a)
                -> a
typeCaseSucc = undefined

typeCaseSucc2 :: forall a n . Typeable (S n) =>
                Proxy (S n) -> (Typeable n => a)
                -> a
typeCaseSucc2 = undefined


-- Can't make custom Typeable instance, and this requires UndecidableInstances anyway:
-- instance Typeable (S n) => Typeable n

downVec :: forall a n . Typeable n => Vec a n -> Vec' a
downVec !orig
  = case orig of
      Nil -> Nil'
      Cons a b ->
        -- Go from Typeable (S n) to Typeable n...
        -- let rep = typeRep (Proxy::Proxy n) in
        typeCaseSucc2 (Proxy::Proxy n)
          (Cons' a (downVec b))


upVec :: forall a . Vec' a -> SealedVec a
upVec !lower
  = case lower of
        Nil' -> SealedVec Nil
        Cons' a b ->
          case upVec b of
            SealedVec b' ->
--              let n_dict = n_s0_b'_dict in
--              let n_s0_dict = SDict n_dict in
              SealedVec (Cons a b')


main :: P.IO ()
main = print "hello"
