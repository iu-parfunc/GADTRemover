-- Ghostbusted data type 'Vec a_k0  n_s0':
--    kept        : a_k0
--    checked     :
--    synthesised : n_s0
--
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Ghostbuster where
import Prelude
       hiding (Char, Float, Double, Int, Word, Integer, String, FilePath,
               IO, IOError, Ordering, Rational, Real, ShowS, String, Bool(..),
               Maybe(..), Either(..))
import qualified Prelude as P

data TypeDict a where
        ExistentialDict :: TypeDict any
        SDict :: TypeDict a -> TypeDict (S a)
        ZZDict :: TypeDict ZZ

data TyEquality a b where
        Refl :: TyEquality a a

data Vec a_k0 n_s0 where
        Nil :: Vec a ZZ
        Cons :: a -> Vec a n -> Vec a (S n)

deriving instance Show a => Show (Vec a n)
-- deriving instance Read a => Read (Vec a n)
deriving instance Eq a => Eq (Vec a n)
deriving instance Ord a => Ord (Vec a n)

{-
    Couldn't match type ‘n’ with ‘S n0’
      ‘n’ is a rigid type variable bound by
          the instance declaration at Busted_Vec.hs:36:1
    Expected type: Vec a n
      Actual type: Vec a (S n0)
-}

--  readsPrec :: forall a n . P.Int -> P.String -> [(Vec a n, P.String)]
{-
instance (Read a, Typeable a) => Read (Vec a n) where
  readsPrec i s =
    map (\(v',s) ->
          case upVec v' of
            SealedVec d v ->
              case checkTEQ d
         )
        ls
   where
    ls :: [(Vec' a, P.String)]
    ls = readsPrec i s
    -- [(, "")]
-}

data ZZ where

data S n where

data Vec' a_k0 where
        Nil' :: Vec' a
        Cons' :: a -> Vec' a -> Vec' a
 deriving (Show, Read, Eq, Ord)

data SealedVec a_k0 where
        SealedVec :: TypeDict n_s0 -> Vec a_k0 n_s0 -> SealedVec a_k0

data ArrowTy a b where

data Int where
        One :: Int
        Two :: Int
        Three :: Int

data Maybe a where
        Just :: a -> Maybe a
        Nothing :: Maybe a

data Bool where
        True :: Bool
        False :: Bool

data Unit where
        Unit :: Unit

data Tup2 a b where
        Tup2 :: a -> b -> Tup2 a b

checkTEQ :: TypeDict t -> TypeDict u -> Maybe (TyEquality t u)
checkTEQ !x !y
  = case x of
        SDict a1 -> case y of
                        SDict a2 -> case checkTEQ a1 a2 of
                                        Just Refl -> Just Refl
                                        Nothing -> Nothing
                        ZZDict -> Nothing
                        _ -> Nothing
        ZZDict -> case y of
                      SDict a2 -> Nothing
                      ZZDict -> Just Refl
                      _ -> Nothing
        _ -> Nothing

downVec ::
        forall a_k0 n_s0 .
          TypeDict a_k0 -> TypeDict n_s0 -> Vec a_k0 n_s0 -> Vec' a_k0
downVec !a_k0_dict !n_s0_dict !orig
  = case orig of
        Nil -> Nil'
        Cons a b -> Cons' a
                      (downVec (let a_dict = a_k0_dict in a_dict)
                         (let n_dict
                                = case n_s0_dict of
                                      SDict a -> a
                                      _ -> undefined
                            in n_dict)
                         b)

upVec :: forall a_k0 . Vec' a_k0 -> SealedVec a_k0
upVec !lower
  = case lower of
        Nil' ->
                  let n_s0_dict = ZZDict in SealedVec n_s0_dict Nil
        Cons' a b ->
                     case upVec b of
                           SealedVec n_s0_b'_dict b' -> let n_dict = n_s0_b'_dict in
                                                          let n_s0_dict = SDict n_dict in
                                                            SealedVec n_s0_dict (Cons a b')


-- upVec :: forall a_k0 . TypeDict a_k0 -> Vec' a_k0 -> SealedVec a_k0
-- upVec !a_k0_dict !lower
--   = case lower of
--         Nil' -> let a_dict = a_k0_dict in
--                   let n_s0_dict = ZZDict in SealedVec n_s0_dict Nil
--         Cons' a b -> let a_dict = a_k0_dict in
--                        case upVec a_k0_dict b of
--                            SealedVec n_s0_b'_dict b' -> let n_dict = n_s0_b'_dict in
--                                                           let n_s0_dict = SDict n_dict in
--                                                             SealedVec n_s0_dict (Cons a b')

ghostbuster :: ()
ghostbuster = ()

main :: P.IO ()
main = seq ghostbuster (return ())
