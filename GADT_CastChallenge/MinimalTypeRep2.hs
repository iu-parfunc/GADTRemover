{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | For our formal language we don't want to get into the type class
-- business.  Instead we want a minimal set of TypeRep/TypeableDict
-- operations.

module MinimalTypeRep2 where

-- import GHC.Prim (BOX, OpenKind)
import Data.Type.Equality as E

-- | These cases are just an example.  TypeDict in the formalism is an
-- open union.
data TypeDict a where
  IntDict  :: TypeDict Int
  BoolDict :: TypeDict Bool
  ArrDict  :: TypeDict a -> TypeDict b -> TypeDict (a -> b)
  TupDict  :: TypeDict a -> TypeDict b -> TypeDict (a,b)

cast :: TypeDict a -> TypeDict b -> a -> Maybe b
cast d1 d2 a =
  case teq d1 d2 of
    Just refl -> Just $ E.castWith refl a
    Nothing -> Nothing

-- | This would need to be synthesized appropriately based on the
-- final contents of the TypeDict sum.
teq :: TypeDict a -> TypeDict b -> Maybe (a :~: b)
teq IntDict IntDict   = Just Refl
teq BoolDict BoolDict = Just Refl
teq (ArrDict a b) (ArrDict x y)
  | Just Refl <- teq a x
  , Just Refl <- teq b y = Just Refl
teq (TupDict a b) (TupDict x y)
  | Just Refl <- teq a x
  , Just Refl <- teq b y = Just Refl
teq _ _ = Nothing

--------------------------------------------------------------------------------

data Dyn where
 Dyn :: forall a . TypeDict a -> a -> Dyn

fromDyn :: TypeDict t -> Dyn -> Maybe t
fromDyn dict1 (Dyn dict2 x) = cast dict2 dict1 x

--------------------------------------------------------------------------------

test1 :: Maybe Int
test1 = fromDyn IntDict dyn1

dyn1 :: Dyn
dyn1 = Dyn IntDict 3

dyn2 :: Dyn
dyn2 = Dyn BoolDict True

ex1 :: TypeDict (Int, Bool)
ex1 = TupDict IntDict BoolDict

r :: (Int, Bool) :~: (Int, Bool)
Just r = teq ex1 ex1
