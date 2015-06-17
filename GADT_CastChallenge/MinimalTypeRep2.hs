{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

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

deriving instance Show (TypeDict a)

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

instance Show Dyn where
  show (Dyn dict _) = "<dyn "++ show dict++">"

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

ex2 :: TypeDict (Int -> Bool)
ex2 = ArrDict IntDict BoolDict

ex2Dyn :: Dyn
ex2Dyn = Dyn ex2 (undefined :: Int -> Bool)

r :: (Int, Bool) :~: (Int, Bool)
Just r = teq ex1 ex1

--------------------------------------------------------------------------------

-- The above formulation of Dyn would allow us to do the basic list
-- example with SYNTHESIZED rather than CHECKED erasure:

data List a = Nil | Cons a (List a)
  deriving (Show,Eq,Read,Ord)

data List' = Nil' | Cons' Dyn List'
deriving instance Show List'

strip :: TypeDict a -> List a -> List'
strip _ Nil        = Nil'
strip d (Cons a l) = Cons' (Dyn d a) (strip d l)

-- Checked version:
restore1 :: TypeDict a -> List' -> Maybe (List a)
restore1 _ Nil'           = return Nil
restore1 d (Cons' x' xs') = do
  x  <- fromDyn d x'
  xs <- restore1 d xs'
  return (Cons x xs)

-- Similar but not the same as Dyn:
data SealedList = forall a . SealedList (TypeDict a) (List a)

-- Synthesized version.  Doesn't work for empty lists!
restore2 :: List' -> Maybe SealedList
-- restore2 Nil'  = Just $ SealedList (error) Nil
restore2 Nil' = error "restore2: ambiguous type!  Cannot restore empty list."
restore2 (Cons' (Dyn d x) rest) = loop d x rest
  where
  loop :: TypeDict a -> a -> List' -> Maybe SealedList
  loop d0 hd Nil' = Just $ SealedList d0 (Cons hd Nil)
  loop d1 hd (Cons' (Dyn d2 x2) rst) =
    do Refl <- teq d1 d2
       SealedList d3 ls <- loop d2 x2 rst
       Refl <- teq d2 d3
       return $ SealedList d3 (Cons hd ls)

showD :: TypeDict a -> a -> String
showD IntDict  x = show x
showD BoolDict x = show x
showD (ArrDict _ _) _ = "<arrow>"
showD (TupDict d1 d2) (a,b) =
      "("++showD d1 a++","
         ++showD d2 b++")"

toList :: [a] -> List a
toList []     = Nil
toList (x:xs) = x `Cons` toList xs

fromList :: List a -> [a]
fromList Nil = []
fromList (Cons x y) = x : fromList y

test :: Maybe (List Int)
test = restore1 IntDict $
       strip (IntDict) $
       toList [1..5]

test2 :: String
test2 =
  case x of
    Just (SealedList d l) ->
      unwords $ map (showD d) (fromList l)
 where
  x = restore2 $
      strip (IntDict) $
      toList [1..5]
