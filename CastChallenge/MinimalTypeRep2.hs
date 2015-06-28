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

-- But... for List this is well beyond what Ghostbuster can/should do
-- because the Nil constructor fails the ambiguity check for
-- synthesized vars.

-- For non-empty lists, however, things work out fine.

data List a where
  -- Both these constructors are non-ambiguous both for checked mode and synthesized:
  One  :: a -> List a
  Cons :: a -> (List a) -> List a
  deriving (Show,Eq,Read,Ord)

data List' = One' Dyn | Cons' Dyn List'
deriving instance Show List'

strip :: TypeDict a -> List a -> List'
strip d (One x)    = One' (Dyn d x)
strip d (Cons a l) = Cons' (Dyn d a) (strip d l)

-- Checked version:
restore1 :: TypeDict a -> List' -> Maybe (List a)
restore1 d (One' x)       = (fmap One (fromDyn d x))
restore1 d (Cons' x' xs') = do
  x  <- fromDyn d x'
  xs <- restore1 d xs'
  return (Cons x xs)

-- Similar but not the same as Dyn:
data SealedList = forall a . SealedList (TypeDict a) (List a)

-- Synthesized version.  Doesn't work for empty lists!
restore2 :: List' -> Maybe SealedList
-- restore2 Nil'  = Just $ SealedList (error) Nil
restore2 (One' (Dyn d x)) = Just $ SealedList d (One x)
restore2 (Cons' (Dyn d x) rest) = loop d x rest
  where
  loop :: TypeDict a -> a -> List' -> Maybe SealedList
  loop d0 hd (One' (Dyn d1 y)) =
    do Refl <- teq d1 d0
       return $ SealedList d0 (Cons hd (One y))
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
toList []     = error "Can't make non-empty list from list"
toList [x]    = One x
toList (x:xs) = x `Cons` toList xs

fromList :: List a -> [a]
fromList (One x) = [x]
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


-----------------------------------------------------------------------------------
-- Here's something else that's fun:
-- TypeRep should be basically the ghostbusted TypeDict:
-----------------------------------------------------------------------------------

data TypeDict' where
  IntDict'  :: TypeDict'
  BoolDict' :: TypeDict'
  ArrDict'  :: TypeDict' -> TypeDict' -> TypeDict'
  TupDict'  :: TypeDict' -> TypeDict' -> TypeDict'

downDict :: TypeDict a -> TypeDict'
downDict x =
  case x of
   IntDict  -> IntDict'
   BoolDict -> BoolDict'
   (ArrDict y1 y2) -> ArrDict' (downDict y1) (downDict y2)
   (TupDict y1 y2) -> TupDict' (downDict y1) (downDict y2)

-- It supports synthesized or checked.  Here's the synth one:
data SealedDict = forall a . SealedDict (TypeDict a)

upDict :: TypeDict' -> Maybe SealedDict
upDict x =
 case x of
   IntDict'  -> Just $ SealedDict IntDict
   BoolDict' -> Just $ SealedDict BoolDict
   (ArrDict' y1 y2) ->
     do SealedDict d1 <- upDict y1
        SealedDict d2 <- upDict y2
        return $ SealedDict $ ArrDict d1 d2
   (TupDict' y1 y2) ->
     do SealedDict d1 <- upDict y1
        SealedDict d2 <- upDict y2
        return $ SealedDict $ TupDict d1 d2

ex1' :: String
ex1' =
  case upDict (downDict ex1) of
   Just (SealedDict d) -> show d
   Nothing -> ""
