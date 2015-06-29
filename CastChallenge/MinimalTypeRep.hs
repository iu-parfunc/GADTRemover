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

module MinimalTypeRep where

-- import GHC.Prim (BOX, OpenKind)
-- import Data.Type.Equality ((:~:)(..))

type role (:~:) nominal nominal
data (:~:) (a :: k) (b :: k) where
  Refl :: a1 :~: a1

data TypeRep

data TypeDict a

rep :: TypeDict a -> TypeRep
rep = undefined

-- | Normally, this kind of thing is done by the type class system
-- automatically:
mkArr :: TypeDict a -> TypeDict b -> TypeDict (a -> b)
mkArr = undefined

splitRep :: TypeRep -> (String, [TypeRep])
splitRep = undefined

tcast :: TypeDict a -> TypeDict b -> a -> Maybe b
tcast = undefined

tcast1 :: -- forall (k :: BOX) (a :: k) (b :: k) (c :: k -> *) .
          forall a b c .
          TypeDict a -> TypeDict b -> c a -> Maybe (c b)
tcast1 = undefined

teq :: TypeDict a -> TypeDict b -> Maybe (a :~: b)
teq = undefined

recoverDict :: TypeRep -> (forall a. TypeDict a -> ans) -> ans
recoverDict = undefined

----------------------------------------
-- Example application of the above API:

-- | Witness the arrow-ness of a type.
data TypeCaseArrow t where
  TypeCaseArrow :: forall a b c . TypeDict b -> TypeDict c ->
                   (a :~: (b -> c)) -> TypeCaseArrow a


-- | Test a Typeable type to see if it is an arrow.  If so, return a
-- data structure capable of witnessing that fact for the GHC type checker.
typeCaseArrow :: forall arr. (TypeDict arr) -> Maybe (TypeCaseArrow arr)
typeCaseArrow dictArr = case splitRep (rep dictArr) of
  ("->", [b,c]) ->
{-
    recoverDict b (\(db :: TypeDict (b)) ->
    recoverDict c (\(dc :: TypeDict c) ->
    -- fmap TypeCaseArrow (tcast Refl :: Maybe (arr :~: (b -> c)))
    let dbc :: TypeDict ((->) b c)
        dbc = undefined
        _ = (teq db dc :: Maybe (arr :~: (b -> c))) in
    undefined
    ))
-}
-- Problems here: Extra kind signatures needed.
-----------------
-- The second argument of ‘Data.Type.Equality.:~:’
--   should have kind ‘OpenKind’,
--   but ‘b’ has kind ‘k’

    recoverDict b (\db -> recoverDict c (\dc -> g db dc dictArr (mkArr db dc)))
    where
        g :: forall (b :: *) (c :: *) (arrow :: *) .
             TypeDict b -> TypeDict c -> TypeDict arrow -> TypeDict (b -> c) ->
             Maybe (TypeCaseArrow arrow)
        g db dc darr dbc =
           case teq darr dbc :: Maybe (arrow :~: ((->) b c)) of
              Nothing -> Nothing
              Just refl -> Just $ TypeCaseArrow db dc refl

  _ -> Nothing
