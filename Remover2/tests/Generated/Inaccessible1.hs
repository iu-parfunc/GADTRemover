
-- Corresponds to "codegenAllProgs7"
{-# OPTIONS_GHC -fdefer-type-errors #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Generated.Inaccessbile1 where
import Prelude hiding (Int, Maybe(..), Bool(..))
import qualified Prelude as P

data TypeDict a where
        ArrowTyDict :: TypeDict a -> TypeDict b -> TypeDict (ArrowTy a b)
        IntDict :: TypeDict Int

data TyEquality a b where
        Refl :: TyEquality a a

data ArrowTy a b where

data Int where
        One :: Int
        Two :: Int
        Three :: Int
  deriving Show

data Maybe a where
        Just :: a -> Maybe a
        Nothing :: Maybe a

data Bool where
        True :: Bool
        False :: Bool
  deriving Show

data Tup2 a b where
        Tup2 :: a -> b -> Tup2 a b

checkTEQ :: TypeDict t -> TypeDict u -> Maybe (TyEquality t u)
checkTEQ x y
  = case x of
        ArrowTyDict a1 b1 -> case y of
                                 ArrowTyDict a2 b2 -> case checkTEQ a1 a2 of
                                                          Just Refl -> case checkTEQ b1 b2 of
                                                                           Just Refl -> Just Refl
                                                                           Nothing -> Nothing
                                                          Nothing -> Nothing
                                 IntDict -> Nothing
        IntDict -> case y of
                       ArrowTyDict a2 b2 -> Nothing
                       IntDict -> Just Refl

ghostbuster
  = case checkTEQ IntDict (ArrowTyDict IntDict IntDict) of
        Just Refl -> True
        Nothing -> False

--------------------------------------------------------------------------------
-- Note, this is fine:

bar :: Bool
bar =
 let foo d =
       case checkTEQ IntDict d of
         Just Refl -> True
         Nothing -> False
 in foo (ArrowTyDict IntDict IntDict)

baz :: Bool
baz =
 ((\d -> case checkTEQ IntDict d of
           Just Refl -> True
           Nothing -> False)
  (ArrowTyDict IntDict IntDict))
