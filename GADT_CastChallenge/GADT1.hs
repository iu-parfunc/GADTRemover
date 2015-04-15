{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE PolyKinds                 #-}      -- For Typeable of Extend:
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeFamilies              #-}

-- This module define a GADT for a simple expression language that contains lots
-- of type level information. We will use this datatype as our example for
-- converting into a simpler ADT, and then (hopefully) back again.
--
module GADT1 where

import Data.Typeable

--------------------------------------------------------------------------------
-- (*) Types

-- | Simplest version.  Use a closed world of value types in the Exp:
--
-- The way Accelerate, for example, does this is more complicated, using a class
-- for value types which can reify them.
--
data Ty = BoolTy | IntTy | AnyTy
  deriving (Eq, Show, Typeable)

deriving instance (Typeable 'BoolTy)
deriving instance (Typeable 'IntTy)
deriving instance (Typeable 'AnyTy)

class Typeable t => ReifyTy t where
  reifyTy :: Proxy t -> Ty

instance ReifyTy 'BoolTy where reifyTy _ = BoolTy
instance ReifyTy 'IntTy  where reifyTy _ = IntTy
instance ReifyTy 'AnyTy  where reifyTy _ = AnyTy

--------------------------------------------------------------------------------
-- (*) Environments

data Env = EmptyEnv | Extend Ty Env

deriving instance Typeable 'EmptyEnv
deriving instance Typeable 'Extend

type family   ENV_HEAD (t::Env) :: Ty
type instance ENV_HEAD ('Extend s e) = s

--------------------------------------------------------------------------------
-- (1) GADT based AST

-- TLM: How do you write an evaluator for this?
--
data Exp (env :: Env) (a :: Ty) where
  B   :: Bool -> Exp env 'BoolTy
  I   :: Int  -> Exp env 'IntTy
  If  :: Exp env BoolTy -> Exp env a -> Exp env a -> Exp env a
  Add :: Exp env IntTy -> Exp env IntTy -> Exp env IntTy
  Let :: ReifyTy bnd
      => Exp env bnd
      -> Exp (Extend bnd env) body
      -> Exp env body
  Var :: Idx env a -> Exp env a
  deriving Typeable

data Idx (env :: Env) (t :: Ty) where
  -- Here, again, ReifyTy is redundant, but no way to tell GHC that:
  Zero :: forall (env :: Env) (t::Ty) . ReifyTy t =>
          Idx (Extend t env) t
  Succ :: forall (env :: Env) (s :: Ty) (t :: Ty) . ReifyTy s =>
          Idx env t -> Idx (Extend s env) t
  deriving Typeable

deriving instance (Show (Exp env a))
deriving instance (Show (Idx env t))
