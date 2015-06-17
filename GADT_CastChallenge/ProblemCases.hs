{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}

-- | A collection of small casses that may pose problems.

module ProblemCasess where
import Data.Dynamic
import Data.Typeable
import Text.Printf

--------------------------------------------------------------------------------
-- Ambiguity examples.
--------------------------------------------------------------------------------

-- Fails the ambiguity check:
data Foo a where
  Foo :: x -> Foo x
  Bar :: Foo x -> Foo y

-- deriving instance Show x => Show (Foo x)

t0 :: Foo Int
t0 = Bar (Foo 'a')

t1 = Bar' (Foo' (toDyn 'a'))

-- Nothing can recover a type for Bar's argument here:
data Foo' where
  Foo' :: Dynamic -> Foo'
  Bar' :: Foo' -> Foo'
 deriving Show

--------------------------------------------------------------------------------
-- How about erased variables flowing to kept phantom positions?
--------------------------------------------------------------------------------

data A x = A (B x) deriving Show

data B a = B Int deriving Show

-- Ghostbust A.x, checked:
data A' = A' (B Empty)
-- "Empty" here could also be Dynamic for consistency.
-- data A' = A' (B Dynamic)

data Empty

-- We could disallow this scenario, but in some sense it is even
-- *easier* to cast types with phantom vars:
up_A :: Typeable x => A' -> Maybe (A x)
up_A (A' (B i))  =
  Just $ A (B i)

t2 :: Maybe (A Char)
t2 = up_A (A' (B 3))
