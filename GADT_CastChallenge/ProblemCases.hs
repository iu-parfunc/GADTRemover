{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}

-- | A collection of small casses that may pose problems.

module ProblemCasess where
import Data.Dynamic
import Data.Typeable
import Text.Printf

--------------------------------------------------------------------------------

data Foo x where
  Foo :: x -> Foo x
  Bar :: Foo x -> Foo y

-- deriving instance Show x => Show (Foo x)

t0 :: Foo Int
t0 = Bar (Foo 'a') 

t1 = Bar' (Foo' (toDyn 'a'))


data Foo' where
  Foo' :: Dynamic -> Foo'
  Bar' :: Foo' -> Foo'
 deriving Show

--------------------------------------------------------------------------------

