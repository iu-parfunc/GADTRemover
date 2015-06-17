{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

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

-- This clearly fails the ambiguity check for "synthesize".
-- But, because we're not erasing the var in this case, it's fine.
data B a where
  B :: Int -> B x
  deriving Show

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

-----------------------------------------------
-- And with existentials ...

data C a where
  C :: forall a b . (D b a) -> C a

deriving instance Show (C a)
-- deriving instance Eq (C a) -- Gets a type error
instance Eq (C a) where
  C D == C D = True

data D b a = D
 deriving (Show,Eq)

data C' where
  C' :: forall b . (D b Dynamic) -> C'

deriving instance Show C'

castD1 :: D a b -> D c b
castD1 D = D

-- In general castD will have to be replaced with something that
-- actually copies the value.  Dynamic is not
-- representation-equivalent to the types it replaces.
castD :: D a b -> D c d
castD D = D

upC :: forall x . Typeable x => C' -> Maybe (C x)
upC (C' d) = Just $ C d'
  where
  -- Problem: we have no idea what the existential type `b` was!
  -- How can we rebuild it without some kind of TypeRep?
  --
  -- But... by parametricity, we can say that this doesn't matter
  -- and concern ourselves only with constraints on existential vars, right?
  d' :: D Empty x
  d' = (castD d)

downC :: Typeable a => C a -> C'
downC (C d) = C' (castD d)

c :: C Float
c = C (D :: D Int Float)

c' :: C'
c' = downC c

c'' :: Maybe (C Float)
c'' = upC c'
