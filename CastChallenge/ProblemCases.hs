{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A collection of small casses that may pose problems.

module ProblemCasess where
import Data.Dynamic
import Data.Typeable
import Text.Printf

import MinimalTypeRep2

--------------------------------------------------------------------------------
-- Ambiguity examples.
--------------------------------------------------------------------------------

-- Fails the ambiguity check:
data Foo a where
  Foo :: forall x . x -> Foo x
  -- Here x is an existential variable:
  Bar :: forall x y . Foo x -> Foo y
-- Errors:
-- deriving instance Show x => Show (Foo x)
instance Show (Foo x) where
  show (Foo _x) = "Foo"
  show (Bar x) = "Bar ("++ show x ++")"




t0 :: Foo Int
t0 = Bar (Foo 'a')

copy :: Foo a -> Foo a
copy (Foo x) = Foo x
copy (Bar x) = Bar (copy x)

t1 :: Foo'
t1 = Bar' (Foo' (toDyn 'a'))

t2 :: Foo y
t2 = Bar (Bar (Foo 'a'))

-- Nothing can recover a type for Bar's argument here:
data Foo' where
  Foo' :: Dynamic -> Foo'
  Bar' :: Foo' -> Foo'
 deriving Show

upFoo :: Typeable a => Foo' -> Maybe (Foo a)
upFoo (Foo' d) = do a <- fromDynamic d
                    return $ Foo a
upFoo (Bar' x) =
      do -- x' <- upFoo x -- Impossibl, ambiguity error.
         error "impossible"

-- Here's an alternative algorithm, where we deal with *any*
-- ambiguity, whether already present or introduced by erasure, by
-- introducing dictionaries:
data Foo'' where
  Foo'' :: TypeDict a -> a -> Foo''
  Bar'' :: TypeDict a -> Foo'' -> Foo''

-- But this approach runs into an impossibility too.  There's no way
-- for us to recover a dictionary for the existing existential.
downFoo'' :: TypeDict a -> Foo a -> Foo''
downFoo'' d (Foo a) = Foo'' d a
downFoo'' d (Bar a) =
  Bar'' d (downFoo'' (error "impossibility") a)
-- Should ghostbuster therefore disallow existentials in its input programs?
-- Or should it require that they have a TypeDict / Typeable instance?

-- | IF ghostbuster could search for and verify the presence of
-- preexisting TypeDict arguments, then it could handle a datatype
-- like this:
data Foo2 a where
  Foo2 :: forall x . x -> Foo2 x
  -- Here x is an existential variable, but we've got its Dict.
  Bar2 :: forall x y . TypeDict x -> Foo2 x -> Foo2 y

instance Show a => Show (Foo2 a) where
  show (Foo2 x) = "Foo " ++ show x
  show (Bar2 d x) = "Bar ("++ loop d x++")"
    where
     loop :: forall x . TypeDict x -> Foo2 x -> String
     loop dt (Foo2 a) = "Foo "++ showD dt a
     loop d1 (Bar2 d2 a) = "Bar ("++ loop d2 a ++") :: Foo2 "++show d1

instance Show Foo'' where
  show (Foo'' d a) = "Foo "++ show d ++ " "++ showD d a
  show (Bar'' d a) = "Bar ("++ show a ++ " :: Foo'' "++show d++")"

downFoo2 :: TypeDict a -> Foo2 a -> Foo''
downFoo2 d (Foo2 a)     = Foo'' d a
downFoo2 _d1 (Bar2 d2 a) = Bar'' d2 (downFoo2 d2 a)

upFoo2 :: TypeDict a -> Foo'' -> Maybe (Foo2 a)
upFoo2 d1 (Foo'' d2 a) =
  do Refl <- teq d1 d2
     return $ Foo2 a
upFoo2 (_d1::TypeDict res) (Bar'' d2 a) =
  do a' <- upFoo2 d2 a
     return (Bar2 d2 a' :: Foo2 res)

t3 :: Foo2 Int
t3 = (Bar2 BoolDict (Bar2 IntDict (Foo2 3)))

t3' :: Foo''
t3' = downFoo2 IntDict t3

t3'' :: Maybe (Foo2 Int)
t3'' = upFoo2 IntDict t3'

t4 :: Foo2 Int
t4 = (Foo2 3)

t4' :: Foo''
t4' = downFoo2 IntDict t4

t4'' :: Maybe (Foo2 Int)
t4'' = upFoo2 IntDict t4'


t5 :: Foo2 Bool
t5 = Bar2 IntDict (Foo2 3)

t5' :: Foo''
t5' = downFoo2 BoolDict t5

t5'' :: Maybe (Foo2 Bool)
t5'' = upFoo2 BoolDict t5'

--------------------------------------------------------------------------------
-- How about erased variables flowing to kept phantom positions?
--------------------------------------------------------------------------------

data A x where
  A :: (B x) -> A x
  deriving Show

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

-- | We could disallow this scenario, but in some sense it is even
-- *easier* to cast types with phantom vars:
up_A :: Typeable x => A' -> Maybe (A x)
up_A (A' (B i))  =
  Just $ A (B i)

t8 :: Maybe (A Char)
t8 = up_A (A' (B 3))

-- | In the other version of the Ghostbuster algorithm, instead of
-- replacing a with Dyn or Empty, we would let it become an
-- existential type var and include the dictionary:
data A'' where
  A'' :: forall a . TypeDict a -> B a -> A''

downA'' :: TypeDict x -> A x -> A''
downA'' d (A b) = A'' d b

upA'' :: TypeDict x -> A'' -> Maybe (A x)
upA'' d1 (A'' d2 b) =
  do Refl <- teq d1 d2
     return $ A b

t9 :: Maybe (A Int)
t9 = upA'' IntDict $ downA'' IntDict (A (B 3))

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

--------------------------------------------------------------------------------

data Bad a where
  Leaf :: x -> Bad x
  Wrap :: Bad x -> Bad y -> Bad y

-- deriving instance Show y => (Show (Bad y))  -- Could not deduce (Show x).

copyBad :: Bad a -> Bad a
copyBad (Leaf x) = Leaf x
copyBad (Wrap x y) = Wrap (copyBad x) (copyBad y)

data Bad' where
  Leaf' :: Typeable x => x -> Bad'
  Wrap' :: Bad' -> Bad' -> Bad'

downBad :: Typeable a => Bad a -> Bad'
downBad (Leaf x)   = Leaf' x
downBad (Wrap x y) = Wrap' (undefined) (downBad y) -- We don't have the Typeable constraint for downBad x.

data Good a where
  GLeaf :: x -> Good x
  GWrap :: Typeable x => Good x -> Good y -> Good y

data Good' where
  GLeaf' :: Typeable x => x -> Good'
  GWrap' :: Good' -> Good' -> Good'

-- deriving instance (Show (Good'))  -- Still no (Show x) of course

downGood :: Typeable a => Good a -> Good'
downGood (GLeaf x)   = GLeaf' x
downGood (GWrap x y) = GWrap' (downGood x) (downGood y)
