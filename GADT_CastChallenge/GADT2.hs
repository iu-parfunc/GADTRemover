{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module GADT2 where

import Data.Typeable
import Prelude                                          hiding ( exp )

data Idx env t where
  ZeroIdx ::              Idx (t ': env) t
  SuccIdx :: Idx env t -> Idx (s ': env) t

data Env env where
  EmptyEnv ::                 Env '[]
  PushEnv  :: a -> Env env -> Env (a ': env)

data Exp env t where
  Const :: Elt t => t -> Exp env t
  Add   :: Exp env Int -> Exp env Int -> Exp env Int
  If    :: Elt a => Exp env Bool -> Exp env a -> Exp env a -> Exp env a
  Var   :: Elt t => Idx env t -> Exp env t
  Let   :: (Elt a, Elt b) => Exp env a -> Exp (a ': env) b -> Exp env b

deriving instance Show (Exp env t)
deriving instance Show (Idx env t)

prj :: Idx env t -> Env env -> t
prj ZeroIdx      (PushEnv x _)   = x
prj (SuccIdx ix) (PushEnv _ env) = prj ix env
prj _            _               = error "impossible evaluation"

eval :: Exp '[] t -> t
eval = eval' EmptyEnv

eval' :: Env env -> Exp env t -> t
eval' env exp =
  case exp of
    Const c         -> c
    Add x y         -> (eval' env x) + (eval' env y)
    If p t e
      | eval' env p -> eval' env t
      | otherwise   -> eval' env e
    Var ix          -> prj ix env
    Let x y         -> eval' (PushEnv (eval' env x) env) y

{-
data family EltR a :: *
data instance EltR Int  = EltR_Int
data instance EltR Bool = EltR_Bool
-}

data EltR a where
  EltR_Int  :: EltR Int
  EltR_Bool :: EltR Bool

class (Typeable a, Show a) => Elt a where
  reify :: a -> EltR a

instance Elt Int  where reify _ = EltR_Int
instance Elt Bool where reify _ = EltR_Bool

-- Tests

p0 :: Exp '[] Int
p0 = If (Const True) (Const 3) (Const 4)

p1 :: Exp '[] Int
p1 = Let (Const 5) (Var ZeroIdx)

p2 :: Exp '[] Int
p2 = If (Const True) (Const 11) p1

p3 :: Exp '[] Int
p3 = Let (Const 5) (If (Const True) (Var ZeroIdx) (Const 4))

p4 :: Exp '[] Int
p4 = Let (Const 4)
   $ Let (Const 5)
   $ Add (Var ZeroIdx)
         (Var (SuccIdx ZeroIdx))

