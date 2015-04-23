{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeFamilies        #-}


module ADT2 where

import Data.Typeable
import Text.Printf
import Unsafe.Coerce
import Prelude                                          hiding ( exp )

import qualified GADT2 as GADT

data Exp
  = B Bool
  | I Int
  | Add Exp Exp
  | If Exp Exp Exp
  | Let Exp Exp
  | Var Type Ix
  deriving (Eq, Show, Typeable)

type Ix = Int

data Type = TInt | TBool
  deriving (Eq, Typeable)

instance Show Type where
  show TInt  = "Int"
  show TBool = "Bool"


-- We can't write 'eval' for Exp because untyped languages are stupid.
--
-- eval :: Exp -> ??


--------------------------------------------------------------------------------
-- Option 2: The new way. Consumer demands the type and we downcast without ever
-- sealing.
--
-- TLM: oops...
--

idxToInt :: GADT.Idx env t -> Int
idxToInt GADT.ZeroIdx      = 0
idxToInt (GADT.SuccIdx ix) = 1 + idxToInt ix

-- Convert a well-typed expression into an untyped ADT
--
upcast :: forall env t. GADT.Exp env t -> Exp
upcast exp =
  case exp of
    GADT.Var ix       -> Var (upcastType (undefined::t)) (idxToInt ix)
    GADT.Let bnd body -> Let (upcast bnd) (upcast body)
    GADT.Add x y      -> Add (upcast x) (upcast y)
    GADT.If p t e     -> If (upcast p) (upcast t) (upcast e)
    GADT.Const c      -> case GADT.reify c of
                           GADT.EltR_Int  -> I c
                           GADT.EltR_Bool -> B c
                           -- TLM: ugh, this type reification method must be closed.

upcastType :: GADT.Elt t => t -> Type
upcastType x =
  case GADT.reify x of
    GADT.EltR_Int  -> TInt
    GADT.EltR_Bool -> TBool


-- Layouts map environments to index projections into that environment
--
data Layout env env' where
  EmptyLayout :: Layout env '[]
  PushLayout  :: Typeable t
              => GADT.Idx env t -> Layout env env' -> Layout env (t ': env')

incLayout :: Layout env env' -> Layout (t ': env) env'
incLayout EmptyLayout         = EmptyLayout
incLayout (PushLayout ix lyt) = PushLayout (GADT.SuccIdx ix) (incLayout lyt)


typeError :: forall s t a. (Typeable s, Typeable t) => s -> t -> a
typeError _ _
  = error
  $ printf "Couldn't match expected type `%s' with actual type `%s'"
           (show (typeOf (undefined::s)))
           (show (typeOf (undefined::t)))


-- Get an index out of the environment
--
downcastIdx :: forall t env env'. Typeable t => Int -> Layout env env' -> GADT.Idx env t
downcastIdx 0 (PushLayout (ix :: GADT.Idx env t') _)
  | Just ix' <- gcast ix        = ix'
  | otherwise                   = typeError (undefined::t) (undefined::t')
downcastIdx n (PushLayout _ lyt)  = downcastIdx (n-1) lyt
downcastIdx _ _                   = error "unbound variable"


data Sealed env where
  Sealed :: GADT.Elt t => GADT.Exp env t -> Sealed env

-- Convert an ADT into a well typed GADT.
-- This can fail because untyped languages are dumb.
--
downcast :: forall t. GADT.Elt t => Exp -> GADT.Exp '[] t
downcast exp = unseal (downcast' EmptyLayout exp)
  where
    resultTy = expType exp

    unseal (Sealed gadt)
      | expTypeRep resultTy == typeRep (Proxy :: Proxy t) = unsafeCoerce gadt
      | otherwise
      = case resultTy of
          TInt  -> typeError (undefined::t) (undefined::Int)
          TBool -> typeError (undefined::t) (undefined::Bool)

    -- Determine what the value level type of the expression should be. If the
    -- expression is ill-typed, this should be caught by the downcast process (??)
    --
    expType :: Exp -> Type
    expType (B _)       = TBool
    expType (I _)       = TInt
    expType (Add _ _)   = TInt
    expType (If _ x _)  = expType x
    expType (Let _ x)   = expType x
    expType (Var t _)   = t

    expTypeRep :: Type -> TypeRep
    expTypeRep TInt     = typeRep (Proxy :: Proxy Int)
    expTypeRep TBool    = typeRep (Proxy :: Proxy Bool)


downcast' :: forall env. Layout env env -> Exp -> Sealed env
downcast' lyt exp = cvt exp
  where
    cvt :: Exp -> Sealed env
    cvt (Var ty ix)     = case ty of
                            TInt  -> Sealed (GADT.Var (downcastIdx ix lyt) :: GADT.Exp env Int)
                            TBool -> Sealed (GADT.Var (downcastIdx ix lyt) :: GADT.Exp env Bool)
    cvt (I i)           = Sealed (GADT.Const i :: GADT.Exp env Int)
    cvt (B b)           = Sealed (GADT.Const b :: GADT.Exp env Bool)
    cvt (Add x y)
      | Sealed (x' :: GADT.Exp env x)   <- downcast' lyt x
      , Sealed (y' :: GADT.Exp env y)   <- downcast' lyt y
      , Just Refl                       <- unify (undefined :: x) (undefined :: Int)
      , Just Refl                       <- unify (undefined :: x) (undefined :: y)
      = Sealed (GADT.Add x' y')

    cvt (If p t e)
      | Sealed (p' :: GADT.Exp env p)   <- downcast' lyt p
      , Sealed (t' :: GADT.Exp env t)   <- downcast' lyt t
      , Sealed (e' :: GADT.Exp env e)   <- downcast' lyt e
      , Just Refl                       <- unify (undefined :: p) (undefined :: Bool)
      , Just Refl                       <- unify (undefined :: t) (undefined :: e)
      = Sealed (GADT.If p' t' e')

    cvt (Let x y)
      | Sealed (x' :: GADT.Exp env x)           <- downcast' lyt x
      , Sealed (y' :: GADT.Exp (x ': env) y)    <- downcast' (GADT.ZeroIdx `PushLayout` incLayout lyt) y
      = Sealed (GADT.Let x' y')

    cvt _
      = error "downcast failed"


-- Gain some type-level knowledge when two value-level types match
--
unify :: (Typeable s, Typeable t) => s -> t -> Maybe (s :~: t)
unify s t =
  case eqT of
    Nothing   -> typeError s t
    refl      -> refl
