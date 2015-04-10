{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeOperators       #-}

module ADT1 where

import Data.Proxy
import Data.Dynamic
import Data.Typeable
import Text.Printf
import Data.Type.Equality

import qualified GADT

--------------------------------------------------------------------------------
-- (1): A simple ADT version of the language

-- | Strip all phantom type args.
--
-- RRN: BUT... it could reify them all to the value level instead?
--
data Exp
  = T
  | F
  | If Exp Exp Exp
  | Lit Int
  | Add Exp Exp
  | Let Exp Exp
  | Var Idx
  deriving (Show, Typeable)

-- | Reify the type arg to the value level.
--
-- TLM: maybe we can simplify this further as just an Int
--
data Idx
  = Zero GADT.Ty
  | Succ GADT.Ty Idx
  deriving (Show, Typeable)


--------------------------------------------------------------------------------
-- (2): DOWNCAST
--
-- Downcasting never fails.  It strips type-level information or
-- reifies it to the value level.
--


downcast :: GADT.ReifyTy a => GADT.Exp env a -> Exp
downcast e =
  case e of
    GADT.Lit n     -> Lit n
    GADT.T         -> T
    GADT.F         -> F
    GADT.If a b c  -> If  (downcast a) (downcast b) (downcast c)
    GADT.Add a b   -> Add (downcast a) (downcast b)
    GADT.Let a b   -> Let (downcast a) (downcast b)
    GADT.Var ix    -> Var (downcastIdx ix)

downcastIdx
  :: forall env e . GADT.ReifyTy e
  => GADT.Idx env e
  -> Idx
downcastIdx ix =
  case ix of
    GADT.Zero
      -> Zero (GADT.reifyTy (Proxy :: Proxy (GADT.ENV_HEAD env)))

    GADT.Succ (inner :: GADT.Idx env' e')
      -> Succ (GADT.reifyTy (Proxy :: Proxy (GADT.ENV_HEAD env)))
              (downcastIdx inner)


--------------------------------------------------------------------------------
-- (3): UPCAST
--
-- Attempt to generate a fully typed GADT from our value-level-only ADT. This can fail.
--

-- Option 1: the old way. Sealed, monomorphic data and Data.Dynamic.

-- Typeable constraints are actually redundant here, because the kind
-- of 'env' and 'a' should imply Typeable, but we have no way to
-- express that.
--
{--
data Sealed = forall env a . (Typeable env, GADT.ReifyTy a) =>
             Sealed (GADT.Exp env a)

data SealedIdx = forall env a . (Typeable env, GADT.ReifyTy a) =>
                 SealedIdx (GADT.Idx env a)

data SealedTy = forall (t :: GADT.Ty) . GADT.ReifyTy t =>
                SealedTy (Proxy t)
--}

data Sealed where
  Sealed :: (Typeable env, GADT.ReifyTy t)
         => GADT.Exp env t
         -> Sealed

data SealedIdx where
  SealedIdx :: (Typeable env, GADT.ReifyTy t)
            => GADT.Idx env t
            -> SealedIdx

data SealedTy where
  SealedTy :: GADT.ReifyTy t
           => Proxy (t :: GADT.Ty)
           -> SealedTy

deriving instance Show Sealed
deriving instance Show SealedIdx
deriving instance Show SealedTy

-- | The inverse of reifyTy: value to type level.
toType :: GADT.Ty -> SealedTy
toType GADT.IntTy  = SealedTy (Proxy :: Proxy 'GADT.IntTy)
toType GADT.BoolTy = SealedTy (Proxy :: Proxy 'GADT.BoolTy)
toType GADT.AnyTy  = SealedTy (Proxy :: Proxy 'GADT.AnyTy)


-- upcastIdx :: Typeable a => Idx2 -> Idx env a
upcastIdx :: Idx -> SealedIdx
upcastIdx (Zero ty)
  | SealedTy (_ :: Proxy e) <- toType ty
  = SealedIdx (GADT.Zero :: GADT.Idx ('GADT.Extend e 'GADT.EmptyEnv) e)

upcastIdx (Succ ty ix)
  | SealedTy  (_   :: Proxy tty)        <- toType ty
  , SealedIdx (ix' :: GADT.Idx env' t') <- upcastIdx ix
  = SealedIdx (GADT.Succ ix' :: GADT.Idx ('GADT.Extend tty env') t')


unifyEnv
  :: (Typeable env1, Typeable env2)
  => GADT.Exp (env1 :: GADT.Env) a
  -> GADT.Exp (env2 :: GADT.Env) b
  -> Maybe (env1 :~: env2)
unifyEnv _ _ = gcast Refl

unifyExp
  :: forall a b env. (GADT.ReifyTy a, GADT.ReifyTy b)
  => GADT.Exp env (a :: GADT.Ty)
  -> GADT.Exp env (b :: GADT.Ty)
  -> Maybe (a :~: b)
unifyExp _ _ = unify (Proxy :: Proxy a) (Proxy :: Proxy b)


unify
  :: (GADT.ReifyTy a, GADT.ReifyTy b)
  => Proxy a
  -> Proxy b
  -> Maybe (a :~: b)
unify a b | GADT.reifyTy a == GADT.reifyTy b = gcast Refl
unify _ _                                    = Nothing


-- | Upcast converts from less to more strongly typed, which may fail.
--
upcast
   :: (Typeable t, Typeable env)
   => Exp
   -> Maybe (GADT.Exp env t)
upcast exp
  | Just (Sealed e) <- cvt exp = fromDynamic (toDyn e)  -- TLM: this looks real dodgy...
  | otherwise                  = Nothing
  where
    cvt :: Exp -> Maybe Sealed
    cvt T           = Just $ Sealed (GADT.T     :: GADT.Exp GADT.EmptyEnv GADT.BoolTy)
    cvt F           = Just $ Sealed (GADT.F     :: GADT.Exp GADT.EmptyEnv GADT.BoolTy)
    cvt (Lit x)     = Just $ Sealed (GADT.Lit x :: GADT.Exp GADT.EmptyEnv GADT.IntTy)
    cvt (If p t e)
      -- First, convert the subexpressions
      | Just (Sealed (p' :: GADT.Exp env1 p)) <- cvt p
      , Just (Sealed (t' :: GADT.Exp env2 t)) <- cvt t
      , Just (Sealed (e' :: GADT.Exp env3 e)) <- cvt e
      -- Second, ensure the types unify
      , Just Refl                      <- unifyEnv p' t'
      , Just Refl                      <- unifyEnv p' e'
      , Just Refl                      <- unifyExp t' e'
      , Just Refl                      <- unifyExp p' (undefined :: GADT.Exp env1 'GADT.BoolTy)
      = Just . Sealed $ GADT.If p' t' e'

    cvt (Add x y)
      | Just (Sealed (x' :: GADT.Exp env1 x)) <- cvt x
      , Just (Sealed (y' :: GADT.Exp env2 y)) <- cvt y
      , Just Refl                      <- unifyEnv x' y'
      , Just Refl                      <- unifyExp x' y'
      , Just Refl                      <- unifyExp x' (undefined :: GADT.Exp env1 'GADT.IntTy)
      = Just . Sealed $ GADT.Add x' y'

    cvt (Var ix)
      | SealedIdx ix' <- upcastIdx ix
      = Just . Sealed $ GADT.Var ix'

    cvt (Let bnd body)
      | Just (Sealed (bnd'  :: GADT.Exp env1 bnd))  <- cvt bnd
      , Just (Sealed (body' :: GADT.Exp env2 body)) <- cvt body
      , Just Refl                            <- unifyEnv body' (undefined :: GADT.Exp (GADT.Extend bnd env1) body)
      = Just . Sealed $ GADT.Let bnd' body'

    cvt _
      = Nothing

{--
safeCast :: forall a b . (Typeable a, Typeable b) => a -> b
safeCast a =
  case fromDynamic (toDyn a) of
    Just x  -> x
    Nothing -> error $ printf "safeCast failed, from %s to %s"
                          (show (typeOf (unused :: a)))
                          (show (typeOf (unused :: b)))
--}

unused :: a
unused = error "This value should not be used"

