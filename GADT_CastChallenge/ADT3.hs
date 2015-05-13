{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module ADT3
  where

import Prelude                                  hiding ( exp )
import Data.Maybe
import Data.Typeable
import Text.Printf
import qualified GADT3                          as GADT


-- Untyped definition
-- ==================

-- Type representation
-- -------------------

data Type
  = TUnit
  | TInt
  | TBool
  | TFloat
  | TTup [Type]
  deriving (Eq, Show)

data Val
  = VUnit
  | VInt Int
  | VBool Bool
  | VFloat Float
  | VTup [Val]
  deriving Eq

instance Show Val where
  show VUnit      = "()"
  show (VInt x)   = show x
  show (VFloat x) = show x
  show (VBool x)  = show x
  show (VTup t)   =
    case t of
      [a,b]   -> show (a,b)
      [a,b,c] -> show (a,b,c)
      _       -> error "VTup: only expected up to 3-tuple"


-- TLM: We could also encode the full type hierarchy, and/or keep the binary
--      tree encoding of tuples.
--
-- data Type         = TZero | TScalar ScalarType | TCons Type Type
--
-- data ScalarType   = NumType | NonNumType
-- data NumType      = IntegralType | FloatingType
-- data IntegralType = TInt
-- data FloatingType = TFloat
-- data NonNumType   = TUnit | TBool


-- Language definition
-- -------------------

type Idx = Int
type ProdIdx = Int

data Exp
  = Let (Type,Exp) Exp
  | Var Type Idx                -- cons indexing!
  | Const Type Val
  | Prj Type ProdIdx Exp        -- snoc indexing!
  | Prod Type [Exp]
  | If Exp Exp Exp
  | PrimApp PrimFun Exp
  deriving (Eq, Show)

data PrimFun
  = PrimAdd Type
  | PrimMul Type
  | PrimToFloat
  deriving (Eq, Show)


-- Interpreter
-- -----------

type Env = [Val]

eval :: Exp -> Val
eval = evalOpenExp []

evalOpenExp :: Env -> Exp -> Val
evalOpenExp env = go
  where
    go :: Exp -> Val
    go (Let (_,a) b)    = evalOpenExp (go a : env) b
    go (Var _ ix)       = env !! ix             -- assert type! cons indexing!
    go (Const _ c)      = c                     -- assert type!
    go (Prod _ p)       = VTup $ map go p
    go (Prj _ ix p)     = prj ix (go p)
    go (If p t e)       = if_ (go p) (go t) (go e)
    go (PrimApp f x)    = case f of
                            PrimAdd t   -> add t (go x)
                            PrimMul t   -> mul t (go x)
                            PrimToFloat -> toFloat (go x)

    prj :: ProdIdx -> Val -> Val
    prj ix (VTup vs) = reverse vs !! ix         -- snoc indexing!
    prj _ _          = error "Prj: expected tuple"

    if_ :: Val -> Val -> Val -> Val
    if_ (VBool True)  x _ = x
    if_ (VBool False) _ x = x
    if_ _ _ _             = error "If: incorrect arguments"

    add :: Type -> Val -> Val
    add TInt   (VTup [VInt x,   VInt y])   = VInt   (x+y)
    add TFloat (VTup [VFloat x, VFloat y]) = VFloat (x+y)
    add _ _                                = error "PrimAdd: incorrect arguments"

    mul :: Type -> Val -> Val
    mul TInt   (VTup [VInt x,   VInt y])   = VInt   (x*y)
    mul TFloat (VTup [VFloat x, VFloat y]) = VFloat (x*y)
    mul _ _                                = error "PrimMul: incorrect arguments"

    toFloat :: Val -> Val
    toFloat (VInt x) = VFloat (fromIntegral x)
    toFloat _        = error "PrimToFloat: incorrect arguments"


-- Upcasting
-- =========
--
-- So long as the untyped expression language has enough constructs to cover all
-- features of the typed language, upcasting always succeeds: it only throws out
-- information, or downgrades it from the type to value level.
--

-- Types

upcastScalarType :: GADT.ScalarType a -> Type
upcastScalarType (GADT.NumScalarType t)    = upcastNumType t
upcastScalarType (GADT.NonNumScalarType t) = upcastNonNumScalarType t

upcastNumType :: GADT.NumType t -> Type
upcastNumType (GADT.IntegralNumType t) = upcastIntegralNumType t
upcastNumType (GADT.FloatingNumType t) = upcastFloatingNumType t

upcastIntegralNumType :: GADT.IntegralType t -> Type
upcastIntegralNumType GADT.TypeInt{} = TInt

upcastFloatingNumType :: GADT.FloatingType t -> Type
upcastFloatingNumType GADT.TypeFloat{} = TFloat

upcastNonNumScalarType :: GADT.NonNumType t -> Type
upcastNonNumScalarType GADT.TypeUnit   = TUnit
upcastNonNumScalarType GADT.TypeBool{} = TBool

upcastTypeR :: GADT.TypeR t -> Type
upcastTypeR = tup . go
  where
    tup []  = error "empty type!"
    tup [x] = x
    tup xs  = TTup xs

    go :: GADT.TypeR a -> [Type]
    go GADT.TypeRzero                                         = []
    go (GADT.TypeRscalar t)                                   = [ upcastScalarType t ]
    go (GADT.TypeRsnoc GADT.TypeRzero b@GADT.TypeRsnoc{})     = [ tup (go b) ]
    go (GADT.TypeRsnoc a@GADT.TypeRsnoc{} b@GADT.TypeRsnoc{}) = [ tup (go a), tup (go b) ]
    go (GADT.TypeRsnoc a b)                                   = go a ++ go b


-- Values

upcastScalar :: GADT.ScalarType t -> t -> Val
upcastScalar (GADT.NumScalarType t)    x = upcastNumScalar t x
upcastScalar (GADT.NonNumScalarType t) x = upcastNonNumScalar t x

upcastNumScalar :: GADT.NumType t -> t -> Val
upcastNumScalar (GADT.IntegralNumType t) x = upcastIntegralNum t x
upcastNumScalar (GADT.FloatingNumType t) x = upcastFloatingNum t x

upcastIntegralNum :: GADT.IntegralType t -> t -> Val
upcastIntegralNum GADT.TypeInt{} = VInt

upcastFloatingNum :: GADT.FloatingType t -> t -> Val
upcastFloatingNum GADT.TypeFloat{} = VFloat

upcastNonNumScalar :: GADT.NonNumType t -> t -> Val
upcastNonNumScalar GADT.TypeUnit   = const VUnit
upcastNonNumScalar GADT.TypeBool{} = VBool

upcastConstR :: GADT.TypeR t -> t -> Val
upcastConstR ty = tup . go ty
  where
    tup []  = error "empty value!"
    tup [x] = x
    tup xs  = VTup xs

    go :: GADT.TypeR a -> a -> [Val]
    go GADT.TypeRzero                                         ()      = []
    go (GADT.TypeRscalar t)                                   x       = [ upcastScalar t x ]
    go (GADT.TypeRsnoc GADT.TypeRzero b@GADT.TypeRsnoc{})     ((), x) = [ tup (go b x) ]
    go (GADT.TypeRsnoc a@GADT.TypeRsnoc{} b@GADT.TypeRsnoc{}) (x, y)  = [ tup (go a x), tup (go b y) ]
    go (GADT.TypeRsnoc a b)                                   (x, y)  = go a x ++ go b y


-- Expressions

upcast :: forall env t. GADT.OpenExp env t -> Exp
upcast exp =
  case exp of
    GADT.Let (a :: GADT.OpenExp env s) b
                        -> Let (upcastTypeR (GADT.eltType (undefined::s)), upcast a) (upcast b)
    GADT.Var ix         -> Var (upcastTypeR (GADT.eltType (undefined::t))) (GADT.idxToInt ix)
    GADT.Const c        -> let t = GADT.eltType (undefined::t)
                           in  Const (upcastTypeR t) (upcastConstR t c)
    GADT.Prod p         -> prod (upcastTypeR (GADT.eltType (undefined::t))) p
    GADT.If p t e       -> If (upcast p) (upcast t) (upcast e)
    GADT.PrimApp f x    -> PrimApp (prim f) (upcast x)
    GADT.Prj ix (p :: GADT.OpenExp env p)
                        -> Prj (upcastTypeR (GADT.eltType (undefined::p))) (GADT.prodIdxToInt ix) (upcast p)

  where
    prod :: Type -> GADT.Prod (GADT.OpenExp env) p -> Exp
    prod t =
      let go :: GADT.Prod (GADT.OpenExp env) p -> [Exp]
          go GADT.EmptyProd      = []
          go (GADT.PushProd p e) = upcast e : go p
      in
      Prod t . reverse . go

    prim :: GADT.PrimFun f -> PrimFun
    prim (GADT.PrimAdd t) = PrimAdd (upcastNumType t)
    prim (GADT.PrimMul t) = PrimMul (upcastNumType t)
    prim GADT.PrimToFloat = PrimToFloat


-- Downcasting
-- ===========
--
-- Downcasting can fail. It takes an untyped expression, or types only at the
-- value level, and attempts to promote type information to the type level.
--
downcast :: GADT.Elt t => Exp -> GADT.Exp t
downcast exp =
  fromMaybe (inconsistent "downcast") (downcastOpenExp EmptyLayout exp)

downcastOpenExp :: forall env t. GADT.Elt t => Layout env env -> Exp -> Maybe (GADT.OpenExp env t)
downcastOpenExp lyt = cvt
  where
    -- We could reduce the 'Elt' constraint here to 'Typeable' (which is
    -- required to support 'unify'), and use 'eltType' to extract the class
    -- constraint locally at each constructor.
    --
    cvt :: forall s. GADT.Elt s => Exp -> Maybe (GADT.OpenExp env s)
    cvt (Var _ ix)                                      -- type check occurs in downcastIdx
      = GADT.Var <$> gcast (downcastIdx ix lyt :: GADT.Idx env s)

    cvt (Let (t,a) b)
      | Elt' (_ :: a)                   <- elt' t       -- In this case the type of the bound expression is existentially
      , Just (a' :: GADT.OpenExp env a) <- cvt a        -- quantified, so we must encode its type in the untyped term tree.
      , Just b'                         <- downcastOpenExp (incLayout lyt `PushLayout` GADT.ZeroIdx) b
      = Just (GADT.Let a' b')

    cvt (Const t c)
      | Elt' (_ :: s')                  <- elt' t                               -- We could assume that 's' is correct, but this
      , Just Refl                       <- unify (undefined::s) (undefined::s') -- way we get a type error message instead of a
      = Just . GADT.Const $ downcastConstR (GADT.eltType (undefined::s)) c      -- pattern match failure in 'downcastConst'

    cvt (Prod t p)
      | Just (IsProduct' (_ :: s'))     <- isProduct' t
      , Just Refl                       <- unify (undefined::s) (undefined::s')
      , Just p'                         <- downcastProd lyt (GADT.prodR (undefined::s)) p
      = Just (GADT.Prod p')

    cvt (Prj t ix p)
      | Just (IsProduct' (_ :: p))      <- isProduct' t
      , Just (p' :: GADT.OpenExp env p) <- cvt p        -- Here we can explicitly require the conversion result to be type 'p'
      , ix'                             <- downcastProdIdx ix (GADT.prodR (undefined::p))
      = Just (GADT.Prj ix' p')

    cvt (If p t e)
      | Just p' <- cvt p                -- No extra (value-level) type witness is required for this case, as we rely
      , Just t' <- cvt t                -- on the unification constraints imposed by GADT.If; i.e. p ~ Bool and t ~ e,
      , Just e' <- cvt e                -- to guide the recursive calls to 'cvt'.
      = Just (GADT.If p' t' e')

    cvt (PrimApp f x)
      | Just (PrimFun' (f' :: GADT.PrimFun (a -> r)))   <- downcastPrimFun f
      , Just Refl                                       <- unify (undefined::r) (undefined::s)
      , Just x'                                         <- cvt x
      = Just (GADT.PrimApp f' x')

    cvt _
      = Nothing


-- Promoting types
-- ---------------

-- Construct some _sealed_ proof that our value-level types imply class
-- membership.
--
data Elt' where
  Elt' :: GADT.Elt t => {- dummy -} t -> Elt'

data IsProduct' where
  IsProduct' :: (GADT.Elt p, GADT.IsProduct p) => {- dummy -} p -> IsProduct'

elt' :: Type -> Elt'
elt' TUnit   = Elt' ()
elt' TInt    = Elt' (undefined :: Int)
elt' TFloat  = Elt' (undefined :: Float)
elt' TBool   = Elt' (undefined :: Bool)
elt' (TTup t)
  | [ta,tb]       <- t
  , Elt' (_ :: a) <- elt' ta
  , Elt' (_ :: b) <- elt' tb
  = Elt' (undefined :: (a,b))
  --
  | [ta,tb,tc]    <- t
  , Elt' (_ :: a) <- elt' ta
  , Elt' (_ :: b) <- elt' tb
  , Elt' (_ :: c) <- elt' tc
  = Elt' (undefined :: (a,b,c))
  --
  | [ta,tb,tc,td] <- t
  , Elt' (_ :: a) <- elt' ta
  , Elt' (_ :: b) <- elt' tb
  , Elt' (_ :: c) <- elt' tc
  , Elt' (_ :: d) <- elt' td
  = Elt' (undefined :: (a,b,c,d))
  --
  | otherwise
  = error "elt': I only know how to handle up to 4-tuples"


isProduct' :: Type -> Maybe IsProduct'
isProduct' TUnit   = Nothing
isProduct' TInt    = Nothing
isProduct' TFloat  = Nothing
isProduct' TBool   = Nothing
isProduct' (TTup t)
  | [ta,tb]       <- t
  , Elt' (_ :: a) <- elt' ta
  , Elt' (_ :: b) <- elt' tb
  = Just $ IsProduct' (undefined :: (a,b))
  --
  | [ta,tb,tc]    <- t
  , Elt' (_ :: a) <- elt' ta
  , Elt' (_ :: b) <- elt' tb
  , Elt' (_ :: c) <- elt' tc
  = Just $ IsProduct' (undefined :: (a,b,c))
  --
  | [ta,tb,tc,td] <- t
  , Elt' (_ :: a) <- elt' ta
  , Elt' (_ :: b) <- elt' tb
  , Elt' (_ :: c) <- elt' tc
  , Elt' (_ :: d) <- elt' td
  = Just $ IsProduct' (undefined :: (a,b,c,d))
  --
  | otherwise
  = error "isProduct': I only know how to handle up to 4-tuples"


-- Utilities
-- ---------

typeError :: forall s t a. (Typeable s, Typeable t) => s -> t -> a
typeError _ _
  = error
  $ printf "Couldn't match expected type `%s' with actual type `%s'"
           (show (typeOf (undefined::s)))
           (show (typeOf (undefined::t)))

inconsistent :: String -> a
inconsistent s = error (s ++ ": inconsistent valuation")

-- Gain some type-level knowledge when two value-level types match
--
unify :: (Typeable s, Typeable t) => s -> t -> Maybe (s :~: t)
unify s t =
  case eqT of
    Nothing   -> typeError s t
    refl      -> refl


-- Indices of let-bound variables
-- ------------------------------

-- Layouts map environments to indices projecting into that environment. The two
-- separate environment types are required because the weakening step
-- (incLayout) happens separately to adding a new term when we push under a
-- binder.
--
data Layout env env' where
  EmptyLayout :: Layout env ()
  PushLayout  :: Typeable t
              => Layout env env' -> GADT.Idx env t -> Layout env (env',t)

-- Increment all the indices in the layout. This makes space at the head of the
-- layout to add a new index, for when we push under a binder.
--
incLayout :: Layout env env' -> Layout (env, t) env'
incLayout EmptyLayout         = EmptyLayout
incLayout (PushLayout lyt ix) = PushLayout (incLayout lyt) (GADT.SuccIdx ix)

-- Get an index out of the environment
--
downcastIdx :: forall t env env'. Typeable t => Int -> Layout env env' -> GADT.Idx env t
downcastIdx 0 (PushLayout _ (ix :: GADT.Idx env t'))
  | Just ix' <- gcast ix          = ix'
  | otherwise                     = typeError (undefined::t) (undefined::t')
downcastIdx n (PushLayout lyt _)  = downcastIdx (n-1) lyt
downcastIdx _ _                   = error "unbound variable"


-- Constant values
-- ---------------

-- TLM: ugh, this is difficult because we threw away some structure when we
--      flattened tuple types into lists analogous to the surface
--      representation, instead of keeping the binary tree encoding; see the
--      final case of 'upcastConstR' which uses (++).
--
downcastConstR :: GADT.TypeR t -> Val -> t
downcastConstR t = go t . untup
  where
    untup :: Val -> [Val]
    untup (VTup vs) = vs
    untup x         = [x]

    go :: GADT.TypeR a -> [Val] -> a
    go GADT.TypeRzero                                           []      = ()
    go (GADT.TypeRscalar s)                                     [v]     = downcastScalar s v
    go (GADT.TypeRsnoc GADT.TypeRzero b@GADT.TypeRsnoc{})       [v]     = ((), go b (untup v))
    go (GADT.TypeRsnoc GADT.TypeRzero b@GADT.TypeRscalar{})     v       = ((), go b v)
    go (GADT.TypeRsnoc a@GADT.TypeRsnoc{} b@GADT.TypeRscalar{}) xs      = (go a (init xs), go b [last xs])
    go (GADT.TypeRsnoc a b)                                     [x,y]   = (go a (untup x), go b (untup y))
    go _                                                        _       = inconsistent "downcastConstR"

downcastScalar :: GADT.ScalarType t -> Val -> t
downcastScalar (GADT.NumScalarType t)    v = downcastNumScalar t v
downcastScalar (GADT.NonNumScalarType t) v = downcastNonNumScalar t v

downcastNumScalar :: GADT.NumType t -> Val -> t
downcastNumScalar (GADT.IntegralNumType t) v = downcastIntegral t v
downcastNumScalar (GADT.FloatingNumType t) v = downcastFloating t v

downcastIntegral :: GADT.IntegralType t -> Val -> t
downcastIntegral GADT.TypeInt{} (VInt x) = x
downcastIntegral _ _ = inconsistent "downcastIntegral"

downcastFloating :: GADT.FloatingType t -> Val -> t
downcastFloating GADT.TypeFloat{} (VFloat x) = x
downcastFloating _ _ = inconsistent "downcastFloating"

downcastNonNumScalar :: GADT.NonNumType t -> Val -> t
downcastNonNumScalar GADT.TypeUnit   VUnit     = ()
downcastNonNumScalar GADT.TypeBool{} (VBool x) = x
downcastNonNumScalar _ _ = inconsistent "downcastNonNumScalar"


-- Products
-- --------

downcastProd :: forall env p. Layout env env -> GADT.ProdR p -> [Exp] -> Maybe (GADT.Prod (GADT.OpenExp env) p)
downcastProd lyt prod = go prod . reverse
  where
    go :: GADT.ProdR s -> [Exp] -> Maybe (GADT.Prod (GADT.OpenExp env) s)
    go GADT.ProdRzero     []     = Just GADT.EmptyProd
    go (GADT.ProdRsnoc p) (e:es) = do
      e'  <- downcastOpenExp lyt e
      es' <- go p es
      Just (GADT.PushProd es' e')
    go _ _ = inconsistent "downcastProd"


downcastProdIdx :: forall p e. Typeable e => Int -> GADT.ProdR p -> GADT.ProdIdx p e
downcastProdIdx 0 (GADT.ProdRsnoc _)
  | Just ix <- gcast GADT.ZeroProdIdx   = ix
downcastProdIdx n (GADT.ProdRsnoc p)    = GADT.SuccProdIdx (downcastProdIdx (n-1) p)
downcastProdIdx _ _                     = error "invalid projection"


-- Primitive functions
-- -------------------

data NumType' where
  NumType' :: GADT.Elt a => GADT.NumType a -> NumType'

data PrimFun' where
  PrimFun' :: (GADT.Elt a, GADT.Elt r) => GADT.PrimFun (a -> r) -> PrimFun'

numType' :: Type -> Maybe NumType'
numType' TInt   = Just $ NumType' (GADT.IntegralNumType (GADT.TypeInt   GADT.IntegralDict))
numType' TFloat = Just $ NumType' (GADT.FloatingNumType (GADT.TypeFloat GADT.FloatingDict))
numType' _      = Nothing

downcastPrimFun :: PrimFun -> Maybe PrimFun'
downcastPrimFun (PrimAdd t)
  | Just (NumType' dict) <- numType' t
  = Just (PrimFun' (GADT.PrimAdd dict))

downcastPrimFun (PrimMul t)
  | Just (NumType' dict) <- numType' t
  = Just (PrimFun' (GADT.PrimMul dict))

downcastPrimFun PrimToFloat
  = Just (PrimFun' GADT.PrimToFloat)

downcastPrimFun _
  = Nothing

