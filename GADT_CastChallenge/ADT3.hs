{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ADT3
  where

import Prelude                                  hiding ( exp )
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


-- Language definition
-- -------------------

type Idx = Int
type TupleIdx = Int

data Exp
  = Let Exp Exp
  | Var Type Idx                -- cons-indexing
  | Const Type Val
  | Prj TupleIdx Exp            -- snoc-indexing
  | Prod [Exp]
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
    go (Let a b)        = evalOpenExp (go a : env) b
    go (Var _ ix)       = env !! ix             -- assert type!
    go (Const _ c)      = c                     -- assert type!
    go (Prod p)         = VTup $ map go p
    go (Prj ix p)       = prj ix (go p)
    go (If p t e)       = if_ (go p) (go t) (go e)
    go (PrimApp f x)    = case f of
                            PrimAdd t   -> add t (go x)
                            PrimMul t   -> mul t (go x)
                            PrimToFloat -> toFloat (go x)

    prj :: TupleIdx -> Val -> Val
    prj ix (VTup vs) = reverse vs !! ix
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


{--
-- Tests
-- -----

class ToVal a where
  toVal :: a -> Val

instance ToVal () where
  toVal () = VUnit

instance ToVal Int where
  toVal x = VInt x

instance ToVal Float where
  toVal x = VFloat x

instance ToVal Bool where
  toVal x = VBool x

instance (ToVal a, ToVal b) => ToVal (a,b) where
  toVal (a,b) = VTup [toVal b, toVal a]

instance (ToVal a, ToVal b, ToVal c) => ToVal (a,b,c) where
  toVal (a,b,c) = VTup [toVal c, toVal b, toVal a]


constant :: forall a. ToVal a => a -> Exp
constant x = Const TUnit (toVal x)      -- type error!

p0 :: Exp
p0 = If (constant True) (constant (3 :: Int)) (constant (4 :: Int))

p1 :: Exp
p1 = Let (constant (5::Int)) (Var TInt 0)

p2 :: Exp
p2 = If (constant True)
        (constant (11 :: Int)) p1

p3 :: Exp
p3 = Let (constant (5 :: Int))
   $ If (constant True) (Var TInt 0) (constant (4 :: Int))

p4 :: Exp
p4 = Let (constant (4 :: Int))
   $ Let (constant (5 :: Int))
   $ PrimApp (PrimAdd TInt) (Prod [Var TInt 0, Var TInt 1])

p5 :: Exp
p5 = constant True

p6 :: Exp
p6 = Let p5
   $ If (Var TBool 0)
        (constant False) (Var TBool 0)

p7 :: Exp
p7 = constant ((1,pi) :: (Int,Float))

p8 :: Exp
p8 = Let p7
   $ Prj 0 (Var TUnit 0)        -- type error!

p9 :: Exp
p9 = Let (constant ((pi, 8, 4.86) :: (Float,Int,Float)))
   $ Let (PrimApp (PrimMul TFloat) (Prod [ Prj 0 (Var TFloat 0)                         -- type error!
                                         , PrimApp PrimToFloat (Prj 1 (Var TInt 0)) ])) -- type error!
   $ PrimApp (PrimAdd TFloat) (Prod [ Var TFloat 0                                      -- type error!
                                    , Prj 2 (Var TFloat 1) ])                           -- type error!

p10 :: Exp
p10 = constant ((1, (4,2), True) :: (Int, (Float, Int), Bool))

p11 :: Exp
p11 = Let p10
    $ Prj 1 (Var TUnit 0)       -- type error!
--}


-- Upcasting
-- =========

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
    GADT.Var ix         -> Var (upcastTypeR (GADT.eltType (undefined::t))) (GADT.idxToInt ix)
    GADT.Let a b        -> Let (upcast a) (upcast b)
    GADT.Const c        -> let t = GADT.eltType (undefined::t)
                           in  Const (upcastTypeR t) (upcastConstR t c)
    GADT.Prod p         -> prod p
    GADT.Prj ix p       -> Prj (GADT.prodIdxToInt ix) (upcast p)
    GADT.If p t e       -> If (upcast p) (upcast t) (upcast e)
    GADT.PrimApp f x    -> PrimApp (prim f) (upcast x)

  where
    prod :: GADT.Prod (GADT.OpenExp env) p -> Exp
    prod =
      let go :: GADT.Prod (GADT.OpenExp env) p -> [Exp]
          go GADT.EmptyProd      = []
          go (GADT.PushProd p e) = upcast e : go p
      in
      Prod . reverse . go

    prim :: GADT.PrimFun f -> PrimFun
    prim (GADT.PrimAdd t) = PrimAdd (upcastNumType t)
    prim (GADT.PrimMul t) = PrimMul (upcastNumType t)
    prim GADT.PrimToFloat = PrimToFloat

