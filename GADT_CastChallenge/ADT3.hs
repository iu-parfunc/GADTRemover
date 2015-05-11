{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ADT3
  where


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
    prj ix (VTup vs) = vs !! ix
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


-- Upcasting
-- =========

{--
upcastTupleType :: GADT.TupleType t -> Type
upcastTupleType GADT.UnitTuple         = TUnit
upcastTupleType (GADT.PairTuple ta tb) = TPair (upcastTupleType ta) (upcastTupleType tb)
upcastTupleType (GADT.SingleTuple t)   = upcastScalarType t

upcastScalarType :: GADT.ScalarType a -> Type
upcastScalarType (GADT.NumScalarType t)    = upcastNumScalarType t
upcastScalarType (GADT.NonNumScalarType t) = upcastNonNumScalarType t

upcastNumScalarType :: GADT.NumType a -> Type
upcastNumScalarType (GADT.IntegralNumType t) = upcastIntegralNumType t
upcastNumScalarType (GADT.FloatingNumType t) = upcastFloatingNumType t

upcastIntegralNumType :: GADT.IntegralType a -> Type
upcastIntegralNumType GADT.TypeInt{} = TInt

upcastFloatingNumType :: GADT.FloatingType a -> Type
upcastFloatingNumType GADT.TypeFloat{} = TFloat

upcastNonNumScalarType :: GADT.NonNumType a -> Type
upcastNonNumScalarType GADT.TypeBool{} = TBool
--}


