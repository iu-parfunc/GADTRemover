{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module GADT3
  where

import Data.Proxy
import Text.PrettyPrint.Leijen


-- Product types
-- =============

class IsProduct t where
  type ProdRepr t
  fromProd :: t -> ProdRepr t
  toProd   :: ProdRepr t -> t

instance IsProduct () where
  type ProdRepr () = ()
  fromProd () = ()
  toProd ()   = ()

instance IsProduct (a, b) where
  type ProdRepr (a, b) = (((), a), b)
  fromProd (a, b)     = (((), a), b)
  toProd (((), a), b) = (a, b)

instance IsProduct (a, b, c) where
  type ProdRepr (a, b, c) = (ProdRepr (a, b), c)
  fromProd (a, b, c) = (fromProd (a,b), c)
  toProd (ab, c)     = let (a, b) = toProd ab in (a, b, c)


-- Type hierarchy
-- ==============

data IntegralDict a where
  IntegralDict :: (Integral a, Num a, Show a, Eq a) => IntegralDict a

data FloatingDict a where
  FloatingDict :: (Floating a, Fractional a, Num a, Show a, Eq a) => FloatingDict a

data NonNumDict a where
  NonNumDict   :: (Show a, Eq a) => NonNumDict a

data TupleType a where
  UnitTuple   :: TupleType ()
  SingleTuple :: ScalarType a -> TupleType a
  PairTuple   :: TupleType a -> TupleType b -> TupleType (a, b)

data ScalarType a where
  NumScalarType    :: NumType a -> ScalarType a
  NonNumScalarType :: NonNumType a -> ScalarType a

data NumType a where
  IntegralNumType :: IntegralType a -> NumType a
  FloatingNumType :: FloatingType a -> NumType a

data IntegralType a where
  TypeInt :: IntegralDict Int -> IntegralType Int

data FloatingType a where
  TypeFloat :: FloatingDict Float -> FloatingType Float

data NonNumType a where
  TypeBool :: NonNumDict Bool -> NonNumType Bool

integralDict :: IntegralType a -> IntegralDict a
integralDict (TypeInt d) = d

floatingDict :: FloatingType a -> FloatingDict a
floatingDict (TypeFloat d) = d


-- Surface and representation types
-- ================================

type family EltRepr a :: *
type instance EltRepr () = ()
type instance EltRepr Int = Int
type instance EltRepr Bool = Bool
type instance EltRepr Float = Float
type instance EltRepr (a, b) = ProdRepr (EltRepr a, EltRepr b)
type instance EltRepr (a, b, c) = ProdRepr (EltRepr a, EltRepr b, EltRepr c)


class Show a => Elt a where
  toElt   :: EltRepr a -> a
  fromElt :: a -> EltRepr a
  eltType :: Proxy a -> TupleType (EltRepr a)

instance Elt () where
  toElt     = id
  fromElt   = id
  eltType _ = UnitTuple

instance Elt Int where
  toElt     = id
  fromElt   = id
  eltType _ = SingleTuple (NumScalarType (IntegralNumType (TypeInt IntegralDict)))

instance Elt Float where
  toElt     = id
  fromElt   = id
  eltType _ = SingleTuple (NumScalarType (FloatingNumType (TypeFloat FloatingDict)))

instance Elt Bool where
  toElt     = id
  fromElt   = id
  eltType _ = SingleTuple (NonNumScalarType (TypeBool NonNumDict))

instance (Elt a, Elt b) => Elt (a, b) where
  toElt p        = let (a, b) = toProd p in (toElt a, toElt b)
  fromElt (a, b) = fromProd (fromElt a, fromElt b)
  eltType Proxy  = PairTuple (PairTuple UnitTuple (eltType (Proxy :: Proxy a)))
                             (eltType (Proxy :: Proxy b))

instance (Elt a, Elt b, Elt c) => Elt (a, b, c) where
  toElt p           = let (a, b, c) = toProd p in (toElt a, toElt b, toElt c)
  fromElt (a, b, c) = fromProd (fromElt a, fromElt b, fromElt c)
  eltType Proxy     = PairTuple (eltType (Proxy :: Proxy (a, b)))
                                (eltType (Proxy :: Proxy c))


-- Language definition
-- ===================

-- Environments
-- ------------

data Idx env t where
  ZeroIdx ::              Idx (env, t) t
  SuccIdx :: Idx env t -> Idx (env, s) t

data Env env where
  EmptyEnv ::                 Env ()
  PushEnv  :: a -> Env env -> Env (env, a)

prjIdx :: Idx env t -> Env env -> t
prjIdx ZeroIdx      (PushEnv t _)   = t
prjIdx (SuccIdx ix) (PushEnv _ env) = prjIdx ix env
prjIdx _            _               = error "impossible case"

idxToInt :: Idx env t -> Int
idxToInt ZeroIdx      = 0
idxToInt (SuccIdx ix) = 1 + idxToInt ix

-- Product types
-- -------------

data Prod c p where
  EmptyProd ::                             Prod c ()
  PushProd  :: Elt p => Prod c s -> c p -> Prod c (s, p)

data ProdIdx p e where
  ZeroProdIdx ::                ProdIdx (p, s) s
  SuccProdIdx :: ProdIdx p e -> ProdIdx (p, s) e

prodIdxToInt :: ProdIdx p e -> Int
prodIdxToInt ZeroProdIdx      = 0
prodIdxToInt (SuccProdIdx ix) = 1 + prodIdxToInt ix


-- Language definition
-- -------------------

type Exp t = OpenExp () t

data OpenExp env t where
  Let           :: (Elt bnd, Elt body)
                => OpenExp env        bnd
                -> OpenExp (env, bnd) body
                -> OpenExp env        body

  Var           :: Elt t
                => Idx env t
                -> OpenExp env t

  Const         :: Elt t
                => EltRepr t
                -> OpenExp env t

  Prod          :: (Elt t, IsProduct t)
                => Prod (OpenExp env) (ProdRepr t)
                -> OpenExp env t

  Prj           :: (Elt t, IsProduct t, Elt e)
                => ProdIdx (ProdRepr t) e
                -> OpenExp env t
                -> OpenExp env e

  PrimApp       :: (Elt a, Elt r)
                => PrimFun (a -> r)
                -> OpenExp env a
                -> OpenExp env r

  If            :: Elt t
                => OpenExp env Bool
                -> OpenExp env t
                -> OpenExp env t
                -> OpenExp env t

data PrimFun f where
  PrimAdd       :: NumType a -> PrimFun ((a,a) -> a)
  PrimMul       :: NumType a -> PrimFun ((a,a) -> a)
  PrimToFloat   :: PrimFun (Int -> Float)


-- Pretty printing
-- ---------------

prettyExp :: forall env t. Int -> (Doc -> Doc) -> OpenExp env t -> Doc
prettyExp lvl wrap = pp
  where
    ppE :: OpenExp env s -> Doc
    ppE = prettyExp lvl parens

    pp :: OpenExp env t -> Doc
    pp (Var ix)         = char 'x' <> int (lvl - idxToInt ix - 1)
    pp (Const c)        = text (show (toElt c :: t))
    pp (Prj ix tup)     = wrap (char '#' <> int (prodIdxToInt ix) <+> ppE tup)

    pp (Let a b) =
      let x  = char 'x' <> int lvl
          a' = prettyExp lvl     id a
          b' = prettyExp (lvl+1) id b

          isLet Let{} = True
          isLet _     = False
      in
      if not (isLet a) && isLet b
         then vcat [ text "let" <+> x <+> equals <+> a' <+> text "in", b'               ]
         else vcat [ text "let" <+> x <+> equals <+> a',               text "in" <+> b' ]

    pp (Prod p) =
      let collect :: Prod (OpenExp env) p -> [Doc]
          collect EmptyProd      = []
          collect (PushProd t e) = prettyExp lvl id e : collect t
      in
      tupled (reverse (collect p))

    pp (PrimApp f x) =
      let ppF :: PrimFun f -> Doc
          ppF PrimAdd{}     = text "(+)"
          ppF PrimMul{}     = text "(*)"
          ppF PrimToFloat{} = text "toFloat"
      in
      wrap (ppF f <+> ppE x)

    pp (If p t e) =
      hang 3 $ vcat [ text "if"   <+> ppE p, text "then" <+> ppE t, text "else" <+> ppE e ]


instance Show (OpenExp env t) where
  show = show . prettyExp 0 id


-- Interpreter
-- -----------

eval :: Exp t -> t
eval = evalOpenExp EmptyEnv

evalOpenExp :: forall env t. Env env -> OpenExp env t -> t
evalOpenExp env e = go e
  where
    go :: OpenExp env s -> s
    go (Let a b)        = evalOpenExp (PushEnv (go a) env) b
    go (Var ix)         = prjIdx ix env
    go (Const c)        = toElt c
    go (Prj ix p)       = prj ix (fromProd (go p))
    go (Prod p)         = toProd (prod p)
    go (PrimApp f x)    = prim f (go x)
    go (If p a b)
      | go p            = go a
      | otherwise       = go b

    prj :: ProdIdx p e -> p -> e
    prj ZeroProdIdx      (_, v) = v
    prj (SuccProdIdx ix) (p, _) = prj ix p

    prod :: Prod (OpenExp env) p -> p
    prod EmptyProd      = ()
    prod (PushProd p v) = (prod p, go v)

    prim :: PrimFun f -> f
    prim (PrimAdd t) = add t
    prim (PrimMul t) = mul t
    prim PrimToFloat = fromIntegral

    add :: NumType a -> ((a,a) -> a)
    add (IntegralNumType t) | IntegralDict <- integralDict t = uncurry (+)
    add (FloatingNumType t) | FloatingDict <- floatingDict t = uncurry (+)

    mul :: NumType a -> ((a,a) -> a)
    mul (IntegralNumType t) | IntegralDict <- integralDict t = uncurry (*)
    mul (FloatingNumType t) | FloatingDict <- floatingDict t = uncurry (*)


-- Tests
-- =====

constant :: Elt t => t -> OpenExp env t
constant = Const . fromElt

p0 :: Exp Int
p0 = If (constant True) (constant 3) (constant 4)

p1 :: Exp Int
p1 = Let (constant 5) (Var ZeroIdx)

p2 :: Exp Int
p2 = If (constant True) (constant 11) p1

p3 :: Exp Int
p3 = Let (constant 5) (If (constant True) (Var ZeroIdx) (constant 4))

p4 :: Exp Int
p4 = Let (constant 4)
   $ Let (constant 5)
   $ PrimApp (PrimAdd (IntegralNumType (TypeInt IntegralDict)))
             (Prod $ EmptyProd `PushProd` Var ZeroIdx
                               `PushProd` Var (SuccIdx ZeroIdx))

p5 :: Exp Bool
p5 = constant True

p6 :: Exp Bool
p6 = Let p5
   $ If (Var ZeroIdx) (constant False)
                      (Var ZeroIdx)

p7 :: Exp (Int,Float)
p7 = constant (1,pi)

p8 :: Exp Float
p8 = Let p7
   $ Prj ZeroProdIdx (Var ZeroIdx)

p9 :: Exp Float
p9 = Let (constant (pi, 8, 4.86))
   $ Let (PrimApp (PrimMul (FloatingNumType (TypeFloat FloatingDict)))
                  (Prod (EmptyProd `PushProd` Prj ZeroProdIdx (Var ZeroIdx)
                                   `PushProd` PrimApp PrimToFloat (Prj (SuccProdIdx ZeroProdIdx) (Var ZeroIdx)))))
         (PrimApp (PrimAdd (FloatingNumType (TypeFloat FloatingDict)))
                  (Prod (EmptyProd `PushProd` Var ZeroIdx
                                   `PushProd` Prj (SuccProdIdx (SuccProdIdx ZeroProdIdx)) (Var (SuccIdx ZeroIdx)))))

