{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Types for all Ghostbuster related tools.

module Ghostbuster.Types
  where

-- I used to use these symbol packages, but had problems with all of them:
-- import Data.Symbol
-- import StringTable.Atom
-- import Data.Atom.Simple

import Data.Map.Lazy as M

import qualified Data.ByteString.Char8 as B
import           Data.String (IsString(..))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)
import qualified Data.List as L

type TypeError = String

-- | We could distinguish our different classes variables: T,K,a, etc,
-- but we don't do that here.  This corresponds to "T":
type TName = Var
type KName = Var    -- ^ This corresponds to "K" in the paper.
type TermVar = Var  -- ^ x,y,z
type TyVar = Var    -- ^ a,b,c
newtype Var = Var B.ByteString
   deriving (Eq, Ord, Show, Read, IsString, Generic)

unVar :: Var -> B.ByteString
unVar (Var v) = v

mkVar :: String -> Var
mkVar = Var . B.pack

unMkVar :: Var -> String
unMkVar = B.unpack . unVar

-- | A program is a list of declarations followed by a "main" expression.
data Prog = Prog [DDef] [VDef] Exp
  deriving (Eq,Ord,Show,Read,Generic)

-- | A single datatype definition.
data DDef = DDef { tyName :: TName
                 , kVars :: [(TyVar,Kind)]
                 , cVars :: [(TyVar,Kind)]
                 , sVars :: [(TyVar,Kind)]
                 , cases :: [KCons]
                 }
  deriving (Eq,Ord,Show,Read,Generic)

-- | Top-level value definitions
data VDef = VDef { valName :: Var
                 , valTy   :: TyScheme
                 , valExp  :: Exp
                 }
  deriving (Eq,Ord,Show,Read,Generic)

-- | Data constructor signatures.
data KCons = KCons { conName :: Var
                   , fields  :: [MonoTy] -- ^ The \tau_1 through \tau_p arguments
                   , outputs :: [MonoTy] -- ^ The type params fed to 'T' in the RHS
                        -- TLM: This is a bit strange, shouldn't there only be one
                        -- output type?
                   }
  deriving (Eq,Ord,Show,Read,Generic)

-- | Monomorphic types (possibly open).
--
data MonoTy
  = VarTy TyVar                 -- ^ type variable
  | ArrowTy MonoTy MonoTy       -- ^ function type
  | ConTy TName [MonoTy]        -- ^ named type or type constructor combined with type application
  | TupleTy [MonoTy]            -- ^ tuple type (boxed)
  | TypeDictTy TName
  deriving (Eq,Ord,Show,Read,Generic)

data Kind = Star | ArrowKind Kind Kind
  deriving (Eq,Ord,Show,Read,Generic)

-- | Type Schemes, Sigma in the paper.
data TyScheme = ForAll [(TyVar,Kind)] MonoTy
              | MonTy MonoTy
  deriving (Eq,Ord,Show,Read,Generic)

data Pat = Pat KName [TermVar]
  deriving (Eq,Ord,Show,Read,Generic)

data Exp = EK KName
         | EVar TermVar
         | ELam (TermVar,MonoTy) Exp
         | EApp Exp Exp
         | ELet (TermVar,TyScheme,Exp) Exp
         | ECase Exp [(Pat,Exp)]
         | EDict TName
         | ECaseDict Exp (TName,[TermVar],Exp) Exp
         | EIfTyEq (Exp,Exp) Exp Exp
  deriving (Eq,Ord,Show,Read,Generic)


-- | Built-in type environment.
primitiveTypes :: [DDef]
primitiveTypes =
  [ DDef "->" [("a",Star), ("b",Star)] [] [] []         -- TLM: change to ArrowTy ???
  , DDef ","  [("a",Star), ("b",Star)] [] [] []         -- TLM: change to TupleTy ???
  , ints
  ]

--------------------------------------------------------------------------------
-- Values, for use by any interpreters:

type Env = Map Var Val

-- | Vals are a subset of Exp
data Val = VK KName [Val]    -- ^ Data constructors are parameterized by values.
         | VClo (TermVar,MonoTy) Env Exp -- ^ Closures with captured environment.
         | VDict TName [Val] -- ^ A dict value may be partially or fully applied.
  deriving (Eq,Ord,Show,Read,Generic)

--------------------------------------------------------------------------------
-- General prerequisites for doing useful things in the core language:

ints :: DDef
ints = DDef "Int" [] [] []
        [ KCons "One" [] []
        , KCons "Two" [] []
        , KCons "Three" [] []
        -- Uh, we're probably missing some integers here.  Should be good enough.
        ]

maybeD :: DDef
maybeD = DDef "Maybe" [("a", Star)] [] []
        [ KCons "Just" ["a"] ["a"]
        , KCons "Nothing" [] ["a"]
        ]

--------------------------------------------------------------------------------
-- Tests:

maybeDGoodOut :: DDef
maybeDGoodOut = DDef "Maybe" [("b", ArrowKind Star Star)] [("a", Star)] []
        [ KCons "Just" ["a"] ["b", "a"]
        , KCons "Nothing" [] ["b", TypeDictTy "a"]
        ]

maybeDbad :: DDef
maybeDbad = DDef "Maybe" [("a", Star)] [("b", ArrowKind Star Star)] []
        [ KCons "Just" ["a"] ["b"]
        , KCons "Nothing" [] ["a"]
        ]

maybeDbadOut :: DDef
maybeDbadOut = DDef "Maybe" [("b", ArrowKind Star Star)] [("a", Star)] []
        [ KCons "Just" ["a"] ["b"]
        , KCons "Nothing" [] ["a"]
        ]

maybeDOutBad :: DDef
maybeDOutBad = DDef "Maybe" [("b", ArrowKind Star Star)] [("a", Star)] []
        [ KCons "Just" ["a"] ["b", "a"]
        , KCons "Nothing" [] ["a", "b"]
        ]

kindTyScheme1 :: TyScheme
kindTyScheme1 = ForAll [("a", Star), ("b", ArrowKind Star Star)] (VarTy "b")

kindTyScheme2 :: TyScheme
kindTyScheme2 = ForAll [("a", Star), ("b", ArrowKind Star Star)] (VarTy "a")

kindTyScheme3 :: TyScheme
kindTyScheme3 = ForAll [("a", Star), ("b", ArrowKind Star Star)] (VarTy "c")


--------------------------------------------------------------------------------
-- Instances

instance IsString MonoTy where
  fromString s = VarTy (Var$ B.pack s)

instance IsString Exp where
  fromString s = EVar (Var$ B.pack s)

instance Out B.ByteString where
  doc b = PP.text (B.unpack b)
  docPrec _ b  = doc b

instance Out Var where
  doc (Var b) = doc b
  docPrec _ v = doc v

instance Out KCons
instance Out MonoTy
instance Out Kind
instance Out TyScheme
instance Out Pat
instance Out Exp
instance Out DDef
instance Out VDef
instance Out Prog

-- instance Out Val

instance (Out k, Out v) => Out (Map k v) where
  docPrec _ b  = doc b
  doc mp = doc (M.toList mp)

-- Concise value printing:
instance Out Val where
  doc (VClo (v,t) env v2) = PP.parens (PP.hcat [ "\\",doc (v,t), " -> ", doc v2
                                               , " in env ", doc env] )
  doc (VDict v1 ls) = PP.hcat $ "Dict " : doc v1 : wList (L.map (PP.parens . doc) ls)
  -- docPrec n v = PP.hcat [PP.text (show n), "~", doc v]
  doc (VK v1 ls) = PP.hcat $ doc v1 : wList (L.map maybeParen ls)
   where
   maybeParen v@(VK _ []) = doc v
   maybeParen oth = PP.parens $ doc $ oth

wList :: IsString t => [t] -> [t]
wList [] = []
wList ls = " " : L.intersperse " " ls

--------------------------------------------------------------------------------

 -- TODO: when it's done ghostbuster will have this sig:
ghostbuster :: [DDef] -> Prog
ghostbuster = undefined
