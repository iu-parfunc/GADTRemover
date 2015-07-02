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

toVarTy :: Var -> MonoTy
toVarTy = VarTy

-- | A program is a list of declarations followed by a "main" expression.
data Prog = Prog
  { prgDefs :: [DDef]
  , prgVals :: [VDef]
  , prgMain :: VDef
  }
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
                   }
  deriving (Eq,Ord,Show,Read,Generic)

-- | Monomorphic types (possibly open).
--
data MonoTy
  = VarTy TyVar                 -- ^ type variable
  | ArrowTy MonoTy MonoTy       -- ^ function type
  | ConTy TName [MonoTy]        -- ^ named type or type constructor combined with type application
  | TypeDictTy TName
  deriving (Eq,Ord,Show,Read,Generic)

data Kind = Star | ArrowKind Kind Kind
  deriving (Eq,Ord,Show,Read,Generic)

-- | Type Schemes, Sigma in the paper.
data TyScheme = ForAll [(TyVar,Kind)] MonoTy
  deriving (Eq,Ord,Show,Read,Generic)

data Pat = Pat KName [TermVar]
  deriving (Eq,Ord,Show,Read,Generic)

data Exp = EK KName                   -- ^ Data constructor ref.  Could be combined with EVar.
         | EVar TermVar               -- ^ Variable reference.
         | ELam (TermVar,MonoTy) Exp
         | EApp Exp Exp
         | ELet (TermVar,TyScheme,Exp) Exp
         | ECase Exp [(Pat,Exp)]

         | EDict TName                -- ^ Dictionary reification for the named type constr.
         | ECaseDict Exp (TName,[TermVar],Exp) Exp
            -- ^ Two-branch case on a dictionary.
         | EIfTyEq (Exp,Exp) Exp Exp
  deriving (Eq,Ord,Show,Read,Generic)


-- | Built-in type environment.  The idea is to use this for only
-- types which MUST be present to type the native forms of the
-- language such as ELam.
primitiveTypes :: [DDef]
primitiveTypes =
-- RRN: For a convention, I'm not sure if we want "(->)" or "->":
  [ DDef "ArrowTy" [("a",Star), ("b",Star)] [] [] []
--  , DDef "(,)"  [("a",Star), ("b",Star)] [] [] [] -- TLM: change to TupleTy ???
-- RRN: that tuple type doesn't expose any constructors...
-- Tup2 below does... we can use comma or Tup2, either way.
-- TLM: I would vote for (,) then. The code generator might need to special case
--      this to output Haskell tuples in the generated code, and "(,*)" is
--      easier to search for. Even if we don't special case this, Haskell might
--      be able to deal with the prefix "(,) a b" notation as is.
-- RRN: See gchat comments about getting intro trouble with name-mangling
--      infix/punctuation names.  Easier to avoid for now.


-- Only arrow really needs to be here.  We CAN put other types here
-- for convenience, but the original plan was to include only the
-- types that must truly be built-in here...
  , ints
  , maybeD
  , boolD
  ] ++
  tupsD

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

boolD :: DDef
boolD = DDef "Bool" [] [] []
      [ KCons "True" [] []
      , KCons "False" [] []
      ]

-- RRN: We can use "," or "Tup2" as the constructor.
tupsD :: [DDef]
tupsD = [ DDef "Tup2" [("a", Star), ("b", Star)] [] []
          [ KCons "Tup2" ["a","b"] ["a","b"]]

        -- If needed, add more:
        -- , DDef "Tup3" [("a", Star),("b", Star),("c", Star)] [] []
        ]

--------------------------------------------------------------------------------
-- Tests:
-- | Test mutually recursive data definitions
-- data Foo (a :: *) where
--   Bar :: Baz a -> Foo a
--
-- data Baz (a :: *) where
--  Qux :: Foo a -> Baz a
mutRecurseDDefsGood :: [DDef]
mutRecurseDDefsGood =
  [
    DDef "Foo" [("a", Star)] [] []
      [KCons "Bar" [ConTy "Baz" ["a"]] ["a"]]
  , DDef "Baz" [("a", Star)] [] []
      [KCons "Qux" [ConTy "Foo" ["a"]] ["a"]]
  ]

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

-- One of the type constructors is applied to too few enough arguments
mutRecurseDDefsBad1 :: [DDef]
mutRecurseDDefsBad1 =
  [
    DDef "Foo" [("a", Star)] [] []
      [KCons "Bar" [ConTy "Baz" []] ["a"]]

  , DDef "Baz" [("a", Star)] [] []
      [KCons "Qux" [ConTy "Foo" ["a"]] ["a"]]
  ]

-- Wrong kinding of variables
mutRecurseDDefsBad2 :: [DDef]
mutRecurseDDefsBad2 =
  [
    DDef "Foo" [("a", ArrowKind Star Star)] [] []
      [KCons "Bar" [ConTy "Baz" ["a"]] ["a"]]

  , DDef "Baz" [("a", Star)] [] []
      [KCons "Qux" [ConTy "Foo" ["a"]] ["a"]]
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
