{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Types for

module Ghostbuster.Types
  where

-- I used to use these symbol packages, but had problems with all of them:
-- import Data.Symbol
-- import StringTable.Atom
-- import Data.Atom.Simple

import qualified Data.ByteString.Char8 as B
import           Data.String (IsString(..))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)


type TypeError = String

-- | We could distinguish our different classes variables: T,K,a, etc,
-- but we don't do that here:
type TName = Var
type KName = Var
type TermVar = Var
type TyVar = Var
newtype Var = Var B.ByteString
   deriving (Eq, Ord, Show, Read, IsString, Generic)

-- | A program is a list of declarations followed by a "main" expression.
data Prog = Prog [DDef] [VDef] Exp
  deriving (Eq,Ord,Show,Read,Generic)

-- | A single datatype definition.
data DDef = DDef { tyName :: Var
                 , kVars :: [(TyVar,Kind)]
                 , cVars :: [(TyVar,Kind)]
                 , sVars :: [(TyVar,Kind)]
                 , cases :: [KCons]
                 }
  deriving (Eq,Ord,Show,Read,Generic)

-- | Top-level value definitions
data VDef = VDef { valName :: Var
                 , valTy   :: Sigma
                 , valExp  :: Exp
                 }
  deriving (Eq,Ord,Show,Read,Generic)

-- | Data constructor signatures.
data KCons = KCons { conName :: Var
                   , fields  :: [MonoTy] -- ^ The \tau_1 through \tau_p arguments
                   , outputs :: [MonoTy] -- ^ The type params fed to 'T' in the RHS
                   }
  deriving (Eq,Ord,Show,Read,Generic)

-- | (possibly open) Monomorphic types.
data MonoTy = VarTy TyVar
            | ArrowTy MonoTy MonoTy
            | ConTy KName [MonoTy]
            | TypeDict TName
  deriving (Eq,Ord,Show,Read,Generic)

data Kind = Star | ArrowKind Kind Kind
  deriving (Eq,Ord,Show,Read,Generic)

-- | Type Schemes
data Sigma = ForAll [(TyVar,Kind)] MonoTy | MonTy MonoTy
  deriving (Eq,Ord,Show,Read,Generic)

data Pat = Pat KName [TermVar]
  deriving (Eq,Ord,Show,Read,Generic)

data Exp = EK KName
         | EVar TermVar
         | ELam (TermVar,MonoTy) Exp
         | EApp Exp Exp
         | ELet (TermVar,Sigma,Exp) Exp
         | ECase Exp [(Pat,Exp)]
         | EDict TName
         | ECaseDict Exp (TName,[TermVar],Exp) Exp
         | EIfTyEq (Exp,Exp) Exp Exp
  deriving (Eq,Ord,Show,Read,Generic)

--------------------------------------------------------------------------------
-- Values, for use by any interpreters:

-- | Vals are a subset of Exp
data Val = VK KName [Val] -- ^ Data constructors are parameterized by values.
         | VLam (TermVar,MonoTy) Exp
         | VDict TName
  deriving (Eq,Ord,Show,Read,Generic)

-- | Sometimes it's convenient to convert back to expression:
val2Exp :: Val -> Exp
val2Exp (VK k []) = EK k
val2Exp (VK k (h:t)) = EApp (val2Exp (VK k t)) (val2Exp h)
val2Exp (VLam vt bod) = ELam vt bod
val2Exp (VDict t) = EDict t

--------------------------------------------------------------------------------

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
instance Out Sigma
instance Out Pat
instance Out Exp
instance Out Val
instance Out DDef
instance Out VDef
instance Out Prog

--------------------------------------------------------------------------------

 -- TODO: when it's done ghostbuster will have this sig:
ghostbuster :: [DDef] -> Prog
ghostbuster = undefined
