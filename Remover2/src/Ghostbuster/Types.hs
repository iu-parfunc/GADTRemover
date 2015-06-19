{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | hello

module Ghostbuster.Types
  where

-- I used to use these symbol packages, but had problems with all of them:
-- import Data.Symbol
-- import StringTable.Atom
-- import Data.Atom.Simple

import qualified Data.ByteString.Char8 as B
import           Data.String (IsString)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)

-- | We could distinguish our different classes variables: T,K,a, etc,
-- but we don't do that here:
type TName = Var
type KName = Var
type TermVar = Var
type TyVar = Var
newtype Var = Var B.ByteString
   deriving (Eq, Ord, Show, Read, IsString, Generic)
-- instance Show Var where
--   show (Var s) = B.unpack s
-- instance Read Var where
--   readsPrec i s = map (\ (a,b) -> (Var a,b)) (readsPrec i s)
-- instance NFData Var where
--   rnf (Var s) = rnf s

data DDef = DDef { tyName :: Var
                 , tyParams :: KCS Var
                 , cases :: [KCons]
                 }
  deriving (Eq,Ord,Show,Read,Generic)

-- KCSegorized entities:
data KCS a = KCS { ks :: [a]
                 , cs :: [a]
                 , ss :: [a]
                 }
  deriving (Eq,Ord,Show,Read,Generic)

data KCons = KCons { conName :: Var
                   , fields  :: [MonoTy] -- ^ The \tau_1 through \tau_p arguments
                   , outputs :: KCS MonoTy -- ^ The type params fed to 'T' in the RHS
                   }
  deriving (Eq,Ord,Show,Read,Generic)

data MonoTy = VarTy TyVar
            | ArrowTy MonoTy MonoTy
            | ConTy KName [MonoTy]
            | TypeDictTy TName
  deriving (Eq,Ord,Show,Read,Generic)

data Kind = Star | ArrowKind Kind Kind
  deriving (Eq,Ord,Show,Read,Generic)

data Sigma = ForAll [TyVar] MonoTy
data Pat = Pat KName [TermVar]

data Exp = EK KName
         | EVar TermVar
         | ELam (TermVar,MonoTy) Exp
         | ELet (TermVar,Sigma,Exp) Exp
         | ECase Exp [(Pat,Exp)]
         | EDict TName
         | ECaseDict Exp (TName,[TermVar],Exp)
         | EIfTyEq (Exp,Exp) Exp Exp


--------------------------------------------------------------------------------

instance Out B.ByteString where
  doc b = PP.text (B.unpack b)
  docPrec _ b  = doc b

instance Out Var where
  doc (Var b) = doc b
instance Out MonoTy
instance Out Kind

--------------------------------------------------------------------------------
-- WIP: Let's build our simple example:

v :: Var
v = Var "hello"

dd1 :: DDef
dd1 = DDef "xExp" (KCS [] [] [])
           [KCons "Con" [ConTy "Int" []] (KCS [] [] [])]


{-
data Exp (e :: *) (a :: *) where
  Con :: Int -> Exp e Int
  Add :: Exp e Int -> Exp e Int -> Exp e Int
  Mul :: Exp e Int -> Exp e Int -> Exp e Int
  Var :: Var e a -> Exp e a
  Abs :: Typ a -> Exp (e,a) b -> Exp e (a -> b)
  App :: Exp e (a -> b) -> Exp e a -> Exp e b
  -}
