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
import           Data.String (IsString(..))
import           Prelude hiding (exp)
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
  deriving (Eq,Ord,Show,Read,Generic)

data Pat = Pat KName [TermVar]
  deriving (Eq,Ord,Show,Read,Generic)

data Exp = EK KName
         | EVar TermVar
         | ELam (TermVar,MonoTy) Exp
         | ELet (TermVar,Sigma,Exp) Exp
         | ECase Exp [(Pat,Exp)]
         | EDict TName
         | ECaseDict Exp (TName,[TermVar],Exp)
         | EIfTyEq (Exp,Exp) Exp Exp
  deriving (Eq,Ord,Show,Read,Generic)

--------------------------------------------------------------------------------

instance IsString MonoTy where
  fromString s = VarTy (Var$ B.pack s)

instance Out B.ByteString where
  doc b = PP.text (B.unpack b)
  docPrec _ b  = doc b

instance Out Var where
  doc (Var b) = doc b
  docPrec _ v = doc v
instance Out a => Out (KCS a)
instance Out KCons
instance Out MonoTy
instance Out Kind
instance Out Sigma
instance Out Pat
instance Out Exp
instance Out DDef

--------------------------------------------------------------------------------
-- WIP: Let's build our simple example:


{-
data Exp (e :: *) (a :: *) where
  Con :: Int -> Exp e Int
  Add :: Exp e Int -> Exp e Int -> Exp e Int
  Mul :: Exp e Int -> Exp e Int -> Exp e Int
  Var :: Var e a -> Exp e a
  Abs :: Typ a -> Exp (e,a) b -> Exp e (a -> b)
  App :: Exp e (a -> b) -> Exp e a -> Exp e b
-}
dd1 :: DDef
dd1 = DDef "Exp" (KCS [] ["e"] ["a"])
      [ KCons "Con" [int]                          (KCS [] ["e"] [int])
      , KCons "Add" [exp "e" int, exp "e" int]     (KCS [] ["e"] [int])
      , KCons "Mul" [exp "e" int, exp "e" int]     (KCS [] ["e"] [int])
      , KCons "Var" [ConTy "Var" ["e","a"]]        (KCS [] ["e"] ["a"])
      , KCons "Abs" [ConTy "Typ" ["a"], exp (tup "e" "a") "b"]
                                                   (KCS [] ["e"] [arr "a" "b"])
      , KCons "App" [exp "e" (arr "a" "b"), exp "e" "a"]
                                                   (KCS [] ["e"] ["b"])
      ]
  where
  exp a b = ConTy "Exp"   [a,b]
  tup a b = ConTy ","  [a,b]
  arr a b = ConTy "->" [a,b]

-- TODO: Needs Var and Typ to be defined.

int :: MonoTy
int = ConTy "Int" []
