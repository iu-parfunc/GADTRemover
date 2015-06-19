{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}


-- | hello

module Ghostbuster.Types
  where

-- I used to use these symbol packages, but had problems with all of them:
-- import Data.Symbol
-- import StringTable.Atom
-- import Data.Atom.Simple

import qualified Data.ByteString.Char8 as B
import           Data.String (IsString)
import           Text.PrettyPrint.GenericPretty (Out(doc,docPrec), Generic)

newtype Var = Var B.ByteString
   deriving (Eq, Ord, Show, Read, IsString, Generic)
-- instance Show Var where
--   show (Var s) = B.unpack s
-- instance Read Var where
--   readsPrec i s = map (\ (a,b) -> (Var a,b)) (readsPrec i s)
-- instance NFData Var where
--   rnf (Var s) = rnf s

data DDef = DDef { tyName :: Var
                 , tyParams :: Cat Var
                 -- , kVars :: [Var]
                 -- , cVars :: [Var]
                 -- , sVars :: [Var]
                 , cases :: [KCons]
                 }
  deriving (Eq,Ord,Show,Read,Generic)

-- Categorized entities:
data Cat a = Cat { ks :: [a]
                 , cs :: [a]
                 , ss :: [a]
                 }
  deriving (Eq,Ord,Show,Read,Generic)

data KCons = KCons { conName :: Var
                   , fields  :: [MonoTy] -- ^ The \tau_1 through \tau_p arguments
                   , outputs :: Cat MonoTy -- ^ The type params fed to 'T' in the RHS
                   }
  deriving (Eq,Ord,Show,Read,Generic)

data MonoTy = VarTy Var
            | ArrowTy MonoTy MonoTy
            | ConTy Var [MonoTy]
            | TypeDictTy Var
  deriving (Eq,Ord,Show,Read,Generic)

data Kind = Star | ArrowKind Kind Kind
  deriving (Eq,Ord,Show,Read,Generic)

--------------------------------------------------------------------------------

-- instance Out Var
-- instance Out MonoTy

--------------------------------------------------------------------------------
-- WIP: Let's build our simple example:

v = Var "hello"

dd1 = DDef "Exp" (Cat [] [] [])
           [KCons "Con" [ConTy "Int" []] (Cat [] [] [])]


{-
data Exp (e :: *) (a :: *) where
  Con :: Int -> Exp e Int
  Add :: Exp e Int -> Exp e Int -> Exp e Int
  Mul :: Exp e Int -> Exp e Int -> Exp e Int
  Var :: Var e a -> Exp e a
  Abs :: Typ a -> Exp (e,a) b -> Exp e (a -> b)
  App :: Exp e (a -> b) -> Exp e a -> Exp e b
  -}
