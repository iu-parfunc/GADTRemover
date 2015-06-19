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
                 , kVars :: [(TyVar,Kind)]
                 , cVars :: [(TyVar,Kind)]
                 , sVars :: [(TyVar,Kind)]
                 , cases :: [KCons]
                 }
  deriving (Eq,Ord,Show,Read,Generic)

data KCons = KCons { conName :: Var
                   , fields  :: [MonoTy] -- ^ The \tau_1 through \tau_p arguments
                   , outputs :: [MonoTy] -- ^ The type params fed to 'T' in the RHS
                   }
  deriving (Eq,Ord,Show,Read,Generic)

data MonoTy = VarTy TyVar
            | ArrowTy MonoTy MonoTy
            | ConTy KName [MonoTy]
            | TypeDictTy TName
  deriving (Eq,Ord,Show,Read,Generic)

data Kind = Star | ArrowKind Kind Kind
  deriving (Eq,Ord,Show,Read,Generic)

data Sigma = ForAll [(TyVar,Kind)] MonoTy
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
dd1 = DDef "Exp" [] [("e",Star)] [("a",Star)]
      [ KCons "Con" [int]                          ["e",int]
      , KCons "Add" [exp "e" int, exp "e" int]     ["e",int]
      , KCons "Mul" [exp "e" int, exp "e" int]     ["e",int]
      , KCons "Var" [ConTy "Var" ["e","a"]]        ["e","a"]
      , KCons "Abs" [ConTy "Typ" ["a"], exp (tup "e" "a") "b"]
                                                   (["e",arr "a" "b"])
      , KCons "App" [exp "e" (arr "a" "b"), exp "e" "a"]
                                                   (["e","b"])
      ]
  where
  exp a b = ConTy "Exp"   [a,b]

tup :: MonoTy -> MonoTy -> MonoTy
tup a b = ConTy ","  [a,b]

arr :: MonoTy -> MonoTy -> MonoTy
arr a b = ConTy "->" [a,b]

int :: MonoTy
int = ConTy "Int" []

-- | Var is also ghostbusted with e=checked, a=synth:
dd2 :: DDef
dd2 = DDef "Var" [] [("e",Star)] [("a",Star)]
      [ KCons "Zro" [] (["e","a"])
      , KCons "Suc" [ConTy "Var" ["e","a"]] ([tup "e" "b", "a"])
      ]

dd3 :: DDef
dd3 = DDef "Typ" [] [] [("a",Star)]
      [ KCons "Int" [] ([int])
      , KCons "Arr" [ConTy "Typ" ["a"], ConTy "Typ" ["b"]]
                    ([arr "a" "b"])
      ]

feldspar :: [DDef]
feldspar = [dd1,dd2,dd3]
