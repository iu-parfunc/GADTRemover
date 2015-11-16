{-# LANGUAGE OverloadedStrings #-}

module Ghostbuster.CodeGen.Prog
  where

import Ghostbuster.Types                                as G
import Ghostbuster.CodeGen.DDef
import Ghostbuster.CodeGen.VDef
-- import Ghostbuster.Showable

import Language.Haskell.Exts                            as H
import Language.Haskell.Exts.SrcLoc                     ( noLoc )
-- import qualified Data.Set                               as S


moduleOfProg :: Prog -> Module
moduleOfProg (Prog ddefs vdefs vtop) =
  Module
    noLoc
    (ModuleName "Ghostbuster")          -- TLM: module name???
    pragmas                             -- top-level module pragmas
    Nothing                             -- warning text, e.g. deprecated
    Nothing                             -- export spec; just export everything for now
    imports                             -- import declarations
    decls                               -- top-level module declarations
  where
    pragmas     = [ LanguagePragma noLoc [ Ident "GADTs" ]
                  , LanguagePragma noLoc [ Ident "ScopedTypeVariables" ]
                  , LanguagePragma noLoc [ Ident "BangPatterns" ]
                  , LanguagePragma noLoc [ Ident "MagicHash" ]
                  -- , LanguagePragma noLoc [ Ident "EmptyCase" ]
                  , OptionsPragma noLoc (Just GHC) " -Wall "
                  -- , OptionsPragma noLoc (Just GHC) " -fdefer-type-errors "
                  , OptionsPragma noLoc (Just GHC) " -fno-warn-unused-binds "
                  , OptionsPragma noLoc (Just GHC) " -fno-warn-unused-matches "
                  , OptionsPragma noLoc (Just GHC) " -fno-warn-name-shadowing "
                  -- , OptionsPragma noLoc (Just GHC) " -fno-warn-dodgy-imports "
                  -- , OptionsPragma noLoc (Just GHC) " -fno-warn-unused-imports "
                  ]

    mkImport n  = ImportDecl noLoc (ModuleName n) False False False Nothing Nothing
    imports     = [ mkImport "Prelude" $ Just (True, builtinTypes)
                  ,(mkImport "Prelude" Nothing) { importQualified = True }
                  -- , mkImport "Data.Typeable" Nothing
                  ]

    ddefs'      = ddefs ++ primitiveTypes       -- Add the "Prelude" types
    canshow _   = False
    -- showable    = showableDefs ddefs'
    -- canshow tn  = S.member tn showable

    topShowable = case valTy vtop of
                    ForAll [] (ConTy tn _) -> canshow tn
                    _                      -> False

    decls       = map (\d -> gadtOfDDef (canshow (tyName d)) d) ddefs'
               ++ concatMap declOfVDef vdefs
               ++ declOfVDef vtop
               ++ declOfVDef (mkMain topShowable vtop)

builtinTypes :: [ImportSpec]
builtinTypes = map (IAbs      . Ident) types
            ++ map (IThingAll . Ident) ctors
  where
    types       = [ "Char", "Float", "Double", "Int", "Word", "Integer", "String", "FilePath", "IO", "IOError", "Ordering", "Rational", "Real", "ShowS", "String" ]
    ctors       = [ "Bool", "Maybe", "Either" ]
    -- ctypes      = [ "CChar", "CSChar", "CUChar", "CFloat", "CDouble", "CShort", "CUShort", "CInt", "CUInt", "CLong", "CULong", "CLLong", "CULLong" ]
    -- ints        = [ "Int8", "Int16", "Int32", "Int64" ]
    -- words       = [ "Word8", "Word16", "Word32", "Word64" ]
    -- tuples      = map (\i -> "(" ++ replicate i ',' ++ ")") [(0::Int)..14]


mkMain :: Bool -> VDef -> VDef
mkMain doprint vtop =
  VDef { valName = "main"
       , valTy   = ForAll [] (ConTy "Prelude.IO" [ConTy "()" []])
       , valExp  = if doprint
                      then EApp "print" (G.EVar (valName vtop))
                      else EApp (EApp "seq" (G.EVar (valName vtop)))
                                (EApp "return" (EK "()"))
       }
