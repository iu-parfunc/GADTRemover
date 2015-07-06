-- Created:       Fri 03 Jul 2015 11:32:18 AM EDT
-- Last Modified: Sun 05 Jul 2015 10:34:00 PM EDT
{-# LANGUAGE OverloadedStrings #-}

{-|
  - TODO:
    - Add conversion for VDef
    - Make sure we are handling tuples properly in the DDefs.
      * In general: How do we want to handle multiple-arity type
                    constructors that we (may or may not) need to create on the fly?
-}

module Ghostbuster.Parser.Prog where

import qualified Ghostbuster.CodeGen.Prog as GCP
import           Ghostbuster.Types        as G
import           Language.Haskell.Exts    as H
import           Text.PrettyPrint.GenericPretty (Out(doc))
import           Control.Monad
import           Control.Applicative
import           Data.Maybe
import           Data.List
import           Debug.Trace

-- | User facing, they use this datatype in their annotations (see test.hs for an example of this)
data Ghostbust k c s = G k c s
{-data Ghostbust k c s = G {keep :: k , check :: c, synth :: s}-}

-- | Internal representation of a Ghostbust annotation/declaration
data GhostBustDecl k c s = GhostBustDecl TName k c s
  deriving Show

type GhostBustDecls = [(TName,GhostBustDecl [TyVar] [TyVar] [TyVar])]

-- | Take a module name (as a file name to read in) and parse it into our AST
gParseModule :: String -> IO G.Prog
gParseModule str = do
  parsed <- parseFileWithMode ParseMode { parseFilename         = str
                                        , baseLanguage          = Haskell2010
                                        , extensions            = glasgowExts
                                        , ignoreLanguagePragmas = False
                                        , ignoreLinePragmas     = True
                                        , fixities              = Just preludeFixities
                                        }
                              str
  let m@(Module srcLoc moduleName _ _ _ _ decls) = fromParseResult parsed
      prog = gParseProg decls
  {-putStrLn "INPUT PROGRAM: \n\n"-}
  {-putStrLn $ show m-}
  putStrLn "\n\nPARSED PROGRAM\n\n"
  print $ doc prog
  putStrLn "\n\n==============================\n\n"
  {-putStrLn "\n\nCODEGEN'd PROGRAM\n\n"-}
  {-putStrLn $ prettyPrint $ GCP.moduleOfProg prog-}
  {-putStrLn "\n\n==============================\n\n"-}
  return prog

-- | Convert a Haskell name into a Ghostbuster name
fromName :: Name -> G.Var
fromName (Ident str)  = mkVar str
fromName (Symbol str) = mkVar str

-- | Convert a Haskell kind into a Ghostbuster kind
mkKind :: H.Kind -> G.Kind
mkKind KindStar       = G.Star
mkKind KindBang       = G.Star -- Unboxed types are of kind * right?
mkKind (KindFn k1 k2) = G.ArrowKind (mkKind k1) (mkKind k2)

kindTyVar:: TyVarBind -> (G.TyVar, G.Kind)
kindTyVar (KindedVar name kind) = (fromName name, mkKind kind)
kindTyVar (UnkindedVar name)    = (fromName name, G.Star)

-- | Take a list of Decls (i.e., a Haskell module) and return the
--   corresponding Ghostbuster representation. The general mapping is:
-- DDef:
--  --> DataDecl
--  --> GDataDecl
gParseProg :: [Decl] -> G.Prog
gParseProg decls = G.Prog ddefs vdefs exp
  where
   anns  = foldr ((++) . gatherAnnotation) [] decls
   ddefs = foldr ((++) . (gatherDataDecls anns)) [] decls
   vdefs = []
   exp   = gatherExp decls

gatherByTyVar :: G.Var -> GhostBustDecls -> [(TyVar, G.Kind)] -> ([(TyVar, G.Kind)],[(TyVar, G.Kind)],[(TyVar, G.Kind)])
gatherByTyVar name anns ktys =
  case lookup name anns of
    -- not annotated
    Nothing -> ([], [], [])
    -- Annotated
    Just (GhostBustDecl _ k c s) -> (filter (\x -> elem (fst x) k) ktys, filter (\x -> elem (fst x) c) ktys, filter (\x -> elem (fst x) s) ktys)

-- | This reads in a data declaration. Kept, Checked, and Synthesized are marked via an annotation pragma as such:
--   {-# ANN <datatype name> (Ghostbust [<kept>] [<checked>] [<synthesized>])}
--   NOTE: this will be done via a pragma/comment
-- TODO: Need to clean this up and get rid of duplicaton
gatherDataDecls :: GhostBustDecls -> Decl -> [DDef]
gatherDataDecls anns (DataDecl _ DataType _ name tyvars contrs _) =
      let ktys = map kindTyVar tyvars
          tName = fromName name
          (kept', checked, synthesized) = gatherByTyVar tName anns ktys
          kept = ktys \\ (kept' ++ checked ++ synthesized)
      in [DDef  tName kept checked synthesized  (map (convertQualConDecl (map (G.VarTy . fst) ktys)) contrs)]
gatherDataDecls anns (GDataDecl _ DataType _ name tyvars kinds contrs _) =
      let ktys = map kindTyVar tyvars
          tName = fromName name
          (kept', checked, synthesized) = gatherByTyVar tName anns ktys
          kept = ktys \\ (kept' ++ checked ++ synthesized)
      in [DDef tName kept checked synthesized (map convertGadtDecl contrs)]
gatherDataDecls _ _ = []

-- | FIXME: Implement
gatherExp :: [Decl] -> G.VDef
gatherExp x = VDef "a" (ForAll [] (ConTy "Int" []))  (G.EVar "Three")

-- | Gather the annotations for data declarations
gatherAnnotation :: Decl -> [(TName, GhostBustDecl [TyVar] [TyVar] [TyVar])]
gatherAnnotation (AnnPragma _ (Ann name (Paren (App (App (App (Con _) (List ks)) (List cs)) (List ss))))) =
  [((fromName name), GhostBustDecl (fromName name) (map tyVarize ks) (map tyVarize cs) (map tyVarize ss))]
    where
     tyVarize (H.Var (UnQual name)) = fromName name
gatherAnnotation _ = []

-- | For a "regular" data def, the output types are always going to be the
--   input type for that type constructor
convertQualConDecl :: [MonoTy] -> QualConDecl -> KCons
convertQualConDecl outputs (QualConDecl _srcLoc _tyvars _ctx (ConDecl name typs)) =
  KCons (fromName name) (foldr gatherFields [] typs) outputs
    where
      gatherFields :: Type -> [MonoTy] -> [MonoTy]
      gatherFields t acc =
        case convertType t of
          Nothing -> acc
          Just t -> t : acc

      gatherOutputs :: Type -> [MonoTy] -> [MonoTy]
      gatherOutputs acc t =  []

-- | For a GADT data definition, convert it into a corresponding DDef in our internal language
convertGadtDecl :: GadtDecl -> KCons
convertGadtDecl g@(GadtDecl _ name (constr : constrs) typ) =
  let Just (inputs, outputs) = toGadtType typ
  in KCons (fromName name) inputs outputs
convertGadtDecl g@(GadtDecl _ name [] typ) =
  let Just (inputs, outputs) = toGadtType typ
  in KCons (fromName name) inputs outputs

-- | Take a GADT type declaration for a constructor, and convert it into a
--   list of "input" types and a list of "output" types that the constructor
--   will be applied to
toGadtType :: Type -> Maybe ([MonoTy], [MonoTy])
toGadtType typ = do
    first <- convertType typ
    let tyls  = tyList first
    return (take (length tyls -1) tyls, getConTyMonos (drop (length tyls -1) tyls))
 where
   tyList :: MonoTy -> [MonoTy]
   tyList (ArrowTy t1 t2) = tyList t1 ++ tyList t2
   tyList t               = [t]

   getConTyMonos :: [MonoTy] -> [MonoTy]
   getConTyMonos []              = []
   getConTyMonos [ConTy _ monos] = monos

-- | Convert a Type into a MonoTy
convertType :: Type -> Maybe G.MonoTy
convertType (TyFun t1 t2)             = do
  t1' <- convertType t1
  t2' <- convertType t2
  return $ ArrowTy t1' t2'
convertType t@(TyApp t1 t2)           = return $ handleTyApps t
convertType (TyVar name)              = return $ G.VarTy $ fromName name
convertType (TyCon (UnQual name))     = return $ ConTy (fromName name) []
convertType (TyParen typ)             = convertType typ
-- FIXME: How do we (really) want to handle these?
convertType (TyTuple _ typs)          = ConTy (mkVar ("Tup" ++ show (length typs))) <$> mapM convertType typs

-- We don't handle these types (at least inside data constructors)
convertType (TyList typ)              = Nothing
convertType (TyParArray typ)          = Nothing
convertType TyForall{}                = Nothing
convertType (TyInfix typ1 qName typ2) = Nothing
convertType (TyKind typ kind)         = Nothing
convertType (TyPromoted promoted)     = Nothing
convertType (TyEquals typ1 typ2)      = Nothing
convertType (TySplice splice)         = Nothing
convertType (TyBang bangtyp typ)      = Nothing

gatherTypes :: Bool -> Type -> [G.MonoTy]
gatherTypes b (TyApp t1 t2) =
 let t1' = convertType t1
     t2' = convertType t2
 in case t1' of
      Nothing -> case t2' of
                   Nothing -> []
                   Just t  -> [t]
      Just tt1' -> case t2' of
                    Nothing -> [tt1']
                    Just tt2' -> (tt1' : [tt2'])
gatherTypes b (TyFun t1 t2) = if b 
                              then gatherTypes b t1 ++ gatherTypes b t2
                              else let Just t1' = convertType t1
                                       Just t2' = convertType t2
                                   in [ArrowTy t1' t2']
gatherTypes b (TyParen t) = gatherTypes False t
gatherTypes b (TyVar name) = [G.VarTy (fromName name)]
gatherTypes b (TyTuple _ typs) = case  mapM convertType typs of
                                 Just ts -> [ConTy (mkVar ("Tup" ++ show (length typs))) ts]
                                 Nothing -> []
-- FIXME: hacky
gatherTypes b (TyCon (UnQual name)) = [ ConTy (fromName name) [] ]
gatherTypes _ t = error $ "WITH TYPE = " ++ show t

-- | Take a bunch of type applications to a type constructor and turn it into
--   a ConTy applied to a list of those types. We have to do this in order to mimic
--   the type application that haskell has with our language where we don't
--   have "real" type application.
handleTyApps :: Type -> G.MonoTy
handleTyApps typ = let (monotys, constr) = loop typ
                   in constr monotys
 where
   loop :: Type -> ([MonoTy], [MonoTy] -> MonoTy)
   loop (TyApp (TyCon (UnQual name)) typs)      = (gatherTypes True typs, ConTy (fromName name))
   loop (TyApp t1 t2) = let (tylist1, realName) = loop t1
                            (tylist2, _bogus)   = loop t2
                        in (tylist1 ++ tylist2, realName)
   loop t = case convertType t of
              Nothing -> ([], ConTy "bogusParseName")
              Just t  -> ([t], ConTy "bogusParseName")
