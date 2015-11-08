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

-- import qualified Ghostbuster.CodeGen.Prog as GCP
import           Ghostbuster.Types        as G hiding (outputs)
import           Language.Haskell.Exts    as H hiding (name)
import           Text.PrettyPrint.GenericPretty (Out(doc))
-- import           Control.Monad
-- import           Control.Applicative
import qualified Data.Set as S
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
  let (Module _srcLoc _moduleName _ _ _ _ decls) = fromParseResult parsed
      prog = gParseProg decls
  {-putStrLn "INPUT PROGRAM: \n\n"-}
  {-putStrLn $ show m-}
  putStrLn "\nDECLS\n\n";  print $ decls
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
kindTyVar (KindedVar nm kind) = (fromName nm, mkKind kind)
kindTyVar (UnkindedVar nm)    = (fromName nm, G.Star)

-- | Take a list of Decls (i.e., a Haskell module) and return the
--   corresponding Ghostbuster representation. The general mapping is:
-- DDef:
--  --> DataDecl
--  --> GDataDecl
gParseProg :: [Decl] -> G.Prog
gParseProg decls =
   trace ("All annotiations found: "++show anns)$
   G.Prog ddefs vdefs ex
  where
   anns  = foldr ((++) . gatherAnnotation) [] decls
   ddefs = foldr ((++) . (gatherDataDecls anns)) [] decls
   vdefs = []
   ex    = gatherExp decls

gatherByTyVar :: G.Var -> GhostBustDecls -> [(TyVar, G.Kind)]
              -> ([(TyVar, G.Kind)],[(TyVar, G.Kind)],[(TyVar, G.Kind)])
gatherByTyVar nm anns ktys =
  let annMentioned = S.fromList (map fst ktys) in
  case lookup nm anns of
    -- not annotated
    Nothing -> ([], [], [])
    -- Annotated
    Just (GhostBustDecl _ k c s) ->
      if S.fromList (k++c++s) == annMentioned then
       (filter (\x -> elem (fst x) k) ktys,
        filter (\x -> elem (fst x) c) ktys,
        filter (\x -> elem (fst x) s) ktys)
      else error$  "Error.\nGhostbuster annotation mentioned variables: "++show annMentioned ++
                   "\nBut datatype is actually indexed by variables: "++show (k++c++s)

-- | This reads in a data declaration. Kept, Checked, and Synthesized are marked via an annotation pragma as such:
--   {-# ANN <datatype name> (Ghostbust [<kept>] [<checked>] [<synthesized>])}
--   NOTE: this will be done via a pragma/comment
-- TODO: Need to clean this up and get rid of duplicaton
gatherDataDecls :: GhostBustDecls -> Decl -> [DDef]
gatherDataDecls anns (DataDecl _ DataType _ nm tyvars contrs _) =
      let ktys = map kindTyVar tyvars
          tName = fromName nm
          (kept', checked, synthesized) = gatherByTyVar tName anns ktys
          kept = ktys \\ (kept' ++ checked ++ synthesized)
      in [DDef  tName kept checked synthesized  (map (convertQualConDecl (map (G.VarTy . fst) ktys)) contrs)]
gatherDataDecls anns (GDataDecl _ DataType _ nm tyvars _kinds contrs _) =
      let ktys = map kindTyVar tyvars
          tName = fromName nm
          (kept', checked, synthesized) = gatherByTyVar tName anns ktys
          kept = ktys \\ (kept' ++ checked ++ synthesized)
      in [DDef tName kept checked synthesized (map convertGadtDecl contrs)]
gatherDataDecls _ _ = []

-- | FIXME: Implement
gatherExp :: [Decl] -> G.VDef
gatherExp _ = VDef "a" (ForAll [] (ConTy "Int" []))  (G.EVar "Three")

-- | Gather the annotations for data declarations
gatherAnnotation :: Decl -> [(TName, GhostBustDecl [TyVar] [TyVar] [TyVar])]
gatherAnnotation (AnnPragma _ (Ann nm (Paren (App (App (App (Con _) (List ks)) (List cs)) (List ss))))) =
  [((fromName nm), GhostBustDecl (fromName nm) (map tyVarize ks) (map tyVarize cs) (map tyVarize ss))]
    where
     tyVarize (H.Var (UnQual nm)) = fromName nm
gatherAnnotation ann@AnnPragma{} =
  trace ("WARNING: ignoring annotation: "++show ann)
  []
gatherAnnotation _ = []

-- | For a "regular" data def, the output types are always going to be the
--   input type for that type constructor
convertQualConDecl :: [MonoTy] -> QualConDecl -> KCons
convertQualConDecl outputs (QualConDecl _srcLoc _tyvars _ctx decl) =
  KCons (fromName (nameOf decl))
        (foldr gatherFields [] (typesOf decl))
        outputs
  where
    gatherFields :: Type -> [MonoTy] -> [MonoTy]
    gatherFields t acc =
      case convertType t of
        Nothing -> acc
        Just t  -> t : acc

    nameOf :: ConDecl -> Name
    nameOf (ConDecl n _)        = n
    nameOf (InfixConDecl _ n _) = n
    nameOf (RecDecl n _)        = n

    typesOf :: ConDecl -> [Type]
    typesOf (ConDecl _ t)        = t
    typesOf (InfixConDecl l _ r) = [l,r]
    typesOf (RecDecl _ ts)       = map snd ts

      -- TODO?
      -- gatherOutputs :: Type -> [MonoTy] -> [MonoTy]
      -- gatherOutputs acc t =  []

-- | For a GADT data definition, convert it into a corresponding DDef in our internal language
convertGadtDecl :: GadtDecl -> KCons
convertGadtDecl (GadtDecl _ name (_constr : _constrs) typ) =
  let Just (inputs, outputs) = toGadtType typ
  in KCons (fromName name) inputs outputs
convertGadtDecl (GadtDecl _ name [] typ) =
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
convertType t@(TyApp _t1 _t2)           = return $ handleTyApps t
convertType (TyVar name)              = return $ G.VarTy $ fromName name
convertType (TyCon (UnQual name))     = return $ ConTy (fromName name) []
convertType (TyParen typ)             = convertType typ
-- FIXME: How do we (really) want to handle these?
convertType (TyTuple _ typs)          = ConTy (mkVar ("Tup" ++ show (length typs))) <$> mapM convertType typs

convertType (TyBang _bangtyp typ)     = convertType typ

-- We don't handle these types (at least inside data constructors)
convertType other = error $ "Unhandled type argument to constructor: "++show other

-- convertType (TyList _typ)              = unhandledType
-- convertType (TyParArray _typ)          = unhandledType
-- convertType TyForall{}                = unhandledType
-- convertType (TyInfix _typ1 _qName _typ2) = unhandledType
-- convertType (TyKind _typ _kind)         = unhandledType
-- convertType (TyPromoted _promoted)     = unhandledType
-- convertType (TyEquals _typ1 _typ2)      = unhandledType
-- convertType (TySplice _splice)         = unhandledType


gatherTypes :: Bool -> Type -> [G.MonoTy]
gatherTypes _b (TyApp t1 t2) =
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
gatherTypes _b (TyParen t) = gatherTypes False t
gatherTypes _b (TyVar name) = [G.VarTy (fromName name)]
gatherTypes _b (TyTuple _ typs) = case  mapM convertType typs of
                                  Just ts -> [ConTy (mkVar ("Tup" ++ show (length typs))) ts]
                                  Nothing -> []
-- FIXME: hacky
gatherTypes _b (TyCon (UnQual name)) = [ ConTy (fromName name) [] ]
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
              Just tt -> ([tt], ConTy "bogusParseName")
