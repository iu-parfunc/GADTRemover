{-# LANGUAGE OverloadedStrings #-}

{-|
  - TODO:
    - Add conversion for VDef
    - Make sure we are handling tuples properly in the DDefs.
      * In general: How do we want to handle multiple-arity type
                    constructors that we (may or may not) need to create on the fly?
-}

module Ghostbuster.Parser.Prog where

import           Data.List
import qualified Data.Set                       as S
import           Debug.Trace
import           Ghostbuster.CodeGen
import           Ghostbuster.Types              as G hiding (outputs)
import           Language.Haskell.Exts          as H hiding (name)
import qualified Language.Preprocessor.Cpphs    as CP
import           Text.PrettyPrint.GenericPretty (Out(doc))
import           Text.Printf

-- | User facing, they use this datatype in their annotations (see test.hs for an example of this)
data Ghostbust k c s = G k c s
{-data Ghostbust k c s = G {keep :: k , check :: c, synth :: s}-}

-- | Internal representation of a Ghostbust annotation/declaration
--
data GhostbustAnn = GhostbustAnn
  { gbName      :: TName
  , gbKeep      :: [TyVar]
  , gbCheck     :: [TyVar]
  , gbSynth     :: [TyVar]
  }
  deriving Show

-- type GhostBustDecls = [(TName,GhostBustDecl [TyVar] [TyVar] [TyVar])]

-- | Take a module name (as a file name to read in) and parse it into our AST
gParseModule :: String -> IO G.Prog
gParseModule str = do
  parsed <- parseFileContentsWithMode
    (ParseMode { parseFilename         = str
               , baseLanguage          = Haskell2010
               , extensions            = glasgowExts
               , ignoreLanguagePragmas = False
               , ignoreLinePragmas     = True
               , fixities              = Just preludeFixities
               })
    <$> ((CP.runCpphs CP.defaultCpphsOptions "") =<< (readFile str))
  let
      Module _ _ _ _ _ _ decls = fromParseResult parsed
      prog                     = gParseProg decls

  putStrLn "INPUT PROGRAM: \n\n"
  putStrLn $ show parsed

  putStrLn "\nDECLS\n\n";  print $ decls
  putStrLn "\n\nPARSED PROGRAM\n\n"
  print $ doc prog
  putStrLn "\n\n==============================\n\n"
  putStrLn "\n\nCODEGEN'd PROGRAM\n\n"
  putStrLn $ prettyProg prog
  putStrLn "\n\n==============================\n\n"
  return prog

-- | Convert a Haskell kind into a Ghostbuster kind
mkKind :: H.Kind -> G.Kind
mkKind KindStar       = G.Star
mkKind KindBang       = G.Star -- Unboxed types are of kind * right?
mkKind (KindFn k1 k2) = G.ArrowKind (mkKind k1) (mkKind k2)

kindTyVar:: TyVarBind -> (G.TyVar, G.Kind)
kindTyVar (KindedVar nm kind) = (fromName nm, mkKind kind)
kindTyVar (UnkindedVar nm)    = (fromName nm, G.Star)

-- | Take a list of Decls (i.e., a Haskell module) and return the
-- corresponding Ghostbuster representation. The general mapping is:
--
-- DDef:
--  --> DataDecl
--  --> GDataDecl
--
gParseProg :: [Decl] -> G.Prog
gParseProg decls
  = trace (printf "All annotiations found: \n%s\n" (unlines $ map (printf "  %s" . show) anns))
  $ G.Prog ddefs vdefs expr
  where
    anns  = [ convertAnnotation a | AnnPragma _ a <- decls ]
    ddefs = [ convertTypeDecl name tvs t         | TypeDecl _ name tvs t                  <- decls ]
         ++ [ convertDataDecl anns name tvs cons | GDataDecl _ DataType _ name tvs _ ks _ <- decls , let cons = map kconsOfGadtDecl ks ]
         ++ [ convertDataDecl anns name tvs cons | DataDecl  _ DataType _ name tvs   ks _ <- decls , let cons = map (kconsOfQualConDecl tvs) ks ]
    vdefs = []

    -- TODO: generate real ghostbuster test program
    expr  = VDef "ghostbuster" (ForAll [] (ConTy "()" [])) (EK "()")

gatherByTyVar
    :: G.Var
    -> [GhostbustAnn]
    -> [(TyVar, G.Kind)]
    -> ( [(TyVar, G.Kind)]
       , [(TyVar, G.Kind)]
       , [(TyVar, G.Kind)]
       )
gatherByTyVar nm anns ktys =
  let annMentioned = S.fromList (map fst ktys) in
  case find (\a -> nm == gbName a) anns of
    Nothing                     -> ([], [], []) -- No Ghostbuster annotation for this datatype
    Just (GhostbustAnn _ k c s) ->              -- Things to ghostbust!
      if S.fromList (k++c++s) == annMentioned
        then ( filter (\x -> elem (fst x) k) ktys
             , filter (\x -> elem (fst x) c) ktys
             , filter (\x -> elem (fst x) s) ktys
             )
        else error $ "Error: gatherByTyVar.\n"
                  ++ "Ghostbuster annotation mentioned variables: " ++ show annMentioned ++ "\n"
                  ++ "But datatype is actually indexed by variables: "++ show (k++c++s)


-- | Convert a Haskell data definition (ADT or GADT) into a Ghostbuster
-- data declaration.
--
convertDataDecl
    :: [GhostbustAnn]
    -> Name
    -> [TyVarBind]
    -> [KCons]
    -> DDef
convertDataDecl ann nm tvs = DDef name k c s
  where
    name        = fromName nm
    tyvars      = map kindTyVar tvs
    (k,c,s)     = gatherByTyVar name ann tyvars


-- | Convert Ghostbuster annotations on data declarations.
--
-- TODO: We should really pre-filter non-Ghostbuster annotations.
--
convertAnnotation
    :: Annotation
    -> GhostbustAnn
convertAnnotation (Ann nm (Paren (App (App (App (Con _) (List ks)) (List cs)) (List ss)))) =
  GhostbustAnn name kept checked synth
  where
    name    = fromName nm
    kept    = [ varOfQName v | H.Var v <- ks ]
    checked = [ varOfQName v | H.Var v <- cs ]
    synth   = [ varOfQName v | H.Var v <- ss ]
convertAnnotation a =
  error $ printf "convertAnnotation: parse error in Ghostbuster annotation '%s'\n" (show a)


convertTypeDecl
    :: Name             -- name of the type declaration
    -> [TyVarBind]      -- type variables
    -> Type             -- the RHS of the type decl; ignored for now
    -> DDef
convertTypeDecl name tvs _ =
  DDef (fromName name) (map kindTyVar tvs) [] [] []

-- | For an ADT-style data declaration, the output types are always going
-- to be the input type for that type constructor
--
kconsOfQualConDecl
    :: [TyVarBind]
    -> QualConDecl
    -> KCons
kconsOfQualConDecl tvs (QualConDecl _ _ _ decl) = KCons name args res
  where
    (n,t)       = case decl of
                    ConDecl n t        -> (n,t)
                    InfixConDecl l n r -> (n,[l,r])
                    RecDecl n ts       -> (n,map snd ts)
    --
    name        = fromName n
    args        = map convertType t
    res         = map (VarTy . fst . kindTyVar) tvs


-- | For a GADT data definition, convert it into a corresponding DDef in
-- our internal language
--
kconsOfGadtDecl :: GadtDecl -> KCons
kconsOfGadtDecl (GadtDecl _ name _ types) = KCons n args res
  where
    split :: MonoTy -> [MonoTy]
    split (ArrowTy a b) = split a ++ split b
    split x             = [x]
    --
    n           = fromName name
    ts          = split (convertType types)
    args        = init ts
    res         = case last ts of
                    ConTy n' r -> r
                    _          -> error "kconsOfGadtDecl: unexpected error"


-- Convert a Haskell Type into a Ghostbuster MonoTy.
--
-- We have to be careful to handle parenthesis properly, and to turn
-- a collection of type applications to a constructor into ConTy applied to
-- a list of those types.
--
convertType :: Type -> G.MonoTy
convertType = go
  where
    go :: Type -> G.MonoTy
    go (TyFun a b)              = G.ArrowTy (go a) (go b)
    go (TyVar v)                = G.VarTy (fromName v)
    go (TyCon c)                = G.ConTy (varOfQName c) []
    go (TyParen t)              = go t  -- careful here
    go (TyBang s t)             = bang s (go t)
    go (TyTuple _ ts)           = let ts' = map go ts
                                  in  G.ConTy (mkVar (printf "Tup%d" (length ts'))) ts'
    go t@TyApp{}                = let app (TyApp (TyCon c) t) = (c, [go t])
                                      app (TyApp a b)         = let (c,r) = app a in (c, r ++ [go b])
                                      app _                   = error "convertType: unhandled type application"
                                      --
                                      (c,ts)                  = app t
                                  in  G.ConTy (varOfQName c) ts
    go other                    = error $ printf "convertType: unhandled case: %s" (show other)

    bang _ t                    = t
    -- bang BangedTy t             = G.ConTy (mkVar "!")              [t]
    -- bang UnpackedTy t           = G.ConTy (mkVar "{-# UNPACK #-}") [t]


-- | Convert a QName into a Ghostbuster name
--
varOfQName :: QName -> G.Var
varOfQName qname =
  let
      strOfName :: Name -> String
      strOfName (Ident s)  = s
      strOfName (Symbol s) = s
  in
  mkVar $ case qname of
            UnQual n              -> strOfName n
            Qual (ModuleName m) n -> m ++ '.':strOfName n
            Special _             -> error "varOfQName: unhandled case: Special"

-- | Convert a Haskell name into a Ghostbuster name
--
fromName :: Name -> G.Var
fromName (Ident str)  = mkVar str
fromName (Symbol str) = mkVar str

