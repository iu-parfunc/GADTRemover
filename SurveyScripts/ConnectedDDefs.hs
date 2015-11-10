module ConnDefs where

import Data.Graph
import Data.Tree
import           Language.Haskell.Exts          as H hiding (name)
import qualified Language.Preprocessor.Cpphs    as CP
import           Text.PrettyPrint.GenericPretty (Out(doc))

-- | Read in a module and then gather it into a forest of connected components
gParseModule :: String -> IO ()
gParseModule str = do
  parsed <- parseFileContentsWithMode
    ParseMode { parseFilename         = str
              , baseLanguage          = Haskell2010
              , extensions            = glasgowExts
              , ignoreLanguagePragmas = False
              , ignoreLinePragmas     = True
              , fixities              = Just preludeFixities
              }
    <$> (CP.runCpphs CP.defaultCpphsOptions "" =<< (readFile str))
  let Module _ _ _ _ _ _ decls = fromParseResult parsed
      ddefs                    = concatMap gatherDataDecls decls
      (graph, lookupF, memberF)    = graphFromEdges $ makeGraph ddefs
      connComps                = components graph
  putStrLn "\n\n------------------------------\n\n"
  putStrLn $ show connComps
  putStrLn "\n\n------------------------------\n\n"
  mapM_ (putStrLn . show) (makeGraph ddefs)

-- | Gather all of the data declarations for this module
gatherDataDecls :: Decl -> [Decl]
gatherDataDecls v@(DataDecl _ DataType _ nm tyvars contrs _) = [v]
gatherDataDecls v@(GDataDecl _ DataType _ nm tyvars _kinds contrs _) = [v]
gatherDataDecls _ = []

-- [decl, name, [<list of data exprs used>]]
makeGraph :: [Decl] -> [(Decl, Name, [Name])]
makeGraph = map calledConstrs

-- | Return all the constructors (or type constructors) that are used in
-- this data declaration
calledConstrs :: Decl -> (Decl, Name, [Name])
calledConstrs v@(DataDecl _ DataType _ nm tyvars contrs _) =
  let tys = concatMap fromConDecl contrs
  in (v, nm, filter (/= nm) $ concatMap gatherCalled tys)
calledConstrs v@(GDataDecl _ DataType _ nm tyvars _kinds contrs _) =
  let tys = map (\x -> case x of GadtDecl _ _ _ typ -> typ) contrs
  in (v, nm, filter (/= nm) $ concatMap gatherCalled tys)

-- | Rip out the types from the ConDecl for non-GADTs
fromConDecl :: QualConDecl -> [Type]
fromConDecl (QualConDecl _ _ _ decl) = destruct decl
  where
    destruct (ConDecl _ ltys) = ltys
    destruct (InfixConDecl atyp _ btyp) = [atyp,  btyp]
    destruct (RecDecl _ ntys) = map snd ntys

-- | Gather the called constructors from the type
gatherCalled :: Type -> [Name]
gatherCalled (TyFun a b)              = gatherCalled a ++ gatherCalled b
gatherCalled (TyVar v)                = []
gatherCalled (TyCon c)                = [nameOfQName c]
gatherCalled (TyParen t)              = gatherCalled t
gatherCalled (TyBang s t)             = gatherCalled t
gatherCalled (TyTuple _ ts)           = concatMap gatherCalled ts
gatherCalled (TyApp t1 t2)            = gatherCalled t1 ++ gatherCalled t2
gatherCalled other                    = error $ "convertType: unhandled case: " ++ show other

nameOfQName :: QName -> Name
nameOfQName qname =
  let
      strOfName :: Name -> String
      strOfName (Ident s)  = s
      strOfName (Symbol s) = s
  in
  case qname of
    UnQual n              -> n
    Qual (ModuleName m) n -> Ident (m ++ '.':strOfName n)
    Special _             -> error "varOfQName: unhandled case: Special"
