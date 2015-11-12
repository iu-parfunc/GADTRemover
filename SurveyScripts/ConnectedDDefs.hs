#!/usr/bin/env stack
-- stack --no-system-ghc --verbosity silent --resolver lts-3.8 --install-ghc runghc --package filemanip --package split
-- | This is a shell script that yanks out all of the connected component
-- data declarations (i.e., all the declarations that refer to each other
-- in the same file) and puts them in separate files -- each file is a
-- separate CC of data declarations.

module ConnectedDDefs where

import           System.Directory
import qualified System.FilePath.Find as SFF
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.Process
import           System.IO
import           Text.Printf
import           Data.List
import           Data.Graph
import           Data.Tree
import           Language.Haskell.Exts          as H hiding (name, parse)
import qualified Language.Preprocessor.Cpphs    as CP
import           Data.Functor
import           Control.Monad

-- | Read in a module and then gather it into a forest of connected components
-- TZ: Treating pairs and arrows as primitive for now
gParseModule :: String -> IO [Module]
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
  let Module a b c d e f decls = fromParseResult parsed
      ddefs                    = concatMap gatherDataDecls decls
      (graph, lookupF, memberF)= graphFromEdges $ makeGraph ddefs
      connComps                = components graph
      -- list of list of names of CCs
      connNames = map (nub . (concatMap (smash . lookupF) . flatten)) connComps
      -- list of list of CC ddefs
      cDefs = map (lookupDDef ddefs) connNames
      -- Make this into a module of CC data defs
      modules = map (Module a b c d e f) cDefs
  return $ modules

-- | Gather all of the data declarations for this module
gatherDataDecls :: Decl -> [Decl]
gatherDataDecls v@(DataDecl _ DataType _ nm tyvars contrs _) = [v]
gatherDataDecls v@(GDataDecl _ DataType _ nm tyvars _kinds contrs _) = [v]
gatherDataDecls _ = []

-- | We don't particularly care about this, but this is the way we get it
-- out of the graph so...
smash :: (a,b,[b]) -> [b]
smash (_, x, y) = x : y

-- | Given a list of decls, and a list of names in this connected
-- component, return all of the decls in this CC
lookupDDef :: [Decl] -> [Name] -> [Decl]
lookupDDef decls names = filter getName decls
  where
    getName (DataDecl _ DataType _ nm tyvars contrs _) = elem nm names
    getName v@(GDataDecl _ _ _ nm _ _ _ _) = elem nm names

-- [decl, name, [<list of data exprs used>]]
makeGraph :: [Decl] -> [(Decl, Name, [Name])]
makeGraph = map calledConstrs

-- | Return all the constructors (or type constructors) that are used in
-- this data declaration
calledConstrs :: Decl -> (Decl, Name, [Name])
calledConstrs v@(DataDecl _ DataType _ nm tyvars contrs _) =
  let tys = concatMap fromConDecl contrs
  in (v, nm, nub (filter (/= nm) $ concatMap gatherCalled tys))
calledConstrs v@(GDataDecl _ DataType _ nm tyvars _kinds contrs _) =
  let tys = map (\x -> case x of GadtDecl _ _ _ typ -> typ) contrs
  in (v, nm, nub (filter (/= nm) $ concatMap gatherCalled tys))

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
gatherCalled (TyPromoted _)           = []
gatherCalled other                    = [] -- error $ "convertType: unhandled case: " ++ show other

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
    Special x             -> error  ("varOfQName: unhandled case: Special " ++ show x)

---------------------------------------------------------------------------
-- Different way of doing things...
---------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  let (curDir, outputDir) = parseInput args
  fls <- SFF.find SFF.always
        (SFF.fileType SFF.==? SFF.RegularFile SFF.&&? SFF.extension SFF.==? ".hs")
        curDir
  zipWithM_ outputCCs fls (map ((outputDir </>) . dropExtension) fls)

parseInput :: [String] -> (String, String)
parseInput [input]         = (input, takeDirectory input </> "output")
parseInput [input, output] = (input, output)
parseInput _               = error "argument parse failed: expected one or two args"

-- OBSOLETE
---------------------------------------------------------------------------
-- Make the tool runable from the command line.
---------------------------------------------------------------------------
-- | Most of this is pulled from the Main.hs file, however most of it is
-- *slightly* different so I couldn't just pull that stuff in.
fmain :: IO ()
fmain = do
  args  <- getArgs
  check args
  let (inputFilename, baseOutputFilename) = parse args
  outputCCs inputFilename baseOutputFilename

-- | Parse the module and return the list of CCs
outputCCs :: String -> String -> IO ()
outputCCs input outputBase = do
  mods <- gParseModule input
  -- Each connected component gets a new name
  zipWithM_ (\mod num -> writeProg (outputBase ++ "_" ++ show num ++ ".hs") mod) mods [1..]

-- | Write the decls out to a file
writeProg :: String -> Module -> IO ()
writeProg filename (Module a nm c d e f decls) = do
  createDirectoryIfMissing True (takeDirectory filename)
  hdl <- openFile filename WriteMode
  hPutStr hdl (prettyPrint (Module a nm' c d e f decls))
  hClose hdl
  return ()
    where
      nm' = ModuleName (takeBaseName filename)

---- BOILERPLATE

check :: [String] -> IO ()
check ["-h"]                 = usage   >> exit
check ["-v"]                 = version >> exit
check []              = error "Invalid arguments -- a file name MUST be passed to getConnectedDefs.  Try -h."
check ls@(_:_:_:_)    = error (printf "Invalid args: %s\n" (show ls))
check _               = return ()

parse :: [String] -> (String, String)
parse [input]         = (input, takeDirectory input </> "output")
parse [input, output] = (input, output)
parse _               = error "parse failed"

exit :: IO a
exit = exitSuccess

usage :: IO ()
usage = do
  version
  putStrLn ""
  putStrLn "Usage: getConnectedComponents [-vh] <inputFile> [<outputFile>]"

version :: IO ()
version = putStrLn "getConnectedComponents version 0.1"
