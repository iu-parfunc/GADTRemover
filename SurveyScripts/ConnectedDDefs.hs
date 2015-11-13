#!/usr/bin/env stack
-- stack --no-system-ghc --verbosity silent --resolver lts-3.8 --install-ghc runghc  --package Ghostbuster
-- | This is a shell script that yanks out all of the connected component
-- data declarations (i.e., all the declarations that refer to each other
-- in the same file) and puts them in separate files -- each file is a
-- separate CC of data declarations.

-- | How to call it and what it does:
-- Let's say we have a dir called "testDir" that has some haskell files
-- that we want to look at (which can be arbitrarily nested). In fact,
-- let's say it looks like this:
--
-- testDir/
-- ├── examples
-- │   ├── DataHashMap.hs
-- │   ├── DataMap.hs
-- │   └── MiniFeldspar.hs
-- └── Foo.hs
--
-- Then we can run: 
--    ./ConnectedDDefs.hs testDir/
-- which tells the tool to gather all haskell files contained in testDir,
-- find the connected components and then output one of these per file and
-- try all the various erasure setting per CC. After this, it places these
-- files under the dir "output" in testDirs/. We would then get a structure
-- that looks like this:
--
-- testDir/
-- ├── examples
-- │   ├── DataHashMap.hs
-- │   ├── DataMap.hs
-- │   └── MiniFeldspar.hs
-- ├── Foo.hs
-- └── output
--     ├── ghostbust_data.hdata
--     └── testDir/
--         └── examples
--             ├── DataHashMap_1.hs
--             ├── DataMap_1ghostbusted000.hs
--             ├── DataMap_1.hs
--             ├── MiniFeldspar_1ghostbusted000.hs
--             └── MiniFeldspar_1.hs
--
-- Notice how the original directory structure is replicated. Also notice
-- that we have the file "ghostbust_data.hdata" at the top-level of the
-- generated directory. This contains information per-connected component.
--
-- You can also specify the output directory for our generated files,
-- however I haven't tested this that much so it is very likely buggy.

{-
 - TODO:
   - DONE Count number of GADTs/ADTs
   - DONE Collect Stats
   - DONE Output stats to file
   - DONE Run Ghostbuster and output to a file inside a directory
   - DONE Fix directory structure?  Nah can handle it.

   - DONE Stream output lines to file
   - DONE -- Added in ghostbuster.hs: Handle HUGE search spaces, look before you leap.
   - Fix CPP: try expanding it first, then fall back to dropping lines on floor.

   - Report final answer for gradual-erasure hypothesis. (??)
   - Report how many fail after ambiguity-check (goal: 0)
   - Make more robust to exceptions


   - Driver: build parallel driver.
   - Driver: set up directories so intermediate files are not in NFS
-}

{-# LANGUAGE DeriveGeneric, OverloadedStrings #-}
module ConnectedDDefs where

import           Control.Exception      
import           System.Directory
import qualified System.FilePath.Find as SFF
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.Process
import           System.IO
import           Text.Printf
import qualified Data.Vector                    as V
import           Data.List
import           Data.Graph
import           Data.Tree
import           Language.Haskell.Exts          as H hiding (name, parse)
import qualified Language.Preprocessor.Cpphs    as CP
import           Data.Functor
import           Control.Monad
import qualified Ghostbuster                    as G
import qualified Ghostbuster.Parser.Prog        as GPP
import qualified Ghostbuster.Types              as GT
import qualified Data.Csv                       as CSV
import           GHC.Generics
import qualified Data.ByteString.Lazy.Char8     as DBLC
import qualified Data.ByteString as DB

data Stats = Stats { numADTs            :: Integer  -- Number of ADTs in this file
                   , numGADTs           :: Integer  -- Number of GADTs in this file
                   , parseSucc          :: Integer
                   , parseFailed        :: Integer  -- These are integers to make it easier to combine
                   , numCCs             :: Integer  -- Number of connected components
                   , failedErasures     :: Integer  -- Number of failed erasure settings
                   , successfulErasures :: Integer  -- Number of successful erasure settings
                   , fileName           :: String   -- File name
                   }
 deriving (Show, Eq, Ord, Generic)

instance CSV.FromNamedRecord Stats
instance CSV.ToNamedRecord Stats
instance CSV.ToRecord Stats
instance CSV.DefaultOrdered Stats

emptyStats :: Stats
emptyStats = Stats { numADTs            = 0
                   , numGADTs           = 0
                   , parseSucc          = 0
                   , parseFailed        = 0
                   , numCCs             = 0
                   , failedErasures     = 0
                   , successfulErasures = 0 
                   , fileName = ""   }

-- | Read in a module and then gather it into a forest of connected components
-- TZ: Treating pairs and arrows as primitive for now
gParseModule :: String -> IO (Either ([Module], [(Integer, Integer)], [GT.Prog]) String)
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
  case parsed of
    ParseOk (Module a b c d e f decls) ->
      let ddefs                    = concatMap gatherDataDecls decls
          (graph, lookupF, memberF)= graphFromEdges $ makeGraph ddefs
          connComps                = components graph
          -- list of list of names of CCs
          connNames = map (nub . (concatMap (smash . lookupF) . flatten)) connComps
          -- list of list of CC ddefs
          cDefs = map (lookupDDef ddefs) connNames
          -- [(numADTs,numGADTs)] -- each pair corresponds to a CC
          countGADTs =
            map (foldr (\x acc -> if isDataDecl x
                                  then (1+ fst acc, snd acc)
                                  else (fst acc, 1 + snd acc))
                       (0,0)) cDefs
          -- Take the various data definitions and output them to a file
          ghostbusterDDefs = map sParseProg cDefs
          -- Make this into a module of CC data defs
          modules = map (Module a b c d e f) cDefs
      in return $ Left (modules, countGADTs, ghostbusterDDefs)
    ParseFailed _ err -> return $ Right $ "ParseFailed: "++show err

-- | We have to replicate some of the functionality from the parser here,
-- but we _can't_ use the gParseProg from the parser since that expects
-- annotations (and adding annotations is actually harder than doing this)
sParseProg :: [Decl] -> GT.Prog
sParseProg decls = GT.Prog ddefs vdefs expr
 where
  ddefs = [GT.DDef (GPP.fromName name) [] (map GPP.kindTyVar tvs) [] cons
            | DataDecl  _ DataType _ name tvs   ks _ <- decls
            , let cons = map (GPP.kconsOfQualConDecl tvs) ks ]
    ++    [GT.DDef (GPP.fromName name) [] (map GPP.kindTyVar tvs) [] cons
            | GDataDecl _ DataType _ name tvs _ ks _ <- decls
            , let cons = map GPP.kconsOfGadtDecl ks]
  vdefs = []
  expr  = GT.VDef "ghostbuster" (GT.ForAll [] (GT.ConTy "()" [])) (GT.EK "()")

-- | Gather all of the data declarations for this module
gatherDataDecls :: Decl -> [Decl]
gatherDataDecls v@(DataDecl _ DataType _ nm tyvars contrs _) = [v]
gatherDataDecls v@(GDataDecl _ DataType _ nm tyvars _kinds contrs _) = [v]
gatherDataDecls _ = []

isDataDecl :: Decl -> Bool
isDataDecl v@(DataDecl _ DataType _ nm tyvars contrs _) = True
isDataDecl  _ = False

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

strOfName :: Name -> String
strOfName (Ident s)  = s
strOfName (Symbol s) = s

nameOfQName :: QName -> Name
nameOfQName qname =
  case qname of
    UnQual n              -> n
    Qual (ModuleName m) n -> Ident (m ++ '.':strOfName n)
    Special x             -> Ident "foo" -- error  ("varOfQName: unhandled case: Special " ++ show x)

---------------------------------------------------------------------------
-- Make the tool runable from the command line.
---------------------------------------------------------------------------

-- We feed this guy a package or a directory
-- This then spits out a ghostbust_data.hdata file in the top level
-- resulting directory that is a CSV that contain information on each
-- connected component that we found and the ghostbusting of that
-- component.
main :: IO ()
main = do
  args <- getArgs
  let (curDir, outputDir) = parseInput args
      -- ick
      header = (DB.intercalate ",") (V.toList (CSV.headerOrder (undefined :: Stats)))
  (putStrLn . show) header
  fls <- SFF.find SFF.always
        (SFF.fileType SFF.==? SFF.RegularFile SFF.&&? SFF.extension SFF.==? ".hs")
        curDir
  -- Get the stats for each file in this package
  createDirectoryIfMissing True outputDir -- Just in case, but it _should_ be there
  hdl <- openFile (outputDir </> "ghostbust_data.hdata") WriteMode
  DB.hPutStrLn hdl header
  stats <- zipWithM (outputCCs hdl) fls (map ((outputDir </>) . dropExtension) fls)
  hClose hdl
  {-mapM_ (putStrLn . show) stats-}

parseInput :: [String] -> (String, String)
-- We place our output in the same directory that we started in but in "output"
parseInput [input]         = (input, (takeDirectory . takeDirectory) input </>  "output" </> input)
parseInput [input, output] = (input, output)
parseInput _               = error "argument parse failed: expected one or two args"

-- | Parse the module and return the list of CCs
outputCCs :: Handle -> String -> String -> IO Stats
outputCCs hdl input outputBase =
   catch go (\e -> 
              do putStrLn $ "--------- Haskell exception while working on " ++ input ++ " --------------"
                 print (e :: SomeException)
                 return $ emptyStats{parseFailed = (parseFailed emptyStats) + 1})
 where 
  go = 
   gParseModule input >>= \res ->
    case res of
      Left (mods, count, gdecls) -> do
        putStrLn $ "--------- Reading File " ++ input ++ " --------------"
        -- Output the file that we're looking at
        zipWithM_ (\mod num -> sWriteProg (outputBase ++ "_" ++ show num ++ ".hs") mod) mods [1..]
        -- Barfing all over the place here... Please don't judge me based on
        -- this code...
        maybeFiles <- zipWithM (\prog num ->
                                 catch (G.fuzzTestDDef True prog
                                        (outputBase ++ "_" ++ show num ++ "ghostbusted" ++ ".hs"))
                                (\e -> putStrLn (show (e :: SomeException)) >>=
                                   (\_ -> return ([Nothing] :: [Maybe (Int, FilePath)]))))
                              gdecls [1..]
        {-mapM_ (putStrLn . show) maybeFiles -}
        {-let (nothings, somethings) = unzip (map (partition (/= Nothing)) maybeFiles)-}
        -- This should be able to be done like the above but for some
        -- reason it's giving faulty results so I'm just going to go with
        -- the in-elegant solution that works...
        let deepSumFilter = \x -> sum (map (toInteger . length . (filter x)) maybeFiles)
            somethings = deepSumFilter (/= Nothing)
            nothings = deepSumFilter (== Nothing)
            stats = Stats { numADTs            = foldr (+) 0 (map fst count)
                       , numGADTs           = foldr (+) 0 (map snd count)
                       , parseSucc          = 1
                       , parseFailed        = 0
                       , numCCs             = toInteger $ length mods
                       , failedErasures     = nothings
                       , successfulErasures = somethings
                       , fileName           = input
                       }
        DBLC.hPutStr hdl $ CSV.encode [stats]
        return stats
      Right str -> do
        putStrLn $ "--------- Failed parse of file " ++ input ++ " --------------"
        putStrLn str
        return $ emptyStats{parseFailed = (parseFailed emptyStats) + 1}

-- | Write the decls out to a file
sWriteProg :: String -> Module -> IO ()
sWriteProg filename (Module a nm c d e f decls) = do
  createDirectoryIfMissing True (takeDirectory filename)
  hdl <- openFile filename WriteMode
  hPutStr hdl (prettyPrint (Module a nm' c d e f decls))
  hClose hdl
  return ()
    where
      nm' = ModuleName (takeBaseName filename)

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
