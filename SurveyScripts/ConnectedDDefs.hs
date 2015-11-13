#!/usr/bin/env stack
-- stack --no-system-ghc --verbosity silent --resolver lts-3.8 --install-ghc runghc --package Ghostbuster
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
   - DONE Report how many fail after ambiguity-check (goal: 0)
     - Changed fields around to support this
   - DONE Cauterize DDefs so that we don't have missing constructors

   - Fix CPP: try expanding it first, then fall back to dropping lines on floor.
   - Report final answer for gradual-erasure hypothesis. (??)
   - Make more robust to exceptions

   - Driver: build parallel driver.
   - Driver: set up directories so intermediate files are not in NFS
-}

{-# LANGUAGE DeriveGeneric, OverloadedStrings #-}
module ConnectedDDefs where

import           Control.Exception
import           Control.Monad
import qualified Data.ByteString             as DB
import qualified Data.ByteString.Char8       as DBB
import qualified Data.ByteString.Lazy.Char8  as DBLC
import qualified Data.Csv                    as CSV
import           Data.Graph
import           Data.List
import           Data.Maybe
import           Data.Tree
import           Data.Tuple.Utils
import qualified Data.Vector                 as V
import           GHC.Generics
import qualified Ghostbuster                 as G
import qualified Ghostbuster.Parser.Prog     as GPP
import qualified Ghostbuster.Types           as GT
import           Language.Haskell.Exts       as H hiding (name, parse)
import qualified Language.Preprocessor.Cpphs as CP
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import qualified System.FilePath.Find        as SFF
import           System.IO

data Stats = Stats { numADTs            :: Integer  -- Number of ADTs in this file
                   , numGADTs           :: Integer  -- Number of GADTs in this file
                   , parseSucc          :: Integer
                   , parseFailed        :: Integer  -- These are integers to make it easier to combine
                   , numCCs             :: Integer  -- Number of connected components
                   , failedAmb          :: Integer  -- Number of failed erasure settings
                   , failedGBust        :: Integer  -- Number of failed erasure settings
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
                   , failedAmb          = 0
                   , failedGBust        = 0
                   , successfulErasures = 0
                   , fileName           = ""
                   }

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
    ParseOk (Module a b c _ _ f decls) ->
      let ddefs                     = [ d | d <- decls , isDataDecl d ]
          g                         = makeGraph ddefs
          (graph, lookupF, memberF) = graphFromEdges $ map cleanGraph g
          connComps                 = components graph
          -- list of list of names of CCs
          connNames                 = map (nub . (concatMap (smash . lookupF) . flatten)) connComps
          -- list of list of CC ddefs
          defsAndKnownNames         = map unzip $ map (lookupDDef ddefs) connNames
          (cDefs, knownDefNames)    = unzip defsAndKnownNames
          -- [(numADTs,numGADTs)] -- each pair corresponds to a CC
          countGADTs =
            map (foldr (\x acc -> if isDataDecl x
                                  then (1+ fst acc, snd acc)
                                  else (fst acc, 1 + snd acc))
                       (0,0)) cDefs
          -- Take the various data definitions and output them to a file
          cauterizedCDefs  = zipWith3 (cauterize (concatMap thd3 g)) cDefs connNames knownDefNames
          ghostbusterDDefs = map sParseProg cauterizedCDefs
          -- Make this into a module of CC data defs
          modules = map (Module a b c Nothing Nothing f) cauterizedCDefs
       in return $ Left (modules, countGADTs, ghostbusterDDefs)
    ParseFailed _ err -> return $ Right $ "ParseFailed: "++show err

builtin :: [Name]
builtin = map Ident [ "Int", "Bool", "Maybe", "Unit"]   -- Ghostbuster.Types.primitiveTypes


cleanGraph :: (a,b,[(c,d)]) -> (a,b,[c])
cleanGraph (a,b,c) = (a,b, map fst c)

cauterize :: [(Name, Int)] -- List of kinding info for all found TyCons
          -> [Decl] -- List of decls 
          -> [Name] -- List of Names in this CC
          -> [Name] -- List of Names already defined in this CC
          -> [Decl]
cauterize nameKinds decls total defined = newDecls
  where
    -- Get the names we know
    unknownNames = total \\ (defined ++ builtin)
    -- hacky but whatevs right now
    createStubs = concatMap (\nm -> if elem nm unknownNames 
                                    then case lookup nm nameKinds of 
                                            Just i -> [(nm,i)]
                                            Nothing -> []
                                    else ([] :: [(Name,Int)])) unknownNames 
    stubDecls = [ DataDecl (SrcLoc "Foo" 0 0) DataType [] name vars [] []
                | (name, vars) <- map (\(x,y) -> (x, createVars y)) createStubs]
    createVars i = take i $ map (UnkindedVar . Ident . ("a"++) . show) [(0::Int)..]
    newDecls = stubDecls ++ decls

{-[DataDecl (SrcLoc "Test.hs" 1 1) DataType [] (Ident "Foo") [UnkindedVar (Ident "a-}
{-1"),UnkindedVar (Ident "a2"),UnkindedVar (Ident "a3")] [] []]-}
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
maybeDataDecl :: Decl -> Maybe Decl
maybeDataDecl v =
  case v of
    DataDecl  _ DataType _ _ _ _ _   -> Just v
    GDataDecl _ DataType _ _ _ _ _ _ -> Just v
    _                                -> Nothing

isDataDecl :: Decl -> Bool
isDataDecl = isJust . maybeDataDecl

-- | We don't particularly care about this, but this is the way we get it
-- out of the graph so...
smash :: (a,b,[b]) -> [b]
smash (_, x, y) = x : y

-- | Given a list of decls, and a list of names in this connected
-- component, return all of the decls in this CC
lookupDDef :: [Decl] -> [Name] -> [(Decl, Name)]
lookupDDef decls names = concatMap
  (\x -> let (yes, name) = getName names x
         in if yes
            then [(x,name)]
            else [])
  decls
{-filter (getName names) decls-}

getName :: [Name] -> Decl -> (Bool, Name)
getName names (DataDecl _ _ _ nm _ _ _)    = (elem nm names, nm)
getName names (GDataDecl _ _ _ nm _ _ _ _) = (elem nm names, nm)

-- [decl, name, [<list of data exprs used>]]
makeGraph :: [Decl] -> [(Decl, Name, [(Name, Int)])]
makeGraph = map calledConstrs

-- | Return all the constructors (or type constructors) that are used in
-- this data declaration
calledConstrs :: Decl -> (Decl, Name, [(Name, Int)])
calledConstrs v@(DataDecl _ DataType _ nm tyvars contrs _) =
  let tys = concatMap fromConDecl contrs
  in (v, nm, nub (filter ((/= nm) . fst) $ concatMap gatherCalled tys))
calledConstrs v@(GDataDecl _ DataType _ nm tyvars _kinds contrs _) =
  let tys = map (\x -> case x of GadtDecl _ _ _ typ -> typ) contrs
  in (v, nm, nub (filter ((/= nm) . fst) $ concatMap gatherCalled tys))

-- | Rip out the types from the ConDecl for non-GADTs
fromConDecl :: QualConDecl -> [Type]
fromConDecl (QualConDecl _ _ _ decl) = destruct decl
  where
    destruct (ConDecl _ ltys)           = ltys
    destruct (InfixConDecl atyp _ btyp) = [atyp,  btyp]
    destruct (RecDecl _ ntys)           = map snd ntys

-- | Gather the called constructors from the type
gatherCalled :: Type -> [(Name, Int)]
gatherCalled (TyFun a b)    = gatherCalled a ++ gatherCalled b
gatherCalled (TyVar v)      = []
gatherCalled (TyCon c)      = [(nameOfQName c, 0)]
-- gatherCalled (TyCon q)      = case q of
--                                 Special _ -> []
--                                 _         -> [(nameOfQName q, 0)]
gatherCalled (TyParen t)    = gatherCalled t
gatherCalled (TyBang s t)   = gatherCalled t
gatherCalled (TyTuple _ ts) = concatMap gatherCalled ts
-- Tricky
gatherCalled (TyApp t1 t2)  = case gatherCalled t1 of
                                [] -> gatherCalled t2
                                ((nm,kind):rest) -> ((nm, kind + 1) : rest) ++ gatherCalled t2
gatherCalled (TyPromoted _) = []
gatherCalled other          = [] -- error $ "convertType: unhandled case: " ++ show other


strOfName :: Name -> String
strOfName (Ident s)  = s
strOfName (Symbol s) = s

nameOfQName :: QName -> Name
nameOfQName qname =
  case qname of
    UnQual n              -> n
    Qual (ModuleName m) n -> Ident (m ++ '.':strOfName n)
    Special x             -> nameOfSpecialCon x

nameOfSpecialCon :: SpecialCon -> Name
nameOfSpecialCon x =
  Ident $ case x of
    UnitCon            -> "()"
    ListCon            -> "[]"
    FunCon             -> "->"
    Cons               -> ":"
    TupleCon Boxed n   -> "("  ++ replicate (n-1) ',' ++  ")"
    TupleCon Unboxed n -> "(#" ++ replicate (n-1) ',' ++ "#)"
    UnboxedSingleCon   -> "(# #)"


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
  -- putStrLn $ "current directory: " ++ curDir
  -- putStrLn $ "output directory:  " ++ outputDir
  putStrLn (show header)
  fls <- SFF.find SFF.always
        (SFF.fileType SFF.==? SFF.RegularFile SFF.&&? SFF.extension SFF.==? ".hs")
        curDir
  -- Get the stats for each file in this package
  createDirectoryIfMissing True outputDir -- Just in case, but it _should_ be there
  withFile (outputDir </> "ghostbust_data.hdata") WriteMode $ \hdl -> do
    DBB.hPutStrLn hdl header
    _stats <- zipWithM (outputCCs hdl) fls (map ((outputDir </>) . dropExtension) fls)
    {-mapM_ (putStrLn . show) stats-}
    return ()

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
        zipWithM_ (\mod num -> sWriteProg (outputBase ++ "_" ++ show num ++ ".hs") mod) mods [(1::Int)..]
        -- Barfing all over the place here... Please don't judge me based on
        -- this code...
        maybeFiles <- zipWithM (\prog num ->
          -- If we catch an error, that means that we have passed the
          -- ambiguity check but have failed in one of the other passes.
          -- Don't care for now about which pass, just that it happened
                                 catch (G.fuzzTestDDef True prog
                                        (outputBase ++ "_" ++ show num ++ "ghostbusted" ++ ".hs"))
                                (\e -> putStrLn (show (e :: SomeException)) >>=
                                   (\_ -> return ([] :: [Maybe (Int, FilePath)]))))
                              gdecls [(1::Int)..]
        {-mapM_ (putStrLn . show) maybeFiles-}
        {-let (nothings, somethings) = unzip (map (partition (/= Nothing)) maybeFiles)-}
        -- This should be able to be done like the above but for some
        -- reason it's giving faulty results so I'm just going to go with
        -- the in-elegant solution that works...
        let deepSumFilter = \x -> sum (map (toInteger . length . (filter x)) maybeFiles)
            somethings = deepSumFilter (\x -> (x /= Nothing))
            failedAmb = deepSumFilter (== Nothing)
            failedGBust = toInteger  $ sum $ map length $ filter (== []) maybeFiles
            stats = Stats { numADTs         = foldr (+) 0 (map fst count)
                       , numGADTs           = foldr (+) 0 (map snd count)
                       , parseSucc          = 1
                       , parseFailed        = 0
                       , numCCs             = toInteger $ length mods
                       , failedAmb          = failedAmb
                       , failedGBust        = failedGBust
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
  writeFile filename (prettyPrint (Module a nm' c d e f decls))
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
