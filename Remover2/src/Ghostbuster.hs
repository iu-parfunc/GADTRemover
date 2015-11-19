{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE ScopedTypeVariables  #-}

-- |  The main module which reexports the primary entrypoints into the Ghostbuster tool.

module Ghostbuster (
      Ghostbust
    , runWGhostbusted
    -- , interpWGhostbusted
    , runghcProg
    , say
    , ghostBustToFile
    , writeProg
    , fuzzTest
    , fuzzTestProg
    , surveyFuzzTest
    , FuzzResult(..), SurveyMode(..), SurveyResult(..)
    , varyBusting
    , isGADT
    ---------------
    , ErasureConfig(..), EraseMode(..)
    , permuteTyArgs
    -- TEMP:
    , maxima, PartCompare, allTheSame
    , erasureConfigPartOrd, verifyGradualErasure
    ) where

import Ghostbuster.Ambiguity   as A
import Ghostbuster.CodeGen
import Ghostbuster.Core        as Core
import Ghostbuster.Interp      ()
import Ghostbuster.LowerDicts
import Ghostbuster.Parser.Prog as Parse
import Ghostbuster.Types

import Control.Exception       (catch, SomeException, throw)
import Control.Monad           (forM, forM_, when)
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Text.Printf
import qualified Data.List  as L

-- import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.Map as M
-- import Data.Functor -- for GHC 7.8.4
-- import Debug.Trace as Trace

-- | Records a result from the fuzzer. Since we want to keep track of each
-- of these fields for each erasure setting
data FuzzResult a = AmbFailure
                  | CodeGenFailure
                  | Success { ghostbustedProg :: Prog, fuzzResult :: a }
 deriving (Show, Eq, Ord)

-- | Each ConnectedComponent of DDefs is surveyed in one of these two modes.
data SurveyMode
  = Exhaustive { searchSpace      :: Integer }
  | Partial    { searchSpace      :: Integer, exploredVariants :: Integer } -- | Temporary version
  | Greedy     { searchSpace      :: Integer
               , exploredVariants :: Integer -- ^ If this equals searchSpace then we shoud have done Exhaustive.
               , exploredRounds   :: (Integer,Integer)
               -- ^ How many complete rounds, then how many variants within the last round.
               }
  deriving Show

data SurveyResult =
     SurveyResult { gadtsBecameASTS :: [TName] -- ^ a subset of the survey'd CC that became ADTs in some variant
                  , surveyMode :: SurveyMode
                  , results :: M.Map ErasureConfig (FuzzResult (Int,FilePath))
                  }
  deriving Show

-- | An erasure configuration for a complete CC.
--  The type arguments are listed in the original order in the datatype.
newtype ErasureConfig = ErasureConfig (M.Map TName [(TyVar, EraseMode)])
  deriving (Eq, Ord)
  -- ^ Note this Ord instance is JUST for using it in data structures.
  --  It is not the semantic notion of ordering (which is a partial order).

instance Show ErasureConfig where
  show (ErasureConfig mp) =
    let ls = M.toList mp
    in "(ErasureConfig, "++
       concat (L.intersperse " "
               [ unMkVar tv ++ "(" ++
                 (concat$ L.intersperse "," (map (unMkVar . fst) vrls))
                  ++ ")"
               | (tv,vrls) <- ls ])
       ++ ":  "++
       concat [ [ eraseModeToChar em
                | (_,em) <- vrls ] ++ " "
              | (_,vrls) <- ls ]
       ++")"

eraseModeToChar :: EraseMode -> Char
eraseModeToChar Kept        = 'K'
eraseModeToChar Checked     = 'C'
eraseModeToChar Synthesized = 'S'

data EraseMode = Kept | Checked | Synthesized  -- ORDER matters.
  deriving (Show,Read,Eq,Ord)

type SingletonErasureConf = (TName,[(TyVar, EraseMode)])


-- | Permute the type args to match a given erasure config, while
-- maintaining the <kept, checked, synth> ordering.  The kept/checked/synth status of
-- each input DDef is IGNORED, and the output DDefs respect the ErasureConfig.
permuteTyArgs :: ErasureConfig -> [DDef] -> [DDef]
permuteTyArgs (ErasureConfig mp) alldefs =
  [ DDef { tyName
         , kVars= map snd ks
         , cVars= map snd cs
         , sVars= map snd ss
         , cases= map (permuteKConsTyApps allPermutes) cases
         }
  | DDef{tyName,cases} <- alldefs
  | ((ks,cs,ss),_) <- allProcessed ]
 where

  allProcessed = map doOne alldefs
  -- This first pass computes the per-type-constructor permutations and new variable layout:
  doOne DDef{tyName,kVars,cVars,sVars} =
    let origOrder = kVars ++ cVars ++ sVars
        Just pairs = M.lookup tyName mp
        ks = [ (ind,(same v1 v2,kind)) | (ind,(v1,Kept       ),(v2,kind)) <- zip3 [0..] pairs origOrder ]
        cs = [ (ind,(same v1 v2,kind)) | (ind,(v1,Checked    ),(v2,kind)) <- zip3 [0..] pairs origOrder ]
        ss = [ (ind,(same v1 v2,kind)) | (ind,(v1,Synthesized),(v2,kind)) <- zip3 [0..] pairs origOrder ]
        -- At each application of TName, we reorder by doing a gather with this permutation.
        -- This will transform the old order, into the new order that respects ErasureConfig.
        permuteInds = map fst ks ++
                      map fst cs ++
                      map fst ss
    in ((ks,cs,ss),permuteInds)

  allPermutes :: M.Map TName Permutation
  allPermutes = M.fromList [ (tyName, perm)
                           | (DDef{tyName}, (_,perm)) <- zip alldefs allProcessed ]

  same v w | v == w    = v
           | otherwise = error $ "permuteTyArgs: internal error, should match: " ++show(v,w)


type Permutation = [Int]

-- | Permute all type applications within the given KCons.
permuteKConsTyApps :: M.Map TName Permutation -> KCons -> KCons
permuteKConsTyApps perms KCons{conName,fields,outputs} =
  KCons{ conName
       , fields  = map (permuteMonoTy perms) fields
       , outputs = map (permuteMonoTy perms) outputs
       }

permuteMonoTy :: M.Map TName Permutation -> MonoTy -> MonoTy
permuteMonoTy perms = go
 where
  go mono =
    case mono of
      VarTy _      -> mono
      TypeDictTy _ -> mono
      ArrowTy a b -> ArrowTy (go a) (go b)
      ConTy tname args ->
        let args' = map go args in
        -- Cauterization has not happened yet.. some TNames may be absent:
        case M.lookup tname perms of
           Just perm -> ConTy tname $ applyPerm perm args'
           Nothing   -> ConTy tname args'

-- This is quadratic... better use on small lists.
applyPerm :: Permutation -> [a] -> [a]
applyPerm inds ls = [ ls !! i | i <- inds ]

-- Take a bunch of per-ddef/TName singleton-ECs, and combine them into
-- all possible complete ErasureConfigs.
--
-- Each of the innermost input lists shoud be for the SAME TName.
cartProdECs :: [[SingletonErasureConf]] -> [ErasureConfig]
cartProdECs perDDefPossibs =
  do (slice :: [SingletonErasureConf]) <- sequence perDDefPossibs
     -- TODO: this doesn't check for name collision.
     return $ ErasureConfig $ M.fromList slice

-- | This defines "stronger"/bigger erasures as erasing more things.
erasureConfigPartOrd :: PartCompare ErasureConfig
erasureConfigPartOrd (ErasureConfig ec1) (ErasureConfig ec2)
  | (M.keys ec1 /= M.keys ec2) = Nothing
  | otherwise = compareMany maybeCs
    where
     maybeCs = map snd $ M.toList $ M.intersectionWithKey fn ec1 ec2
     fn _k left right =
       -- If every variable is "less" on one side than the other...
       let individuals = [ eraseModePartOrd emL emR | ((_,emL), (_,emR)) <- zip left right ] in
       compareMany individuals
       -- if allTheSame individuals
       --    then case individuals of
       --           []    -> Just EQ
       --           (c:_) -> Just c
       --    else Nothing

eraseModePartOrd :: PartCompare EraseMode
eraseModePartOrd x y =
  case (x,y) of
    (_,_) | x==y       -> Just EQ
    (Kept,Checked)     -> Just LT
    (Kept,Synthesized) -> Just LT
    (Checked,Kept)     -> Just GT
    (Synthesized,Kept) -> Just GT
    (Synthesized,Checked) -> Nothing
    (Checked,Synthesized) -> Nothing

-- compareMany :: PartCompare a -> [a] ->

-- | Lift a partial ordering to a product type.
compareMany :: [Maybe Ordering] -> Maybe Ordering
compareMany ls =
   case (allTheSame ls, ls) of
     -- If any two compare differently, then the whole thing is incomparable.
     (False,_) -> Nothing
     (True,[]) -> Just EQ -- Empty tuple
     (True,hd:_) -> hd

-- | Check whether the gradual erasure property held for the configs
-- explored by the Survey.  Return Nothing if the property holds, and
-- otherwise return a message explaining what failed.
--
-- Also return the number of maxima.
verifyGradualErasure :: SurveyResult -> (Int, Maybe String)
verifyGradualErasure SurveyResult{results} =
   (numMaxima,mainResult)
  where
   mainResult =
      if null allResults
         then Nothing
         else Just $
              "Found "++show numMaxima ++
              " distinct failures of gradual-erasure in the SurveyResult of this connected component.\n"++
              "This was while searching under "++show (length maxes)++" different successful maxima.\n"++
              concat allResults

   numMaxima     = length allResults
   maxes         = maxima erasureConfigPartOrd $ M.keys successesOnly
   successesOnly = M.filter isSuccess results

   asList = M.toList results

   allResults = concat allTests
   allTests = map testUnder maxes

   -- There's probaby a more efficient data structure to avoid this quadratic business..
   testUnder ecMax =
     let go [] = []
         go ((ec,fr):rest) =
           let showBoth = "\n Maxima: "++show ecMax++
                          "\n Point:  "++show ec++"\n}"
           in
           case erasureConfigPartOrd ec ecMax of
             Nothing -> go rest
             Just LT -> case fr of
                          Success{} -> go rest
                          f -> ["{GradualErasureFailure: found failure ("++ show f
                                ++") under maxima." ++showBoth] ++
                               go rest
             Just EQ -> go rest -- This is just the maxima itself.
             Just GT -> go rest

     in go asList

isSuccess :: FuzzResult a -> Bool
isSuccess Success{} = True
isSuccess _ = False


--------------------------------------------------------------------------------

-- | Run an expression in the context of ghostbusted definitions.
-- This invokes the complete compiler pipeline, including ambiguity
-- checking, code generation, and running the generated code.
--
-- As for output, it prints the value of the main expression if its
-- type supports printing.  Otherwise, it evaluates it to WHNF.
runWGhostbusted :: Maybe String    -- ^ Descriptive name for this program.
                -> [DDef]          -- ^ Data definitions, including ones to be ghostbusted.
                -> (TyScheme, Exp) -- ^ Main expression to run.
                -> IO ()
runWGhostbusted tname ddefs mainE =
  case ambCheck ddefs of
    Left err -> error$ "Failed ambiguity check:\n" ++err
    Right () ->
      runghcProg tname $
        lowerDicts $ Core.ghostbuster ddefs mainE

-- | Just like runWGhostbusted, but run through the interpreter.
--
--   This pretty prints the resulting `Val`.
-- interpWGhostbusted :: Maybe String -> [DDef] -> (TyScheme, Exp) -> IO ()
-- interpWGhostbusted tname ddefs mainE =
--   case ambCheck ddefs of
--     Left err -> error$ "Failed ambiguity check:\n" ++err
--     Right () ->
--       undefined $
--        lowerDicts $ Core.ghostbuster ddefs mainE


--------------------------------------------------------------------------------

-- TODO: Tim, add an entrypoint here for compiling to disk.  That can
-- be exposed via an executable in the cabal file.

ghostBustToFile :: FilePath -> FilePath -> IO ()
ghostBustToFile input output = do
  Prog prgDefs _prgVals (VDef _name tyscheme expr) <- Parse.gParseModule input
  case ambCheck prgDefs of
    Left err -> error$ "Failed ambiguity check:\n" ++err
    Right () ->
      writeProg output $
       lowerDicts $ Core.ghostbuster prgDefs (tyscheme, expr)

writeProg :: String -> Prog -> IO ()
writeProg filename prog = do
  createDirectoryIfMissing True (takeDirectory filename)
  hdl <- openFile filename WriteMode
  say ("\n Writing to file " ++ filename)$ do
    let contents = prettyProg prog
    hPutStr hdl contents
    hClose hdl
    say "\n File written." $
      return ()


-- | This is similar to `fuzzTestProg`, except instead of assuming a
-- prog with ghostbuster annotations, it starts from nothing and
-- exhaustively (or partially/greedily) explores the search space.
--
--
surveyFuzzTest :: Prog -> FilePath -> IO SurveyResult
surveyFuzzTest (Prog origdefs _prgVals (VDef _name tyscheme expr)) outroot = do
   printf "surveyFuzzTest: Number of CC variants (given ordering limitation): %d\n" numPossib
   putStrLn $ "                Based on ddef possibilities (minus the one degenerate): "++show possibCounts

   putStrLn$ "Total possibilities, without ordering constraint: "++ show (numPossib')
   putStrLn$ "Based on ddef possibilities (minus the one degenerate): "++show possibCounts'

   when (numPossib' < toInteger lIMIT) $ do
     putStrLn $ "Search space size under limit, verifying prediction and possib list match: " ++
              show (L.genericLength possibs' == numPossib')

   if True -- (TEMP Greedy not implemented)
       -- numPossib <= lIMIT
      then doExhaustive
      else doGreedy

  where
   lIMIT :: Int
   lIMIT        = 10000 -- Increasing [2015.11.19]
   numPossib    = product possibCounts - 1 -- Discount degenerate option.
   possibCounts = map ddefNumPossib origdefs

   numPossib'    = product possibCounts' - 1 -- Discount degenerate option.
   possibCounts' = map ddefNumPossib' origdefs

   ------------------------------------------------------------

   doExhaustive =
     do putStrLn $ "Performing an exhaustive search of this CC's erasure space..."
        putStrLn $ "Lengths of per-ddef variants: " ++ show (map length perDDefVariants')
        let
            -- Build a map of whether the original datatypes in the CC were GADTs:
            gadtMap :: M.Map TName Bool
            gadtMap = M.fromList [ (gadtDownName (tyName d), isGADT d) | d <- origdefs ]

        putStrLn $ "These datatypes were originally GADTs: "++show
                   [ unMkVar d | (d,True) <- M.toList gadtMap ]
        mode <- case drop lIMIT possibs' of
                  []         -> return (Exhaustive numPossib')
                  _remaining -> do putStrLn "Search space too big, taking a prefix of the exhaustive enumeration..."
                                   return $ Partial numPossib' (toInteger lIMIT)
        let toexplore = take lIMIT possibs'
        ls <- forM (zip [(0::Int)..] toexplore) $ \ (ind,ec:: ErasureConfig) -> do
          printf "%4d:" ind
          let defs = permuteTyArgs ec origdefs
          forM_ defs $ \ DDef{kVars,cVars,sVars} ->
            putStr $ "  " ++
                     show ( map (unVar . fst) kVars
                          , map (unVar . fst) cVars
                          , map (unVar . fst) sVars)
          putStr "\n"
          fr <- gogo (ind,defs)
          let wasGADT :: [DDef]
              wasGADT = case fr of
                         Success{ghostbustedProg} ->
                            -- Trace.trace ("All the ddefs in the busted prog: "++show(map tyName (prgDefs ghostbustedProg))) $
                            -- Here we find the matching datatype in the ghostbusted output
                            -- for each datatype that started out as a GADT:
                            [ dd | dd <- prgDefs ghostbustedProg
                                 , Just True == (M.lookup (tyName dd) gadtMap) ]
                         CodeGenFailure -> []
                         AmbFailure     -> []
              winners = filter (not . isGADT) wasGADT
          -- putStrLn $ "Here are possible winners: " ++
          --            show (map unMkVar $ map tyName $ wasGADT )
          return ((ec,fr), S.fromList winners)

        let (fuzzRes,gadtsBecameASTS) = unzip ls
        putStrLn $ "All exhaustive survey variants explored, returning."
        let finalSet = S.unions gadtsBecameASTS
            becameADTs = (S.map tyName finalSet)
        -- unless (S.null finalSet) $
        --   -- then putStrLn $ "No datatypes became ADTs from GADTs..."
        putStrLn $ (show$ S.size becameADTs) ++ " datatypes BECAME ADTs but were gADTs."
        return $ SurveyResult (S.toList becameADTs) mode (M.fromList fuzzRes)

   -- Don't force this unless we're exhaustive... gets BIG:
   possibs' :: [ErasureConfig]
   possibs'  = filter (not . isDegenerateEC) (cartProdECs perDDefVariants')
   perDDefVariants' :: [[SingletonErasureConf]]
   perDDefVariants' =  map ddefPossibs origdefs

   -- OLD:
   possibs  :: [[DDef]]
   possibs       = filter (not . isDegenerate) cartesianProd
   cartesianProd = sequence perDDefVariants
   perDDefVariants = map _ddefPossibs_old origdefs

   ------------------------------------------------------------

   doGreedy =
     do putStrLn $ "Search space too big ("++show numPossib++") => greedy partial search of CC's erasure space..."
        return $ SurveyResult [] (Greedy numPossib 0 (0,0)) M.empty

   gogo :: (Int,[DDef]) -> IO (FuzzResult (Int,FilePath))
   gogo (index,defs) =
     let
         (file,ext) = splitExtension outroot
         newName    = file ++ printf "%03d" index <.> ext
     in
     case ambCheck defs of
       Left err -> do
         printf "Possibility %d failed ambiguity check!\nReturned error: %s\n" index err
         return $ AmbFailure
       Right () ->
         (do let newprg = lowerDicts $ Core.ghostbuster defs (tyscheme,expr)
             writeProg newName newprg
             return (Success newprg (index,newName)))
          `catch`
            \e ->
              do putStrLn $ "Unable to run codegen on program "
                 -- The above output to a file, but wrote nothing, so remove it
                 fExists <- doesFileExist newName
                 when fExists $ removeFile newName
                 print (e :: SomeException)
                 return $ CodeGenFailure

isGADT :: DDef -> Bool
isGADT DDef{cases} = any gadtCase cases
  where
  gadtCase KCons{outputs} = not (all isTyVar outputs)
  isTyVar (VarTy _) = True
  isTyVar _         = False


-- | Exclude the possibility that there are no erasures at all.
isDegenerate :: [DDef] -> Bool
isDegenerate = (all nullErasure)
  where
   nullErasure DDef{kVars,sVars} = null kVars && null sVars

isDegenerateEC :: ErasureConfig -> Bool
isDegenerateEC (ErasureConfig mp) =
  and [ all (==Kept) (map snd ls) | (_,ls) <- M.toList mp ]

_varPattern :: DDef -> String
_varPattern DDef{kVars,cVars,sVars} =
  show (length kVars) ++"|"++
  show (length cVars) ++"|"++
  show (length sVars)

allVars :: DDef -> [(TyVar, Kind)]
allVars DDef{kVars,cVars,sVars} = kVars ++ cVars ++ sVars

-- | Number of possible erasures.  This is highly limited by our
-- temporary ORDERING limitation.
ddefNumPossib :: DDef -> Integer
ddefNumPossib dd = combinations
  where
  -- There are (totalVars + 1) ways to place a cursor between/before/after some var.
  -- combinations = ((totalVars + 1) `choose` 2)  -- This is wrong.
  -- Argh, I'm too lazy to figure out the closed for for this atm:
  combinations = sum [ (totalVars + 1 - choice1) | choice1 <- [0..totalVars] ]
  totalVars    = L.genericLength (allVars dd)

-- | Much simpler notion of search space WITHOUT arbitrary ordering constraints.
ddefNumPossib' :: DDef -> Integer
ddefNumPossib' dd = (3 :: Integer) ^ L.genericLength (allVars dd)

-- | Explode a single DDef into all the possible erasure modes.
-- Limited by our ORDERING limitation.
_ddefPossibs_old :: DDef -> [DDef]
_ddefPossibs_old dd =
  let allvs = allVars dd
      totalVars = length allvs
  in
  [ dd{kVars= ks, cVars = cs, sVars = ss}
  | take1 <- [0 .. totalVars]
  , take2 <- [take1 .. totalVars]
  , let ks = take take1 allvs
  , let cs = drop take1 $ take take2 allvs
  , let ss = drop take2 allvs
  ]

-- | New version, search FULL possibility space.
ddefPossibs :: DDef -> [SingletonErasureConf]
ddefPossibs dd =
  do let vars = map fst $ allVars dd
     varSettings <- sequence $ replicate (length vars) [Kept,Checked,Synthesized]
     return (tyName dd, zip vars varSettings)

_chooseWithReplacement :: Integral a => a -> a -> a
_chooseWithReplacement n m = (n + m + 1) `choose` m

choose :: Integral a => a -> a -> a
choose n k = (fact n) `quot` (fact k * fact (n-k))

fact :: (Num a, Ord a) => a -> a
fact n = if n < 2 then 1 else n * fact (n-1)


-- | Try different weakenings of the ghostbuster configuration in the input
-- file, and write the outputs to filepaths at the given root.
--
-- This function immediately parses the input file and returns a list
-- of possible test actions corresponding to different weakenings.
-- Each test action returns an output filepath if it succeeds,
-- plus a simple index for which variant in the space it was.
--
-- Make this return whether it failed ambiguity check (AmbFailure)
-- codgen'd (CodeGen (Int, FilePath)) or failed to codegen (CodeGenFailure)
fuzzTestProg :: Bool -> Prog -> FilePath -> IO [FuzzResult (Int, FilePath)]
fuzzTestProg doStrong (Prog prgDefs _prgVals (VDef _name tyscheme expr)) outroot = do
  putStrLn         $ printf "Number of weakening possibilities below current Ghostbuster erasure point: %d" n
  when (n > lIMIT) $ printf "Testing the first %d weakenings\n" (lIMIT `min` (n `div` lIMIT))
  forM_ (zip [(0::Int)..] taken) $ \ (ind,defs) -> do
    printf "%4d:" ind
    forM_ defs $ \ DDef{kVars,cVars,sVars} ->
      putStr $ "  " ++
               show ( map (unVar . fst) kVars
                    , map (unVar . fst) cVars
                    , map (unVar . fst) sVars)
    putStr "\n"

  sequence [
    let
        (file,ext) = splitExtension outroot
        newName    = file ++ printf "%03d" index <.> ext
    in
    case ambCheck defs of
      Left err -> do
        printf "Possibility %d failed ambiguity check!\nReturned error: %s\n" index err
        return $ AmbFailure

      Right () ->
        (do let newprg = lowerDicts $ Core.ghostbuster defs (tyscheme,expr)
            writeProg newName newprg
            return (Success newprg (index,newName)))
         `catch`
           \e ->
             do putStrLn $ "Unable to run codegen on program "
                -- The above output to a file, but wrote nothing, so remove it
                fExists <- doesFileExist newName
                when fExists $ removeFile newName
                print (e :: SomeException)
                return $ CodeGenFailure
   | (index,defs) <- (zip [(0::Int) ..] taken)
   ]

 where
  lIMIT         = 1024
  busted        = map (varyBusting doStrong) prgDefs
  -- Take the cartesian product of varying the erasure level of each data
  -- type, but filter out any combinations where _all_ of the data types
  -- have only kept variables
  weakenings    = filter (not . all (\DDef{..} -> null cVars && null sVars))
                $ sequence busted
  -- Be careful here: don't just take the length of 'weakenings', as this
  -- could be an enormous list. Instead calculate the length ourselves.
  -- This way we don't need to keep the spine of 'weakenings' in memory.
  n             = product [ length b | b <- busted ]
  taken =
    case splitAt lIMIT weakenings of
      (short,[]) -> short
      (x:_,rest) -> x : take (lIMIT-1) (thin rest)
      _          -> error "impossible case"

  thin []       = []
  thin (x:xs)   = x : thin (drop lIMIT xs)

-- | This produces bustings of a DDef that are WEAKER than the current state.
--   That is, some number of erased variables become unerased.
varyBusting :: Bool -> DDef -> [DDef]
varyBusting doStrong dd@DDef{..} =
    [ dd { kVars = kVars ++ take steal1A cVars ++ take steal1B sVars
            , cVars = drop steal1A cVars ++ take steal2 sVars
            , sVars = drop (steal1B + steal2) sVars
            }
    | steal1A <- [0..length cVars]
    , steal1B <- [0.. if steal1A == length cVars
                        then length sVars
                        else 0]
    -- This attempts the stronger form of gradualizaiton, where synth
    -- vars can be demoted to checked.  I think this form doesn't actually
    -- hold, but we need to pinpoint exactly why.
    , steal2  <- if doStrong
                    then [0 .. length sVars - steal1B]
                    else [0] -- Alternatively, this uses only the simpler gradualization.
    ]

fuzzTest :: Bool     -- ^ Should we attempt the "stronger" version of gradual hypothesis?
         -> FilePath -- ^ Input haskell file
         -> FilePath -- ^ Seed to build output file path
         -> IO [Maybe (Int, FilePath)]
fuzzTest doStrong inpath outroot = do
  prg <- Parse.gParseModule inpath
  fromFuzzResult <$> fuzzTestProg doStrong prg outroot
    where
      fromFuzzResult :: [FuzzResult (Int, FilePath)] -> [Maybe (Int, FilePath)]
      fromFuzzResult = map go
         where
            go (Success _ a) = Just a
            go _ = Nothing

--------------------------------------------------------------------------------

-- Attempt to load the generated code for a Prog and run it using Hint. Since
-- Hint can't interpret a whole module from a string, and we need to write it to
-- file anyway, we could also just compile the module directly using 'runghc' or
-- similar.
--
-- TLM: This is shows how to do it, but won't be usable in our setup. Namely,
--      what should 'a' be? This has to be something defined in an _installed_
--      module imported by both this file and the generated code.
--
-- runghcProg :: (Show a, Typeable a) => Prog -> IO a
-- The alternative here is to just execute programs for effect.

-- | WRite a program to a file
runghcProg :: Maybe String -> Prog -> IO ()
runghcProg Nothing p = runghcProg (Just "Ghostbuster") p
runghcProg (Just tname) prg =
 do
   -- Temporarily keeping these while debugging:
   createDirectoryIfMissing True ghostbustTempDir
   (file,hdl) <- openTempFile ghostbustTempDir ("temp_"++tname++ "_.hs")
  -- withSystemTempFile "Ghostbuster.hs" $ \file hdl -> do
   say ("\n   Writing file to: "++ file) $ do
    let contents = prettyProg prg
    hPutStr hdl contents
    hClose hdl
    say ("   File written.") $ do
  {-
-- Hint version:
                when False $ do
                  x <- fmap (either interpreterError id) $
                    runInterpreter $ do
                      loadModules [ file ]
                      setImportsQ [ ("Ghostbuster", Nothing )
                                  , ("Prelude", Nothing) ]
                      interpret "main" infer
                  say "   Interpreter complete.  Got IO action from loaded program.  Running:" $ do
                   () <- x
                   return ()
  -}
     ExitSuccess <- system $ "runghc "++file
     return ()

ghostbustTempDir :: FilePath
ghostbustTempDir = "./ghostbuster_generated/"

------------------------------------------------------------
-- Helper functions
------------------------------------------------------------

{-
-- Depends on Hint:

interpreterError :: InterpreterError -> a
interpreterError e
  = error
  $ case e of
    UnknownError s      -> s
    NotAllowed s        -> s
    GhcException s      -> s
    WontCompile ss      -> unlines $ map errMsg ss

-}

-- | Print something to console.  This deferred version ONLY chats
-- when there's an exception raised.
say :: String -> IO a ->  IO a
say msg act =
  catch act
    (\e ->
       do hPutStrLn stderr ("\n"++msg)
          throw (e::SomeException))


-- Taken from swish:
--------------------------------------------------------------------------------

-- | Partial ordering
type PartCompare a = a -> a -> Maybe Ordering

-- |This function finds the maxima in a list of partially
--  ordered values, preserving the sequence of retained
--  values from the supplied list.
--
--  It returns all those values in the supplied list
--  for which there is no larger element in the list.
--
maxima :: PartCompare a -> [a] -> [a]
maxima cmp = L.foldl' add []
    where
        add []     e = [e]
        add ms@(m:mr) e = case cmp m e of
            Nothing -> m : add mr e
            Just GT -> ms
            Just EQ -> ms
            Just LT -> add mr e


(#) :: (Ord k, Show k, Show v) => M.Map k v -> k -> v
m # k =
  case M.lookup k m of
    Nothing -> error $ "\nERROR: Map lookup failed, key "++show k++" is absent from map:\n "++
                       take 100 (show m)
    Just v -> v

allTheSame :: (Eq a) => [a] -> Bool
allTheSame [] = True
allTheSame (x:xs) = go x xs
 where
   go _ [] = True
   go x (y:ys) | x == y     = go x ys
               | otherwise  = False
