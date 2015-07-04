{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ParallelListComp           #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Ghostbuster.Core
--  ( ghostbuster
--  , ghostbusterDDef
    -- )
  where

import           Control.Exception ( assert )
import           Data.List (isSuffixOf)
import qualified Data.Map as M
import qualified Data.Set as S
import           Debug.Trace
import           Ghostbuster.TypeCheck1 (unify, runTI, composeSubst)
import           Ghostbuster.Types
import           Ghostbuster.Utils

type Equations  = (M.Map TyVar [TyVar])
type Patterns   = (M.Map TyVar MonoTy)

-- Toggle these to turn on debugging prints:
-- uptrace = trace
uptrace :: String -> t1 -> t1
uptrace _ x = x

downtrace :: String  -> t1 -> t1
-- downtrace = trace
downtrace _ x = x


-- | Given a set of definitions and a "main" expression to execute,
--   generate a full program that executes that expression in the
--   context of the ghostbuster-generated definitions.
ghostbuster :: [DDef] -> (TyScheme,Exp) -> Prog
ghostbuster ddefs (topTy,topExp) = Prog (ddefs ++ ddefsNew) vdefsNew vtop
  where
  vtop = VDef "ghostbuster" topTy topExp

  allddefs      = ddefs ++ primitiveTypes
  bustedDefs    = [ dd | dd@DDef {cVars,sVars} <- allddefs
                       , not (null cVars) || not (null sVars)
                  ]

  result        = map ghostbusterDDef bustedDefs
  ddefsNew      = concat (map fst result)
  vdefsNew      = concat (map snd result)

  ghostbusterDDef :: DDef -> ([DDef], [VDef])
  ghostbusterDDef ddef = (returnDDefs, returnVDefs)
    where
    ddefStripped                = gadtToStripped allddefs ddef
    (ddefNoEquals, equalities)  = equalityRemoval ddef
    (ddefNormilized, patterns)  = pmRemoval ddefNoEquals
    sealed                      = generateSealed ddef

    returnDDefs = [ ddefStripped, sealed ]   -- at the moment, these two.
    returnVDefs = [ generateDown   allddefs (tyName ddef)
                  -- , generateUp allddefs patterns equalities ddefNormilized
                  , genUp2 allddefs (tyName ddef)
                  ]

--------------------------------------------------------------------------------
-- Converting the data types
--------------------------------------------------------------------------------

-- | For a given `Foo`, create the datatype `Foo'`.
--   This replaces *any* references to data-types with erased variables with
--   their stripped counterparts.
--
--   As usual, it takes the global list of data definitions.
gadtToStripped :: [DDef] -> DDef -> DDef
gadtToStripped alldefs up =
  DDef { tyName = gadtDownName (tyName up)
       , kVars  = kVars up
       , cVars  = []
       , sVars  = []
       , cases  = map (gadtToStrippedByClause alldefs up) (cases up)
       }

-- | Generate a mask determining which output variables of the GADT have been
-- dropped. False indicates that the variable is dropped, True if kept. The list
-- is in the usual sequence (kVars ++ cVars ++ sVars).
--
maskStrippedVars
    :: DDef     -- original GADT
    -> [Bool]
maskStrippedVars up
  = assert (length vUp >= length vDown)
  $ assert (length vUp == length ans)
  $ ans
  where
    ans   = go vUp vDown
    vUp   = kVars up   ++ cVars up   ++ sVars up
    vDown = kVars up

    go []     _      = []
    go (_:xs) []     = False : go xs []
    go (x:xs) (y:ys)
      | x == y    = True  : go xs ys
      | otherwise = False : go xs (y:ys)


gadtToStrippedByClause
    :: [DDef]   -- all top-level declarations
    -> DDef     -- original GADT
    -> KCons    -- GADT constructor under inspection
    -> KCons
gadtToStrippedByClause alldefs up this =
    KCons name' fields' outputs'
  where
    name'       = gadtDownName (conName this)
    outputs'    = take (length (kVars up)) (map (stripMono alldefs) (outputs this))
    fields'     = map TypeDictTy (getKConsDicts alldefs (conName this))
               ++ map (stripMono alldefs) (fields this)


-- Switch over all references to `T_i` to `T_i'` IFF T_i includes
-- erased (checked or synthesized) type parameters.  This converts the
-- data type from the "pre-ghostbuster" to "post-ghostbuster" world.
--
stripMono :: [DDef] -> MonoTy -> MonoTy
stripMono alldefs monoty =
  case monoty of
    ArrowTy mono1 mono2 -> ArrowTy (go mono1) (go mono2)
    ConTy tname monos
      | any (containErased alldefs) monos ->
         error$ "stripMono: not handling erased as argument to type constructor: "++show monoty
      | hasErased alldefs tname -> ConTy (gadtDownName tname)
                                        (map go (onlyKeep alldefs tname monos))
      | otherwise -> ConTy tname (map go monos)
    (VarTy _)           -> monoty
    (TypeDictTy _)      -> monoty

  where
  go = stripMono alldefs

-- | Is any type-with-erased-vars mentioned under this `MonoTy`?
containErased :: [DDef] -> MonoTy -> Bool
containErased alldefs mono =
  not $ S.null $
   S.intersection busted
     (gatherTypesMentioned mono)
 where
  busted = S.fromList $
           filter (hasErased alldefs) $
           map tyName alldefs

-- | Is the data type affected by Ghostbuster?  I.e. does it have
-- checked or synthesized type variables?  Or is it left alone?
hasErased :: [DDef] -> TName -> Bool
hasErased defs tn = not (null (cVars++sVars))
  where
  DDef {cVars,sVars} = lookupDDef defs tn

-- | Drop all the check and synth type arguments, leaving only keep.
--
onlyKeep :: [DDef] -> TName -> [MonoTy] -> [MonoTy]
onlyKeep alldefs tname monos = take (numberOfKeep alldefs tname) monos

--------------------------------------------------------------------------------
-- Generating "Sealed" versions of the original data types
--------------------------------------------------------------------------------

generateSealed :: DDef -> DDef
generateSealed (DDef tyName k c s _cases) =
  DDef (toSealedName tyName)
       k        -- kept
       c        -- checked
       []       -- sealed
       [ KCons (toSealedName tyName)
               ((map TypeDictTy synthVars) ++ conTy)
               (map toVarTy (keepVars ++ checkVars))
      ]
  where
    keepVars    = map fst k
    checkVars   = map fst c
    synthVars   = map fst s
    allVars     = keepVars ++ checkVars ++ synthVars
    conTy       = [ConTy tyName (map toVarTy allVars)]

--------------------------------------------------------------------------------
-- Helper "passes" for generateUp:
--------------------------------------------------------------------------------

equalityRemoval :: DDef -> (DDef, [Equations])
equalityRemoval ddef = (ddef {cases = newcases} , patterns)
  where
    (newcases, patterns) = unzip (map equalityRemovalByClause (cases ddef))

equalityRemovalByClause :: KCons -> (KCons, Equations)
equalityRemovalByClause clause =
  ( clause { fields  = newfields
           , outputs = newoutputs
           }
  , equations2
  )
  where
    (newfields, equations1)  = equalityRemovalMonoList (fields clause) M.empty
    (newoutputs, equations2) = equalityRemovalMonoList (outputs clause) equations1

equalityRemovalMonoList :: [MonoTy] -> Equations -> ([MonoTy], Equations)
equalityRemovalMonoList []         _equations = ([], M.empty)
equalityRemovalMonoList (mono:rest) equations = (newmono:newrest, equations2)
  where
    (newmono, equations1) = equalityRemovalMono mono equations
    (newrest, equations2) = equalityRemovalMonoList rest equations1

equalityRemovalMono :: MonoTy -> Equations -> (MonoTy, Equations)
equalityRemovalMono monoty equations = case monoty of
  VarTy var -> case M.lookup var equations of
     Just listOfVars -> (toVarTy newvar, M.insert var (newvar:listOfVars) equations)
     Nothing -> (monoty, M.insert var [] equations)
  ArrowTy mono1 mono2 -> ((ArrowTy mono1' mono2'), equations2)
     where
     (mono1', equations1) = equalityRemovalMono mono1 equations
     (mono2', equations2) = equalityRemovalMono mono2 equations1
  ConTy name monos -> ((ConTy name newmonos), equations1)
     where
     (newmonos, equations1) = equalityRemovalMonoList monos equations
  _ -> (monoty, M.empty)
  where
  newvar = (mkVar "newVar")

pmRemoval :: DDef -> (DDef, [Patterns])
pmRemoval ddef =
  ( ddef { cases = newcases }
  , patterns
  )
  where
    (newcases, patterns) = unzip (map pmRemovalByClause (cases ddef))

pmRemovalByClause :: KCons -> (KCons, Patterns)
pmRemovalByClause clause =
  ( clause { fields  = newfields
           , outputs = newoutputs
           }
  , patterns
  )
  where
    (newfields, pattern1)  = unzip (map pmRemovalMono (fields clause))
    (newoutputs, pattern2) = unzip (map pmRemovalMono (outputs clause))
    patterns               = M.union (M.unions pattern1) (M.unions pattern2)

pmRemovalMono :: MonoTy -> (MonoTy, Patterns)
pmRemovalMono monoty = case monoty of
  ArrowTy mono1 mono2 -> (toVarTy newvar, patterns)
     where
     (mono1', pattern1) = pmRemovalMono mono1
     (mono2', pattern2) = pmRemovalMono mono2
     patterns = M.insert newvar (ArrowTy mono1' mono2') (M.union pattern1 pattern2)
  ConTy name monos -> (toVarTy newvar, patterns)
     where
     (newmonos, pattern1) = unzip (map pmRemovalMono monos)
     patterns = M.insert newvar (ConTy name newmonos) (M.unions pattern1)
  _ -> (monoty, M.empty)
  where
  newvar = (mkVar "newVr")

--------------------------------------------------------------------------------
-- Main generateUp function:

generateUp :: [DDef] -> [Patterns] -> [Equations] -> DDef -> VDef
generateUp _alldefs patterns equalities ddef =
  VDef { valName = upconvname
       , valTy   = signature
       , valExp  = bodyOfUp
       }
  where
    upconvname           = upconvName (tyName ddef)
    signature            = ForAll onlyKeepAndCheck
                                (ArrowTy (ConTy (gadtDownName (tyName ddef)) onlyKeepVars)
                                         (ConTy "Maybe" [ConTy (toSealedName (tyName ddef)) onlyKeepAndCheckVars]))
    onlyKeepAndCheck     = kVars ddef ++ cVars ddef
    onlyKeepAndCheckVars = map toVarTy (map fst onlyKeepAndCheck)
    onlyKeepVars         = map toVarTy (map fst (kVars ddef))
    bodyOfUp             = ELam ("x", ConTy (gadtDownName (tyName ddef)) [])
                                (ECase "x" (map (generateUpByClause patterns equalities) (cases ddef)))

generateUpByClause
    :: [Patterns]
    -> [Equations]
    -> KCons
    -> (Pat,Exp)
generateUpByClause patterns equalities clause =
  ( Pat (gadtDownName (conName clause)) newVars
  , generateUpMono 1 patterns equalities (fields clause) (outputs clause)
  )
  where
    newVars = ["x"]  -- to change in x1 x2 x3..

generateUpMono
    :: Int
    -> [Patterns]
    -> [Equations]
    -> [MonoTy]
    -> [MonoTy]
    -> Exp
generateUpMono n patterns equalities introduction conclusion =
  case introduction of
    -- here generate pattern matching, equalities, and the finish with:
    --   (EApp "SealedTyp" (EApp (EApp "Arr" "a") "b" )))
    []          -> EVar "generateUpMono_FINISHME_finalise"
    (mono:rest) ->
      case mono of
        VarTy{}      -> EVar "generateUpMono_FINISHME_VarTy"
        ArrowTy{}    -> EVar "generateUpMono_FINISHME_ArrowTy"
        TypeDictTy{} -> EVar "generateUpMono_FINISHME_TypeDictTy"
        ConTy name monos ->
          ECase (EApp (EVar (upconvName name)) (EVar (mkVar ("x" ++ show n))))
                [( Pat (toSealedName name) (map toVarFromMono monos)
                 , generateUpMono (n+1) patterns equalities rest conclusion
                 )
                ]

toVarFromMono :: MonoTy -> Var
toVarFromMono (VarTy var) = var
toVarFromMono _           = error "toVarFromMono called with non-VarTy"

--------------------------------------------------------------------------------
-- A second attempt at genUp
--------------------------------------------------------------------------------

-- | This is an attempt at a "single pass" version of the algorithm.
genUp2 :: [DDef] -> TName -> VDef
genUp2 alldefs which =
  uptrace ("\nGENUP2("++ show which ++"), initDictMap " ++show initDictMap) $
  VDef (upconvName which) upFunSig $
    mkLams params $
     ECase "lower" $
     [ (Pat (gadtDownName conName) (kdictargs ++ kvalargs),
       uptrace ("\n  Case: ("++ show conName ++") with denv: "++show denv) $
       openConstraints denv (zip dictArgs cOutputs)
        (\denv'' () ->
           doRecursions alldefs denv'' kc unseal
            (\denv''' ls ->
               -- Before the final sealing, we make sure there is a dict binding for all our output variables:
               bindDictVars toBind existentials (map fst sVars) $
                 seal denv''' $ appLst (EVar conName) ls)))
     | kc@KCons {conName,fields,outputs} <- cases
     , let kdictargs = map dictArgify (getKConsDicts alldefs conName)
           kvalargs  = take (length fields) patVars
           (_kOutputs,cOutputs,sOutputs) = splitTyArgs (getArgStatus alldefs which) outputs
           denv = initDictMap `M.union`
                  M.fromList [ (VarTy v, dictArgify v) | v <- getKConsDicts alldefs conName ]
           -- The other equalities from the RHS we will need for later.
           -- We don't have dictionary variables that give us a handle on these.
           -- Rather, we will need these equalities to fabricate the dictionaries at the end.
           toBind = M.fromList (zip (map fst sVars) sOutputs)
           -- toBind = M.fromList (zip (map fst (kVars++sVars)) (kOutputs ++ sOutputs))
           existentials = trace "FINISHME: genUp2 existentials " S.empty
     ]
 where
  params        = [ (d, TypeDictTy t) | (d,(t,_)) <- zip dictArgs cVars ]
               ++ [("lower",startTy)]

  -- Dictionaries seeded from the inputs to the up function:
  initDictMap :: DictEnv
  initDictMap   = M.fromList $ zip (map (VarTy . fst) cVars) (map (fst) params)

  -- The sig of the up function takes dictionaries for checked args.
  upFunSig = (ForAll (kVars ++ cVars)
                     (mkFunTy (dictTys ++ [startTy]) endTy))

  dictTys       = map (TypeDictTy . fst) cVars
  dictArgs      = map (dictArgify . fst) cVars

  startTy       = ConTy tyName' (map (VarTy . fst) kVars)
  tyName'       = gadtDownName tyName
  DDef{..}      = lookupDDef alldefs which

  -- IFF we have synthesized vars we produce/consume a sealed output:
  -- (Probably easier to always produce a sealed output but seal zero variables.)
  ---------------------------------------------------------
  endTy  | null sVars = ConTy tyName                (map (VarTy . fst) (kVars++cVars))
         | otherwise  = ConTy (toSealedName tyName) (map (VarTy . fst) (kVars++cVars))
  -- This takes the actual value "x" and provides the dict args itself.
  seal _denv x | null sVars = x
               | otherwise  = appLst (EK (toSealedName tyName))
                                     ([ buildDict (VarTy sv)
                                      | (sv,_) <- sVars ] ++ [x])
  unseal :: UnsealFn
  unseal (tn,vr) denv x k
         | null sVars = k denv ([],x)
         | otherwise  =
            let vr' = vr +++ "'"
                sVs = getSVars alldefs tn
                newDictVs = [ dictArgify (tv +++ "_" +++ vr')
                            | tv <- sVs ]
                -- TODO: There may be an issue with needing FRESH type variable names here.
                -- To actually generate the correct code we may need to use scoped type variables.
            in ECase x
               [ ( Pat (toSealedName tn) (newDictVs ++ [vr']),
                 k denv (newDictVs, (EVar vr')))]
  ---------------------------------------------------------

unfinished :: String -> Exp
unfinished _ = "undefined"

getSVars :: [DDef] -> TName -> [TyVar]
getSVars defs = map fst . sVars . lookupDDef defs

getCVars :: [DDef] -> TName -> [TyVar]
getCVars defs = map fst . cVars . lookupDDef defs

type UnsealFn
   = ((TName,TermVar) -- ^
   -> DictEnv
   -> Exp
   -> (Cont ([TermVar],Exp)) -- ^ The continuation receives new dictionaries
   -> Exp)

type Cont a = (DictEnv -> a -> Exp)

-- | All the dictionaries we know about, and which are accessible in our
-- lexical environment through a simple variable reference.
--
-- If `(ty,vr)` is in this map, that means `vr :: TypeDictTy ty`.
type DictEnv = M.Map MonoTy TermVar

-- | Unlike in the down case, we open up ALL the constraints we can
-- based on what the pattern match tells us about the dictionaries
-- we're given as arguments.
openConstraints :: DictEnv -> [(TermVar,MonoTy)] -> (Cont ()) -> Exp
openConstraints denv [] k = k denv ()
openConstraints denv ((d,o):rest) k =
  openConstraint denv d o $
   (\denv' () -> openConstraints denv' rest k)

openConstraint :: DictEnv -> TermVar -> MonoTy -> (Cont ()) -> Exp
openConstraint denv dv outTy k =
 uptrace ("   OpenConstraint, equality : "++show (dv,outTy)++ " in denv "++show denv) $
 let denv' = M.insert outTy dv denv in
 case outTy of
   (VarTy vr) ->
     -- Check if there's a dict variable in scope of type "TypeDictTy va"
     case M.lookup outTy denv of
       Nothing ->
         -- Here we already have the dictionary, and just introduce an alias:
         ELet (dictArgify vr, ForAll [] "_", EVar dv) $
         k denv' ()
       Just termVar ->
         -- Here we have existing variables for both dictionaries, and
         -- must assert they are the same type at runtime.
         EIfTyEq (EVar dv, EVar termVar)
                 (k denv' ()) unreachable
   (ArrowTy t1 t2) -> openConstraint denv dv (ConTy "ArrowTy" [t1,t2]) k
   (ConTy tn ls) ->
     -- Here we check an equality and record that in the denv subsequently:
     let denv'' = M.union (M.fromList (zip ls dictvars)) denv'
         dictvars  = [ dictArgify v | VarTy v <- ls]
     in if length dictvars == length ls
           then ECaseDict (EVar dv)
                    (tn, dictvars,
                     k denv'' ())
                    unreachable
           else error$ "Unfinished: need to recursively process: "++show ls

   (TypeDictTy _) -> error$
      "genUp2:openConstraint - Dicts in inputs not allowed: "++show outTy


-- | Create the recursive calls, breaking open the evidence one at a time.
doRecursions :: [DDef] -> DictEnv -> KCons
             -> UnsealFn
             -> (Cont [Exp]) -> Exp
doRecursions alldefs initDictMap KCons{fields} unseal kont =
  loop (zip patVars fields) initDictMap []
  where
  -- Finally, when we have all args in scope, with the right type
  -- evidence visible, we can make the constructor call:
  loop [] denv args = kont denv (reverse args)

  loop ((var,field):rst) denv args =
    doField denv var field
      (\denv' e -> loop rst denv' (e : args))

  -- Takes the type of the field we are processing.
  doField :: DictEnv -> TermVar -> MonoTy -> (Cont Exp) -> Exp
  doField denv var (ConTy tn tyargs) k
    | hasErased alldefs tn =
       let sTys = [ t | (Synth,t) <- zip (getArgStatus alldefs tn) tyargs ]
           cTys = [ t | (Check,t) <- zip (getArgStatus alldefs tn) tyargs ]
       in dispatchRecursion denv (tn,cTys) (EVar var)
          (\denv' eapp ->
            unseal (tn,var) denv' eapp
              (\denv'' (svs, thisFieldE) ->
                -- Verify results of the recursion:
                openConstraints denv'' (zip svs sTys)
                  (\denv''' () -> k denv''' thisFieldE)))

    | otherwise = k denv (EVar var)
  doField denv var field k
    -- NOTE: one of our current rules is that there are not
    -- `hasErased` types under here:
    | containErased alldefs field =
      error $ "genUp2:doRecursions - erased type not allowed nested under other constructors: "++show field
    | otherwise = k denv (EVar var)


  dispatchRecursion denv (tn,checkedTys) expr k =
    k denv $
    appLst (EVar$ upconvName tn)
           (map (buildDict' denv) checkedTys ++[expr])


buildDict' :: DictEnv -> MonoTy -> Exp
buildDict' denv ty =
  case M.lookup ty denv of
    Just v -> uptrace ("    ! buildDict' short circuited to DictEnv "++show (ty,v)) $
              EVar v
    -- Nothing -> buildDict ty
    Nothing ->
      uptrace ("    ! buildDict' calling off to bindDictVars "++show ty++ " with denv "++show denv) $
      bindDictVars (denvToEqualities denv) existentials (S.toList$ ftv ty) (buildDict ty)
  where
  existentials = trace ("    FIXME: buildDict' existentials") S.empty


-- This is inefficient and ugly... refactor it away
denvToEqualities :: DictEnv -> M.Map TyVar MonoTy
denvToEqualities denv =
  M.fromList
  [ (unDictVar dv,ty) | (ty,dv) <- M.toList denv ]



--------------------------------------------------------------------------------
-- Downward conversion
--------------------------------------------------------------------------------

-- | Create a down-conversion function.  This is a simple tree-walk
-- over the input datatype, without any laborious type checking
-- obligations to discharge.
--
generateDown :: [DDef] -> TName -> VDef
generateDown alldefs which =
  VDef (gendownName tyName) (ForAll allVars (mkFunTy (dictTys ++ [startTy]) endTy)) $
    mkLams params $
     ECase "orig" $
     [ (Pat conName args,
       -- Call the (lower) data constructor right at the top:
       appLst (EVar (gadtDownName conName)) $
        (map (\dv -> bindDictVars substs existentials [dv] (buildDict (VarTy dv))) newDicts) ++
        -- Perform the recursions inside the operands:
       [ (dispatch substs existentials arg ty)
       | (arg,ty) <- zip args fields ])
     | kc@KCons {conName,fields,outputs} <- cases
     , let args = (take (length fields) patVars)
           newDicts = getKConsDicts alldefs conName
           existentials = allExistentials kc
           substs = case runTI $
                         do ls <- mapM (\((arg,_),rhsTy) -> unify (VarTy arg) rhsTy)
                                       (zip allVars outputs)
                            return $ foldl1 composeSubst ls of
                      (Left e,_) -> error$ "generateDown: error unifying: "++show e
                      (Right s,_) -> s
     ]
 where
  params        = [ (d, TypeDictTy t) | (d,t) <- zip dictArgs erased ]
               ++ [("orig",startTy)]

  dictArgs      = map dictArgify erased

  erased        = map fst $ cVars ++ sVars
  dictTys       = map TypeDictTy erased

  startTy       = ConTy tyName  (map (VarTy . fst) allVars)
  endTy         = ConTy tyName' (map (VarTy . fst) kVars)
  tyName'       = gadtDownName tyName
  allVars       = kVars++cVars++sVars
  DDef{..}      = lookupDDef alldefs which

  -- For a type T_i, we dispatch to downT_i
  -- We need to build dictionaries for its type-level arguments:
  dispatch substs existentials vr (ConTy name tyargs)
    | hasErased alldefs name
    = appLst (EVar (gendownName name))
             (map (\ty -> bindDictVars substs existentials (S.toList$ ftv ty) (buildDict ty))
                   tyargs ++ [EVar vr])
    | otherwise = EVar vr

  -- If we just have an abstract type, we return it.  No recursions.
  dispatch _ _ vr (VarTy _)       = EVar vr
  -- For now functions are left alone.  Later we should generate proxies.
  dispatch _ _ vr (ArrowTy _ _)   = EVar vr

  -- Are dicts ALLOWED in the input program, or just the output?
  -- For now they are allowed...
  dispatch _ _ vr (TypeDictTy _)  = EVar vr


-- | Build the final dictionary, assuming all the required variable
-- names are in scope.
buildDict :: MonoTy -> Exp
buildDict oty =
  downtrace ("    buildDict for "++show oty++ " -> "++show res) res
 where
  res = loop oty
  loop ty =
    case ty of
      VarTy t       -> EVar $ dictArgify t
      ConTy k ls    -> appLst (EDict k)         (map loop ls)
      ArrowTy t1 t2 -> appLst (EDict "ArrowTy") [loop t1, loop t2]
      TypeDictTy _  -> error $ "Core.buildDict: should never build a dictionary of a dictionary: "++show ty

-- | Bind dictionaries for ALL variable names that occur free in the monotype.
--   Use a substitution to determine relevant equalities.
bindDictVars :: M.Map TyVar MonoTy -> S.Set TyVar -> [TyVar] -> Exp -> Exp
bindDictVars subst existentials varsToBind body =
    -- trace ("\n*** Start BINDDICTVARS for mono "++show mono++" with existentials "++show existentials) $
    loop (varsToBind)
  where

  flipped = M.fromList $
            [ (v,VarTy w) | (w,VarTy v) <- M.toList subst ]

  subst' = M.union flipped subst

  loop :: [TyVar] -> Exp
  loop []       = -- trace ("   all vars bound, now buildDict of "++show mono) $
                  body
  loop (fv:rst) =
    let fv_dict = dictArgify fv in
    -- trace ("  bindDictVars:loop, creating binding for "++show fv)$
    case M.lookup fv subst' of
      Nothing ->
         ELet (fv_dict, ForAll [] "_", findPath fv)
              (loop rst)
      Just ty ->
       -- fv is equal to ty, thus we use it to build the dict
       let dicttype =
             case ty of
               -- VarTy v -> TypeDictTy v -- This invariant is broken with names like arr_a'_dict
               _       -> "_"
       in
       ELet (fv_dict, ForAll [] dicttype, buildDict ty)
            (loop rst) -- (wrap (loop rst))
       -- trace ("FINISHME: buildDictVar "++show (fv) ++" -> " ++show subst) $

  -- Compute the dictionary for `fv` by digging into other dictionaries.
  findPath fv
    | S.member fv existentials = specialExistentialDict
    | otherwise =
      case filter (\(_,ty) -> S.member fv (ftv ty)) $
                 M.toList subst of
        (start,path):_ -> digItOut start path fv
        -- The reason we get here is that a~a constraints don't add anything
        -- to the substitution:
        [] -> EVar$ dictArgify fv
          -- EVar$mkVar$ "(failed to find "++show fv++" in subst "++show subst++")"
          -- error$ "generateDown: failed to find "++show fv++" in subst "++show subst

  digItOut :: TyVar -> MonoTy -> TyVar -> Exp
  digItOut cursor monty dest =
    -- trace ("   Digitout "++ show (cursor, monty, dest)) $
    case monty of
      VarTy x -> if x == dest
                    then EVar cursor
                    else error "internal error, generateDown"
      ArrowTy x1 x2 -> ECaseDict (EVar $ dictArgify cursor)
                          ( "ArrowTy"
                          , ["left","right"]
                          , if S.member dest (ftv x1)
                               then digItOut "left"  x1 dest
                               else digItOut "right" x2 dest
                          )
                          unreachable
      ConTy tn ls -> ECaseDict (EVar $ dictArgify cursor)
                        ( tn
                        , take (length ls) patVars
                        , head [ digItOut vr arg dest | vr  <- patVars
                                                      | arg <- ls
                                                      , S.member dest (ftv arg)
                               ]
                        )
                        unreachable
      TypeDictTy _ -> EVar cursor -- Test me.  How to make this reachable?


--------------------------------------------------------------------------------
-- Conventions and Naming
--------------------------------------------------------------------------------

-- | This isn't bound within our core language, but we could make it
-- part of a prelude and define it as Omega.  Also, we know it will be
-- bound in the generated Haskell code.
--
-- Alternatively, we could simply include a core form "EErr".
unreachable :: Exp
unreachable = (EVar "undefined")

specialExistentialDict :: Exp
specialExistentialDict = EDict "Existential"

upconvName :: Var -> Var
upconvName tyname = mkVar ("up" ++ (unMkVar tyname))

toSealedName :: Var -> Var
toSealedName tyName = mkVar ("Sealed" ++ (unMkVar tyName))

-- | The name of the down-conversion function.
--
gendownName :: TName -> TermVar
gendownName tyName = mkVar ("down" ++ (unMkVar tyName))

-- | Take a type or data constructor from the higher (pre-stripping) type to the
-- lower one.
--
gadtDownName :: TName -> TName
gadtDownName tyname = mkVar ((unMkVar tyname) ++ "'")

-- | Establish a (local) convention for how to name dictionary arguments
dictArgify :: TyVar -> TermVar
dictArgify = (+++ "_dict")

unDictVar :: TermVar -> TyVar
unDictVar v | isSuffixOf "_dict" (unMkVar v) = mkVar $ reverse $ drop 5 $
                                               reverse $ unMkVar v
            | otherwise = error$ "unDictVar: bad input "++show v
