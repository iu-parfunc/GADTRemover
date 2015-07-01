{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Ghostbuster.Core
--  ( ghostbuster
--  , ghostbusterDDef )
  where

import Ghostbuster.Types
import Ghostbuster.Utils

import Control.Exception                        ( assert )
import qualified Data.Map                       as HM


type Equations  = (HM.Map TyVar [TyVar])
type Patterns   = (HM.Map TyVar MonoTy)


ghostbuster :: [DDef] -> Prog
ghostbuster ddefs = Prog (ddefs ++ ddefsNew) vdefsNew vtop
  where
  vtop          = VDef "ghostbuster"
                       (ForAll [("a",Star)] (ConTy "Maybe" ["a"]))
                       (EK "Nothing")

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
                  -- , generateUpconv allddefs patterns equalities ddefNormilized
                  ]

toSealedName :: Var -> Var
toSealedName tyName = mkVar ("Sealed" ++ (unMkVar tyName))

-- | The name of the down-conversion function.
--
downName :: TName -> TermVar
downName tyName = mkVar ("down" ++ (unMkVar tyName))

-- | Take a type or data constructor from the higher (pre-stripping) type to the
-- lower one.
--
gadtDownName :: TName -> TName
gadtDownName tyname = mkVar ((unMkVar tyname) ++ "'")

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
    :: [DDef]   -- all declarations in the program, because somehow this is required??
    -> DDef     -- original GADT
    -> KCons    -- GADT constructor under inspection
    -> KCons
gadtToStrippedByClause alldefs up this =
    KCons name' fields' outputs'
  where
    name'       = gadtDownName (conName this)
{-  FIXME: outputs should just be (map (stripMono alldefs))!!! and then take the "keep" prefix -}
    outputs'    = mask (outputs this)

    mask        = map snd . filter fst . zip predicate
    predicate   = maskStrippedVars up

    -- TLM: the old method, doesn't work...
    -- RRN: Why/how??
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
      | isErased alldefs tname -> ConTy (gadtDownName tname)
                                        (map go (onlyKeep alldefs tname monos))
      | otherwise -> ConTy tname (map go monos)
    (VarTy _)           -> monoty
    (TypeDictTy _)      -> monoty

  where
  go = stripMono alldefs

-- | Is the data type affected by Ghostbuster?  Or is it left alone.
isErased :: [DDef] -> TName -> Bool
isErased defs tn = not (null (cVars++sVars))
  where
  DDef {cVars,sVars} = lookupDDef defs tn

-- | Drop all the check and synth type arguments, leaving only keep.
--
onlyKeep :: [DDef] -> TName -> [MonoTy] -> [MonoTy]
onlyKeep alldefs tname monos = take (numberOfKeep alldefs tname) monos

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
    (newfields, equations1)  = equalityRemovalMonoList (fields clause) HM.empty
    (newoutputs, equations2) = equalityRemovalMonoList (outputs clause) equations1

equalityRemovalMonoList :: [MonoTy] -> Equations -> ([MonoTy], Equations)
equalityRemovalMonoList []         _equations = ([], HM.empty)
equalityRemovalMonoList (mono:rest) equations = (newmono:newrest, equations2)
  where
    (newmono, equations1) = equalityRemovalMono mono equations
    (newrest, equations2) = equalityRemovalMonoList rest equations1

equalityRemovalMono :: MonoTy -> Equations -> (MonoTy, Equations)
equalityRemovalMono monoty equations = case monoty of
  VarTy var -> case HM.lookup var equations of
     Just listOfVars -> (toVarTy newvar, HM.insert var (newvar:listOfVars) equations)
     Nothing -> (monoty, HM.insert var [] equations)
  ArrowTy mono1 mono2 -> ((ArrowTy mono1' mono2'), equations2)
     where
     (mono1', equations1) = equalityRemovalMono mono1 equations
     (mono2', equations2) = equalityRemovalMono mono2 equations1
  ConTy name monos -> ((ConTy name newmonos), equations1)
     where
     (newmonos, equations1) = equalityRemovalMonoList monos equations
  _ -> (monoty, HM.empty)
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
    patterns               = HM.union (HM.unions pattern1) (HM.unions pattern2)

pmRemovalMono :: MonoTy -> (MonoTy, Patterns)
pmRemovalMono monoty = case monoty of
  ArrowTy mono1 mono2 -> (toVarTy newvar, patterns)
     where
     (mono1', pattern1) = pmRemovalMono mono1
     (mono2', pattern2) = pmRemovalMono mono2
     patterns = HM.insert newvar (ArrowTy mono1' mono2') (HM.union pattern1 pattern2)
  ConTy name monos -> (toVarTy newvar, patterns)
     where
     (newmonos, pattern1) = unzip (map pmRemovalMono monos)
     patterns = HM.insert newvar (ConTy name newmonos) (HM.unions pattern1)
  _ -> (monoty, HM.empty)
  where
  newvar = (mkVar "newVr")

generateUpconv :: [DDef] -> [Patterns] -> [Equations] -> DDef -> VDef
generateUpconv _alldefs patterns equalities ddef =
  VDef { valName = upconvname
       , valTy   = signature
       , valExp  = bodyOfUp
       }
  where
    upconvname           = upconvName (tyName ddef)
    signature            = ForAll onlyKeepAndCheck (ArrowTy (ConTy (gadtDownName (tyName ddef)) onlyKeepVars) (ConTy "Maybe" [ConTy (toSealedName (tyName ddef)) onlyKeepAndCheckVars]))
    onlyKeepAndCheck     = kVars ddef ++ cVars ddef
    onlyKeepAndCheckVars = map toVarTy (map fst onlyKeepAndCheck)
    onlyKeepVars         = map toVarTy (map fst (kVars ddef))
    bodyOfUp             = ELam ("x", ConTy (gadtDownName (tyName ddef)) []) (ECase "x" (map (generateUpconvByClause patterns equalities) (cases ddef)))

generateUpconvByClause
    :: [Patterns]
    -> [Equations]
    -> KCons
    -> (Pat,Exp)
generateUpconvByClause patterns equalities clause =
  ( Pat (gadtDownName (conName clause)) newVars
  , generateUpconvMono 1 patterns equalities (fields clause) (outputs clause)
  )
  where
    newVars = ["x"]  -- to change in x1 x2 x3..

generateUpconvMono
    :: Int
    -> [Patterns]
    -> [Equations]
    -> [MonoTy]
    -> [MonoTy]
    -> Exp
generateUpconvMono n patterns equalities introduction conclusion =
  case introduction of
    -- here generate pattern matching, equalities, and the finish with:
    --   (EApp "SealedTyp" (EApp (EApp "Arr" "a") "b" )))
    []          -> error "generateUpconvMono: finalise"
    (mono:rest) ->
      case mono of
        VarTy{}      -> error "generateUpconvMono: VarTy"
        ArrowTy{}    -> error "generateUpconvMono: ArrowTy"
        TypeDictTy{} -> error "generateUpconvMono: TypeDictTy"
        ConTy name monos ->
          ECase (EApp (EVar (upconvName name)) (EVar (mkVar ("x" ++ show n))))
                [( Pat (toSealedName name) (map toVarFromMono monos)
                 , generateUpconvMono (n+1) patterns equalities rest conclusion
                 )
                ]

toVarFromMono :: MonoTy -> Var
toVarFromMono (VarTy var) = var
toVarFromMono _           = error "toVarFromMono called with non-VarTy"

upconvName :: Var -> Var
upconvName tyname = mkVar ("upconv" ++ (unMkVar tyname))


-- | Create a down-conversion function.  This is a simple tree-walk
-- over the input datatype, without any laborious type checking
-- obligations to discharge.
--
generateDown :: [DDef] -> TName -> VDef
generateDown alldefs which =
  VDef down (ForAll allVars (mkFunTy (dictTys ++ [startTy]) endTy)) $
   mkLams params $
    ECase "orig" $
    [ (Pat conName args,
      appLst (EVar (gadtDownName conName)) $
       -- FIXME: We need some analysis here that applies a permutation
       -- between tyvars in the KCons and tyvars in the "T a b c" data decl.
       (map (EVar . dictArgify) newDicts) ++
         -- (map EDict newDicts) ++
      [ (dispatch arg ty)
      | (arg,ty) <- zip args fields ])
    | KCons {conName,fields} <- cases
    , let args = (take (length fields) patVars)
          newDicts = getKConsDicts alldefs conName
    ]
  where
  params        = [ (d, TypeDictTy t) | (d,t) <- zip dictArgs erased ]
               ++ [("orig",startTy)]

  dictArgify    = (+++ "_dict")
  dictArgs      = map dictArgify erased

  erased        = map fst $ cVars ++ sVars
  dictTys       = map TypeDictTy erased
  DDef {..}     = lookupDDef alldefs which

  down          = (downName tyName)
  startTy       = (ConTy tyName  (map (VarTy . fst) allVars))
  endTy         = (ConTy tyName' (map (VarTy . fst) kVars))
  tyName'       = gadtDownName tyName
  allVars       = kVars++cVars++sVars

  -- For a type T_i, we dispatch to downT_i
  -- FIXME: We need to add extra dictionary arguments here.
  dispatch vr (ConTy name _)
    | name == which = appLst (EVar (downName name))
                             (map EVar $ dictArgs++[vr])
    | otherwise = error$  "generateDown: UNFINISHED: need some logic here to dispatch a call to "
                  ++ show name ++" while providing the right dictionary arguments."
  -- If we just have an abstract type, we return it.  No recursions.
  dispatch vr (VarTy _)       = EVar vr
  -- For now functions are left alone.  Later we should generate proxies.
  dispatch vr (ArrowTy _ _)   = EVar vr

  -- Are dicts ALLOWED in the input program, or just the output?
  -- For now they are allowed...
  dispatch vr (TypeDictTy _)  = EVar vr
