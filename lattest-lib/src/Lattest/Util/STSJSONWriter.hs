{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Lattest.Util.STSJSONWriter (
  stsToJSONFile,
  stsListToJSONFile,
) where

import Data.Aeson (object, (.=))
import Data.Bifunctor (Bifunctor(..))
import Data.Constraint.Extras (Has(..))
import Data.Dependent.Sum (DSum(..))
import Data.Some (Some (..))
import Lattest.Model.Alphabet (SymInteract (..), SymGuard, IOAct, isOutputInteract, isInputInteract)
import Lattest.Model.Automaton (Valuation, AutSyntax (..), STStdest (..))
import Lattest.Model.BoundedMonad
import Lattest.Model.StandardAutomata (IOSTS, allLocations)
import Lattest.Model.Symbolic.Expr (Variable (..), Val, Type (..), ExprType (..), VarModel, ExprView(..))
import Lattest.Model.Symbolic.Internal.ExprDefs (Expr(..))
import Lattest.Model.Symbolic.Internal.ExprImpls (Valuation(..), Val (..), VarModel (..))
import Lattest.SMT (RCSet)
import qualified Data.Aeson as JSON
import qualified Data.Aeson.KeyMap as JSON
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Debug.Trace
import qualified Data.List as List

-- TODO: Do we want to export the STS with the check guards?

someVarName :: Some Variable -> String
someVarName (Some v) = varName v

-- | Assign every location a string id, TODO find a nice way to flatten them
-- currently just showing, not sure what's wrong with that?
assignLocationIds :: (Show loc) => Set.Set loc -> Map.Map loc String
assignLocationIds = Map.fromSet show

-- | The initial location(s): single id for atomic, or an array of ids when the initial
-- location is a conjunction.
initLocationJSON :: Ord loc => Map.Map loc String -> FreeLattice loc -> JSON.Value
initLocationJSON locIds locs'
  | Left err   <- asConjunction locs' = error $ "iniLocationJSON error: " <> err
  | Right locs <- asConjunction locs' = JSON.toJSON $ map (locIds Map.!) $ Set.toList locs

initValue :: Valuation -> JSON.Value
initValue valuation = JSON.toJSON m
  where
    m :: Map.Map String JSON.Value
    m = Map.fromList $ map (\(var :=> val) -> (varName var, JSON.toJSON val)) $ DMap.assocs $ runValuation valuation

instance JSON.ToJSON (Val a) where
  toJSON (Val a) = has @JSON.ToJSON (typeOf a) $ JSON.toJSON a

instance Has JSON.ToJSON Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    CharType -> k
    UnitType -> k
    ListType tp -> has @JSON.ToJSON tp k
    SetType tp -> has @JSON.ToJSON tp k
    SumType a b -> has @JSON.ToJSON a $ has @JSON.ToJSON b k
    TupleType a b -> has @JSON.ToJSON a $ has @JSON.ToJSON b k

deriving instance (JSON.ToJSON a) => JSON.ToJSON (RCSet a)

isEmptySwitch :: Switch -> Bool
isEmptySwitch (Switch _ act gal) =
    (isForbidden gal && isOutputInteract act) || (isUnderspecified gal && isInputInteract act)

-- | Given ID, STS, the names of guards and assignments, and the initial valuation, make a JSON
stsToJSON :: (Ord loc, Show loc) => String -> IOSTS FreeLattice loc String String -> Map.Map (Expr Bool) String -> Map.Map VarModel String -> Valuation -> JSON.Value
stsToJSON sid sts guardmap assmap valuation =
    object
        [ "id" .= sid
        , "initial_location" .= initLocationJSON locIds (initConf sts)
        , "initialValuation" .= initValue valuation
        , "locations" .= Map.elems locIds
        , "switches" .= switches''
        -- , "parameters" .= params -- already wrote this, but it uses a different representation of structures, so probably better to just reuse the ones from before merging
        -- , "inputGates" .= -- not needed
        -- , "outputGates" .= -- not needed
        -- , "locationVariables" .= -- not needed
        -- , "guards" .= -- not needed
        -- , "assignments" .= -- not needed
        ]
    where
    locs = allLocations sts
    locIds = assignLocationIds locs
    -- alph = alphabet sts
    switches = Set.toList $ Set.unions $ Set.map (\l -> Set.fromList $ map (l,) $ Map.toList $ transRel sts l) locs
    switches' = map (\(l,(act, ml)) -> Switch (locIds Map.! l) act (bimap (\(STSLoc (g,a)) -> (getGuard g guardmap, getassignment a)) (locIds Map.!) <#> ml)) switches
    switches'' = filter (not . isEmptySwitch) switches'
    -- ws = buildSwitches locIds sts locs

    -- The assignment may be the union of several assignments
    getassignment :: VarModel -> [String]
    getassignment a
      | Just nm <- assmap Map.!? a = [nm]
      | otherwise = map lookupOne $ DMap.assocs $ runVarModel a
      where
        lookupOne (var :=> expr)
          | Just nm <- assmap Map.!? VarModel (DMap.singleton var expr) = nm
          | otherwise = error $ "Assignment not found: " <> show a <> ". Looked in: " <> show assmap
    -- params = Map.fromList $ map (\(Some (Variable nm tp)) -> (nm, Some tp)) $ Set.toList $ Set.unions $ Set.map (\(SymInteract _ vs) -> Set.fromList vs) alph

data Switch = Switch String (SymInteract (IOAct String String)) (FreeLattice (([String], [String]), String))
instance JSON.ToJSON Switch where
  toJSON (Switch loc act guardassignmentloc)
   | isForbidden guardassignmentloc && isOutputInteract act = object []
   | isUnderspecified guardassignmentloc && isInputInteract act = object []
   | Left err <- asConjunction guardassignmentloc = error $ "Error in serializing a switch: " <> err
   | Right (Set.toList -> [((guard, assignment), endloc)]) <- asConjunction guardassignmentloc = object
      [ "init_loc" .= loc
      , "gate" .= show act
      , "guard" .= guard
      , "assignments" .= assignment
      , "end_loc" .= endloc
      ]
   | Right (Set.toList -> gals) <- asConjunction guardassignmentloc = JSON.toJSON $ map (Switch loc act . atom) gals

-- The guard may be a conjunction of guards in the map, and the guards in the map may also be conjunctions
-- So we're looking for a subset of the guards in the map, such that their union is exactly this guard
-- We fold over the map, taking any guards we're allowed to that make progress.
getGuard :: Expr Bool -> Map.Map (Expr Bool) String -> [String]
getGuard g guardmap
  | Just nm <- guardmap Map.!? g = [nm]
  | And gs <- view g = (\(req,_,nms) -> if Set.null req then nms else error ("couldn't find guard" ++ show g)) $ foldr combine (gs, mempty, []) $ Map.toList guardmap
    where
      combine (view -> x,nm) (required, allowed, nms)
        | x `elem` required = (Set.delete x required, Set.insert x allowed, nm:nms)
        | And xs <- x
        , all (`elem` Set.union required allowed) xs
        , any (`elem` required) xs = (Set.difference required xs, Set.union allowed xs, nm:nms)
        | otherwise = (required, allowed, nms) -- skipping this guard
getGuard _ _ = error "couldn't find guard"

-- for params
instance JSON.ToJSON (Some Type) where
  toJSON (Some tp) = JSON.Object $ addFields $ JSON.singleton "type" (case tp of
    IntType -> "int"
    BoolType -> "bool"
    FloatType -> "float"
    CharType -> "char"
    UnitType -> "()"
    ListType CharType -> "string"
    ListType _ -> "array"
    TupleType _ _ -> "structure"
    _ -> error "todo: serialize sets and sumtypes"
    )
    where
      addFields = case tp of
        -- not flattening any nested tuples: structures that originally had 3 or more fields are now nested structures,
        -- and the field names are just the tuple projections 'fst' and 'snd'. This matches with simply printing the expressions.
        TupleType a b -> JSON.insert "attributes" $ JSON.toJSON $ Map.fromList @String [("fst", Some a), ("snd", Some b)]
        ListType t -> JSON.insert "elements" $ JSON.toJSON (Some t) -- recursive call to element types of the 'array'
        _ -> id -- other types don't need any extra fields


-- | Write a single STS to a JSON file.
stsToJSONFile :: (Ord loc, Show loc)
              => FilePath
              -> String
              -> IOSTS FreeLattice loc String String
              -> Map.Map (Expr Bool) String
              -> Map.Map VarModel String
              -> Valuation
              -> IO ()
stsToJSONFile path sid sts gs as valuation = BSL.writeFile path (JSON.encode (stsToJSON sid sts gs as valuation))

-- | Write a list of STSs to a single file containing a JSON array.
stsListToJSONFile :: (Ord loc, Show loc)
                  => FilePath
                  -> [(String, IOSTS FreeLattice loc String String, Valuation)]
                  -> Map.Map (Expr Bool) String
                  -> Map.Map VarModel String
                  -> IO ()
stsListToJSONFile path stss gs as = BSL.writeFile path (JSON.encode [ stsToJSON sid sts gs as valuation | (sid, sts, valuation) <- stss ])
