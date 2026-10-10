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
import Lattest.Model.Alphabet (SymInteract (..), IOAct, isOutputInteract, isInputInteract)
import Lattest.Model.Automaton (Valuation, AutSyntax (..), STStdest (..))
import Lattest.Model.BoundedMonad
import Lattest.Model.StandardAutomata (IOSTS, allLocations)
import Lattest.Model.Symbolic.Expr (Variable (..), Val, Type (..), ExprType (..), VarModel, ExprView(..), enumIndex, prettyValue)
import Lattest.Model.Symbolic.Internal.ExprDefs (Expr(..))
import Lattest.Model.Symbolic.Internal.ExprImpls (Valuation(..), Val (..), VarModel (..), sAnd)
import Lattest.SMT (RCSet)
import qualified Data.Aeson as JSON
import qualified Data.Aeson.KeyMap as JSON
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Dependent.Map as DMap
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Lattest.Model.Symbolic.Internal.FreeMonoidX as FMX
import Data.SBV (AlgReal)

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
  toJSON (Val a) = valueToJSON (typeOf a) a

-- | Enums are written as their position in the original range, also when nested in arrays or structures.
valueToJSON :: Type a -> a -> JSON.Value
valueToJSON t x | Just i <- enumIndex t x = JSON.toJSON i
valueToJSON RationalType x = JSON.toJSON $ fromRational @Double x
valueToJSON (ListType CharType) s = JSON.toJSON s
valueToJSON (ListType t) xs = JSON.toJSON $ map (valueToJSON t) xs
valueToJSON (TupleType a b) (x, y) = JSON.toJSON (valueToJSON a x, valueToJSON b y)
valueToJSON t x = has @JSON.ToJSON t $ JSON.toJSON x

instance Has JSON.ToJSON Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    RationalType -> k
    RealType -> k
    BoolType -> k
    CharType -> k
    UnitType -> k
    ListType tp -> has @JSON.ToJSON tp k
    SetType tp -> has @JSON.ToJSON tp k
    SumType a b -> has @JSON.ToJSON a $ has @JSON.ToJSON b k
    TupleType a b -> has @JSON.ToJSON a $ has @JSON.ToJSON b k

instance JSON.ToJSON AlgReal where
  toJSON = JSON.toJSON @Double . fromRational . toRational

deriving instance (JSON.ToJSON a) => JSON.ToJSON (RCSet a)

isEmptySwitch :: Switch -> Bool
isEmptySwitch (Switch _ act gal) =
    (isForbidden gal && isOutputInteract act) || (isUnderspecified gal && isInputInteract act)

-- | Given ID, STS, the names of guards and assignments, the enums, the names of the fields of the structures (as given by
-- the parser), and the initial valuation, make a JSON.
-- A part of a guard that is not in the given guard map is named after its text ('prettyGuard'), so the file can not be
-- loaded again.
stsToJSON :: (Ord loc, Show loc) => String -> IOSTS FreeLattice loc String String -> Map.Map (Expr Bool) String -> Map.Map VarModel String -> Map.Map String (Some Expr) -> Map.Map (Some Type, [Bool]) String -> Valuation -> JSON.Value
stsToJSON sid sts guardmap assmap enums fields valuation =
    object $
        [ "id" .= sid
        , "initial_location" .= initLocationJSON locIds (initConf sts)
        , "initialValuation" .= initValue valuation
        , "locations" .= Map.elems locIds
        , "switches" .= switches''
        , "enum_translation" .= Map.toList (Map.map (\(Some e) -> show e) enums)
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
    switches' = map (\(l,(act, ml)) -> Switch (locIds Map.! l) act (bimap (\(STSLoc (g,a)) -> (guardNames g, getassignment a)) (locIds Map.!) <#> ml)) switches
    switches'' = filter (not . isEmptySwitch) switches'

    -- the conjuncts of a guard that are not in the guard map are named after their text
    guardNames g
      | Just nm <- guardmap Map.!? g = [nm]
      | otherwise = let (nms, rest) = getGuard (sAnd (Set.fromList (conjuncts g))) guardmap in nms ++ map (prettyGuard enums fields) rest
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

-- | The conjuncts of a guard. An MC/DC row on a list is written as @if c then g else False@, which is the conjunction
-- of @c@ and @g@.
conjuncts :: Expr Bool -> [Expr Bool]
conjuncts g = case view g of
  And gs                -> concatMap (conjuncts . Expr) (Set.toList gs)
  Ite c t (Const False) -> conjuncts (Expr c) ++ conjuncts (Expr t)
  _                     -> [g]

-- The guard may be a conjunction of guards in the map, and the guards in the map may also be conjunctions
-- So we're looking for a subset of the guards in the map, such that their union is exactly this guard
-- We fold over the map, taking any guards we're allowed to that make progress.
-- The result is the names of these guards, and the conjuncts of the guard that are not in the map.
getGuard :: Expr Bool -> Map.Map (Expr Bool) String -> ([String], [Expr Bool])
getGuard g guardmap
  | Just nm <- guardmap Map.!? g = ([nm], [])
  | And gs <- view g = (\(req,_,nms) -> (nms, map Expr (Set.toList req))) $ foldr combine (gs, mempty, []) $ Map.toList guardmap
  | otherwise = ([], [g])
    where
      combine (view -> x,nm) (required, allowed, nms)
        | x `elem` required = (Set.delete x required, Set.insert x allowed, nm:nms)
        | And xs <- x
        , all (`elem` Set.union required allowed) xs
        , any (`elem` required) xs = (Set.difference required xs, Set.union allowed xs, nm:nms)
        | otherwise = (required, allowed, nms) -- skipping this guard

-- | The text of a guard, in a readable form.
prettyGuard :: Map.Map String (Some Expr) -> Map.Map (Some Type, [Bool]) String -> Expr Bool -> String
prettyGuard enums fields = pretty 0 . view
  where
    enumNames = Map.fromListWith (\a b -> b <> "/" <> a) [ (e, nm) | (nm, e) <- Map.toList enums ]

    -- The number is the precedence of the surrounding expression: 0 if-then-else, 1 conjunction, 2 negation,
    -- 3 comparison, 4 sum, 5 product, 9 anything that binds tighter. A weaker expression gets parentheses.
    pretty :: Int -> ExprView t -> String
    pretty p e = case e of
      Var v -> varName v
      Const c
        | Just nm <- enumNames Map.!? Some (Expr e) -> nm
        | otherwise -> constText (typeOf c) c
      Ite c a b -> paren p 0 $ "if " <> pretty 1 c <> " then " <> pretty 1 a <> " else " <> pretty 0 b
      And es
        | Set.null es -> "true"
        | otherwise -> paren p 1 $ List.intercalate " && " $ map (pretty 2) $ Set.toList es
      -- a comparison with a boolean constant is the boolean itself, or its negation
      Equal BoolType a (Const b) -> if b then pretty p a else pretty p (Not a)
      Equal BoolType (Const b) a -> if b then pretty p a else pretty p (Not a)
      Equal _ a b -> paren p 3 $ pretty 4 a <> " == " <> pretty 4 b
      Not (Equal BoolType a (Const b)) -> if b then paren p 2 ("not " <> pretty 3 a) else pretty p a
      Not (Equal BoolType (Const b) a) -> if b then paren p 2 ("not " <> pretty 3 a) else pretty p a
      Not (Equal _ a b) -> paren p 3 $ pretty 4 a <> " != " <> pretty 4 b
      Not (Gez a) -> paren p 3 $ comparison True a
      Not a -> paren p 2 $ "not " <> pretty 3 a
      Gez a -> paren p 3 $ comparison False a
      Sum _ es -> paren p 4 $ case (positive, negative) of
          ([], []) -> "0"
          ([], n : ns) -> "-" <> n <> concatMap (" - " <>) ns
          (ps, ns) -> List.intercalate " + " ps <> concatMap (" - " <>) ns
        where
          ts = sumTerms (FMX.toOccurListT es)
          positive = [ s | (False, _, s) <- ts ]
          negative = [ s | (True, _, s) <- ts ]
      Product _ es -> paren p 5 $ case FMX.toOccurListT es of
        [] -> "1"
        ts -> List.intercalate " * " [ pretty 6 a <> (if n == 1 then "" else "^" <> show n) | (a, n) <- ts ]
      Divide a b -> paren p 5 $ pretty 5 a <> " / " <> pretty 6 b
      DivideFloat a b -> paren p 5 $ pretty 5 a <> " / " <> pretty 6 b
      Modulo a b -> paren p 5 $ pretty 5 a <> " % " <> pretty 6 b
      Length _ xs -> "len(" <> pretty 0 xs <> ")"
      LElem _ x xs -> paren p 3 $ pretty 4 x <> " in " <> pretty 4 xs
      Head xs -> let (n, base) = position xs in pretty 9 base <> "[" <> show n <> "]"
      Tail _ -> let (n, base) = position e in pretty 9 base <> "[" <> show n <> ":]"
      First{} -> let (s, _, path) = projection e in s <> concatMap (\b -> if b then ".snd" else ".fst") path
      Second{} -> let (s, _, path) = projection e in s <> concatMap (\b -> if b then ".snd" else ".fst") path
      Pair x y -> "(" <> pretty 0 x <> ", " <> pretty 0 y <> ")"
      -- the other expressions are simply shown
      _ -> let s = show e in if p > 0 && ' ' `elem` s then "(" <> s <> ")" else s

    paren :: Int -> Int -> String -> String
    paren p q s = if p > q then "(" <> s <> ")" else s

    -- The projections of a structure: the text up to the last field of which the name is known, the type of that field,
    -- and the projections after it. A field without a name is written as its projections @.fst@ and @.snd@.
    projection :: ExprView t -> (String, Some Type, [Bool])
    projection e = case e of
        First _ x -> field False (projection x)
        Second _ x -> field True (projection x)
        _ -> (pretty 9 e, tp, [])
      where
        tp = has @ExprType e (Some (typeOf' e))
        field b (s, t, path)
          | Just nm <- fields Map.!? (t, path ++ [b]) = (s <> "." <> nm, tp, [])
          | otherwise = (s, t, path ++ [b])

    constText :: Type a -> a -> String
    constText RationalType x = show (fromRational x :: Double)
    constText t x = prettyValue t x

    -- @a >= 0@, or @a < 0@ if strict. The negative terms of a sum are moved to the right, and a variable is preferred on
    -- the left: @(-1+x) ≥ 0@ is @x >= 1@, and @(3+-x) ≥ 0@ is @x <= 3@.
    comparison :: Bool -> ExprView a -> String
    comparison strict (Sum _ es)
      | all fst l && not (all fst r) = text r <> (if strict then " > " else " <= ") <> text l
      | otherwise = text l <> (if strict then " < " else " >= ") <> text r
      where
        ts = sumTerms (FMX.toOccurListT es)
        l = [ (isConst, s) | (False, isConst, s) <- ts ]
        r = [ (isConst, s) | (True, isConst, s) <- ts ]
        text :: [(Bool, String)] -> String
        text [] = "0"
        text xs = List.intercalate " + " (map snd xs)
    comparison strict a = pretty 4 a <> (if strict then " < 0" else " >= 0")

    -- For every term of a sum: whether it is negative, whether it is a constant, and the text of its absolute value.
    sumTerms :: Num a => [(ExprView a, Integer)] -> [(Bool, Bool, String)]
    sumTerms = map term
      where
        term (Const x, n) = let v = fromInteger n * x in (v < 0, True, pretty 5 (Const (abs v)))
        term (a, n) = (n < 0, False, (if abs n == 1 then "" else show (abs n) <> "*") <> pretty 5 a)

    -- A list that is the tail of the tail of ... a list, as the number of tails and that list.
    position :: ExprView [x] -> (Int, ExprView [x])
    position (Tail xs) = first (+ 1) (position xs)
    position xs = (0, xs)

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
              -> Map.Map String (Some Expr)
              -> Map.Map (Some Type, [Bool]) String
              -> Valuation
              -> IO ()
stsToJSONFile path sid sts gs as enums fields valuation = BSL.writeFile path (JSON.encode (stsToJSON sid sts gs as enums fields valuation))

-- | Write a list of STSs to a single file containing a JSON array.
stsListToJSONFile :: (Ord loc, Show loc)
                  => FilePath
                  -> [(String, IOSTS FreeLattice loc String String, Valuation)]
                  -> Map.Map (Expr Bool) String
                  -> Map.Map VarModel String
                  -> Map.Map String (Some Expr)
                  -> Map.Map (Some Type, [Bool]) String
                  -> IO ()
stsListToJSONFile path stss gs as enums fields = BSL.writeFile path (JSON.encode [ stsToJSON sid sts gs as enums fields valuation | (sid, sts, valuation) <- stss ])
