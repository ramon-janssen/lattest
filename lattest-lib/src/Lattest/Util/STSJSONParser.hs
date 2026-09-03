{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeApplications #-}

module Lattest.Util.STSJSONParser (
    stsFromJSONFile,
    stsListFromJSONFile,
) where

import Control.Monad (forM)
import Data.Foldable (toList)
import qualified Data.Aeson as JSON
import Data.Dependent.Sum (DSum (..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Map.Strict as Map
import Data.Scientific (toRealFloat)
import qualified Data.Set as Set
import Data.Text (unpack)
import Data.Maybe (fromMaybe)
import Lattest.Model.Alphabet (IOAct (..), SymInteract (..))
import Lattest.Model.Automaton (stsTLoc, STStdest)
import Lattest.Model.BoundedMonad (FreeLattice, atom, (/\))
import Lattest.Model.StandardAutomata (IOSTS, automaton)
import Lattest.Model.Symbolic.Expr
import Data.Some (Some (..))
import Data.Type.Equality ((:~:)(..))
import Data.GADT.Compare (GEq(..))
import Lattest.Model.Symbolic.Internal.ExprDefs (Constant (..), ExprConstraints)
import Data.SBV (RCSet (..))
import qualified Data.Aeson.Types as JSON
import qualified Data.Aeson.KeyMap as JSON
import Data.Bifunctor (Bifunctor(..))
import Data.Aeson.Key (toString)


data UntypedExpr
    = UEBool Bool
    | UEFloat Double
    | UEInt  Integer
    | UEStr  String
    | UEVar  String  -- Variable reference, e.g. { "var": "name" }
    | UEOp1  String UntypedExpr
    | UEOp2  String UntypedExpr UntypedExpr
    -- Op3 and Op5 always start with one or two variable names { "lambda": "name" }, respectively
    | UEOp3  String String UntypedExpr UntypedExpr
    | UEOp5  String String String UntypedExpr UntypedExpr UntypedExpr
    deriving (Show, Eq)

instance JSON.FromJSON UntypedExpr where
  parseJSON (JSON.Bool b)   = pure (UEBool b)
  parseJSON (JSON.Number _) = error "untagged constant integer or float"
  parseJSON (JSON.String s) = pure (UEStr (unpack s))
  parseJSON (JSON.Object o) = do
    mvar <- o JSON..:? "var"
    case mvar of
      Just name -> pure (UEVar name)
      Nothing -> do
        mint <- o JSON..:? "integer"
        case mint of
          Just i -> pure (UEInt i)
          Nothing -> do
            mfloat <- o JSON..:? "float"
            case mfloat of
              Just f -> pure (UEFloat f)
              Nothing -> do
                mbool <- o JSON..:? "boolean"
                case mbool of
                  Just b -> pure (UEBool b)
                  Nothing -> do
                    mstr <- o JSON..:? "string"
                    case mstr of
                      Just s -> pure (UEStr s)
                      Nothing -> do
                        (op :: String) <- o JSON..: "op"
                        case op of
                          "neg" -> UEOp1 op <$> o JSON..: "rhs"
                          "not" -> UEOp1 op <$> o JSON..: "rhs"
                          "len" -> UEOp1 op <$> o JSON..: "rhs"
                          "map"    -> UEOp3 op <$> o JSON..: "lambda" <*> o JSON..: "fun" <*> o JSON..: "lst"
                          "filter" -> UEOp3 op <$> o JSON..: "lambda" <*> o JSON..: "fun" <*> o JSON..: "lst"
                          "forall" -> UEOp3 op <$> o JSON..: "lambda" <*> o JSON..: "expression" <*> o JSON..: "over"
                          "exists" -> UEOp3 op <$> o JSON..: "lambda" <*> o JSON..: "expression" <*> o JSON..: "over"
                          "cardinality" -> UEOp5 op <$> o JSON..: "lambda"  <*> o JSON..: "quantifier" <*> o JSON..: "expression"  <*> o JSON..: "over" <*> (UEInt <$> o JSON..: "n")
                          "foldr"       -> UEOp5 op <$> o JSON..: "lama" <*> o JSON..: "lamb"       <*> o JSON..: "func" <*> o JSON..: "init" <*> o JSON..: "list"
                          "foldl"       -> UEOp5 op <$> o JSON..: "lamb" <*> o JSON..: "lama"       <*> o JSON..: "func" <*> o JSON..: "init" <*> o JSON..: "list"
                          "either"      -> UEOp5 op <$> o JSON..: "lama" <*> o JSON..: "lamb"       <*> o JSON..: "funa" <*> o JSON..: "funb" <*> o JSON..: "eith"
                          _ -> UEOp2 op <$> o JSON..: "lhs" <*> o JSON..: "rhs"
  parseJSON _ = fail "expected expression"

type VarMap = Map.Map String (Some Variable)
type AccessorMap = Map.Map String (Some Expr -> Some Expr)

lookupVar :: VarMap -> String -> Either String (DSum Type Expr)
lookupVar varmap name = case Map.lookup name varmap of
    Just (Some v@(Variable _ t)) -> Right $ t :=> sVar v
    Nothing             -> Left $ "unknown variable: " ++ name

data TwoExprs a = Two (Expr a) (Expr a)
toExpr :: VarMap -> AccessorMap -> UntypedExpr -> Either String (DSum Type Expr)
toExpr varmap accmap = \case
  UEVar name -> lookupVar varmap name
  UEBool  b -> Right $ BoolType  :=> sConst b
  UEInt   i -> Right $ IntType   :=> sConst i
  UEFloat f -> Right $ FloatType :=> sConst f
  UEStr   s -> Right $ ListType CharType :=> sConst s
  UEOp1 o e -> go e >>= op1 o
  UEOp2 "project" e (UEVar f) -> -- need to handle this here, because for all other Op2's we check the types (and field accessors do not have a type here)
    case accmap Map.!? f of
      Just g -> do
        _ :=> e' <- go e
        case g (Some e') of
          Some e'' -> withExprConstraints e'' $ Right $ typeOf' e'' :=> e''
      Nothing -> Left $ "unknown field projection: " <> f
  UEOp2 o e1 e2 -> do
    t1 :=> x <- go e1
    t2 :=> y <- go e2
    case geq t1 t2 of
      Just Refl -> op2ET o (t1 :=> Two x y)
      Nothing -> op2 o (t1 :=> x) (t2 :=> y)
  UEOp3 o v e1 e2 -> op3 o v e1 e2
  UEOp5 o v1 v2 e1 e2 e3 -> op5 o v1 v2 e1 e2 e3
  where
    -- ExprViews that don't (yet) have a parse:
    --   Ite

    go = toExpr varmap accmap

    op1 :: String -> DSum Type Expr -> Either String (DSum Type Expr)
    -- TODO: define non-polymorphic sum types in the json, translate them to our adts before parsing the exprs.
    -- We need to know the type of the other half of an Either to construct it;
    -- which is why e.g. "left" isn't part of the JSON syntax.
    -- instead, if we want e.g. availability = Av | PartAv,
    -- we'll need the json to contain that declaration,
    -- from which we'd generate Av = Left :: Either () (),
    -- and then parse "Av" into TupleType () () :=> sLeft ().
    -- op1 "left"  (tp :=> x) = Right $ TupleType tp undefined :=> sLeft  x
    -- op1 "right" (tp :=> x) = Right $ TupleType undefined tp :=> sRight x
    op1 o (tp :=> x) = case tp of
      BoolType -> case o of
        "not" -> Right $ BoolType :=> sNot x
        _ -> Left $ "unknown op1 @Bool: " <> o
      ListType t -> withExprConstraints t case o of
        "concat" -> case t of
          ListType t' -> withExprConstraints t' $ Right $ t :=> sConcat x
          _ -> Left "concat on non-nested list"
        "len" -> Right $ IntType :=> sLength x
        "head" -> Right $ t :=> sHead x
        "tail" -> Right $ ListType t :=> sTail x
        _ -> Left $ "unknown op1 @List: " <> o
      TupleType t1 t2 -> withExprConstraints t1 $ withExprConstraints t2 case o of
        "first" -> Right $ t1 :=> sFirst x
        "second" -> Right $ t2 :=> sSecond x
        _ -> Left $ "unknown op1 @Tuple: " <> o
      _ -> error "todo"

    -- for two equally-typed expressions
    op2ET :: String -> DSum Type TwoExprs -> Either String (DSum Type Expr)
    op2ET "==" (t :=> Two x y) = withExprConstraints t $ Right $ BoolType :=> x .== y
    op2ET "!=" (t :=> Two x y) = withExprConstraints t $ Right $ BoolType :=> sNot (x .== y)
    op2ET o (t :=> Two x y) = case t of
      BoolType -> case o of
        "&&" -> Right $ BoolType :=> x .&& y
        "||" -> Right $ BoolType :=> x .|| y
        _ -> op2 o (t :=> x) (t :=> y)
      IntType -> case o of
        "%" -> Right $ t :=> x .% y
        "/" -> Right $ t :=> x ./ y
        "+" -> Right $ t :=> x .+ y
        "*" -> Right $ t :=> x .* y
        "<" -> Right $ BoolType :=> x .< y
        "<=" -> Right $ BoolType :=> x .<= y
        ">" -> Right $ BoolType :=> x .> y
        ">=" -> Right $ BoolType :=> x .>= y
        _ -> op2 o (t :=> x) (t :=> y)
      FloatType -> case o of
        "/" -> Right $ t :=> x ./ y
        "+" -> Right $ t :=> x .+ y
        "*" -> Right $ t :=> x .* y
        "<" -> Right $ BoolType :=> x .< y
        "<=" -> Right $ BoolType :=> x .<= y
        ">" -> Right $ BoolType :=> x .> y
        ">=" -> Right $ BoolType :=> x .>= y
        _ -> op2 o (t :=> x) (t :=> y)
      ListType _ -> case o of
        "++" -> Right $ t :=> sAppend x y
        _ -> op2 o (t :=> x) (t :=> y)

      _ -> error "todo"
    -- for two potentially unequally-typed expressions
    op2 :: String -> DSum Type Expr -> DSum Type Expr -> Either String (DSum Type Expr)
    op2 "cons" (t1 :=> x) (ListType t2 :=> xs) = case geq t1 t2 of
      Just Refl -> Right $ ListType t1 :=> sCons x xs
      Nothing -> Left "mismatched type for cons"
    op2 "elem" (t1 :=> x) (ListType t2 :=> xs) = case geq t1 t2 of
      Just Refl -> Right $ BoolType :=> sElem x xs
      Nothing -> Left "mismatched type for list elem"
    op2 "take" (IntType :=> i) (ListType t :=> xs) = Right $ ListType t :=> sTake i xs
    op2 "drop" (IntType :=> i) (ListType t :=> xs) = Right $ ListType t :=> sDrop i xs
    op2 "pair" (t1 :=> x) (t2 :=> y) = Right $ TupleType t1 t2 :=> sPair x y
    op2 "selem" (t1 :=> x) (SetType t2 :=> y) = case geq t1 t2 of
      Just Refl -> Right $ BoolType :=> sSElem x y
      Nothing -> Left "mismatched type for set elem"
    op2 "insert" (t1 :=> x) (SetType t2 :=> y) = withExprConstraints t1 case geq t1 t2 of
      Just Refl -> Right $ SetType t1 :=> sInsert x y
      Nothing -> Left "mismatched type for set insert"
    op2 o _ _ = Left $ "unknown or badly typed op2: " <> o

    op3 :: String -> String -> UntypedExpr -> UntypedExpr -> Either String (DSum Type Expr)
    op3 op v f xs = do
      t'' :=> ys <- go xs
      case t'' of
        ListType t -> do
          t' :=> g <- toExpr (Map.insert v (Some (Variable v t)) varmap) accmap f
          withExprConstraints t $ withExprConstraints t' case op of
            "map" -> Right $ ListType t' :=> sMap (Variable v t) g ys
            "filter" -> case geq BoolType t' of
              Just Refl -> Right $ ListType t :=> sFilter (Variable v t) g ys
              Nothing -> Left "non-bool function in filter"
            "forall" -> case geq BoolType t' of
              Just Refl -> Right $ BoolType :=> let y = Variable "forallAccumulator" BoolType
                                                    x = Variable "forallIterator" BoolType
                                                in sFoldr x y (sVar x .&& sVar y) sTrue $ sMap (Variable v t) g ys
              Nothing -> Left "non-bool function in forall"
            "exists" -> case geq BoolType t' of
              Just Refl -> Right $ BoolType :=> let y = Variable "existsAccumulator" BoolType
                                                    x = Variable "existsIterator" BoolType
                                                in sFoldr x y (sVar x .|| sVar y) sFalse $ sMap (Variable v t) g ys
              Nothing -> Left "non-bool function in forall"
            _ -> Left $ "unknown or mistyped op3: " <> op
        _ -> Left "op3 received non-list as third expression"

    op5 :: String -> String -> String -> UntypedExpr -> UntypedExpr -> UntypedExpr -> Either String (DSum Type Expr)
    op5 "either" v1 v2 e1 e2 e3 = do
      st :=> e <- go e3
      case st of
        SumType t1 t2 -> do
          t  :=> l <- toExpr (Map.insert v1 (Some (Variable v1 t1)) varmap) accmap e1
          t' :=> r <- toExpr (Map.insert v2 (Some (Variable v2 t2)) varmap) accmap e2
          withExprConstraints t1 $ withExprConstraints t2 $ withExprConstraints t case geq t t' of
            Just Refl -> Right $ t :=> sEither (Variable v1 t1) (Variable v2 t2) l r e
            Nothing -> Left "wrongly typed either"
        _ -> Left "non-Either in either"
    op5 "foldr" v1 v2 f i xs = do
      lt :=> ys <- go xs
      case lt of
        ListType ta -> do
          tb :=> i' <- go i
          tb' :=> g <- toExpr (Map.insert v1 (Some (Variable v1 ta)) $ Map.insert v2 (Some (Variable v2 tb)) varmap) accmap f
          withExprConstraints ta case geq tb tb' of
            Just Refl -> Right $ tb :=> sFoldr (Variable v1 ta) (Variable v2 tb) g i' ys
            Nothing -> Left "wrongly typed foldr"
        _ -> Left "non-list in foldr"
    op5 "foldl" v1 v2 f i xs = do
      lt :=> ys <- go xs
      case lt of
        ListType ta -> do
          tb :=> i' <- go i
          tb' :=> g <- toExpr (Map.insert v1 (Some (Variable v1 tb)) $ Map.insert v2 (Some (Variable v2 ta)) varmap) accmap f
          withExprConstraints ta case geq tb tb' of
            Just Refl -> Right $ tb :=> sFoldl (Variable v1 tb) (Variable v2 ta) g i' ys
            Nothing -> Left "wrongly typed foldr"
        _ -> Left "non-list in foldl"
    -- "cardinality" is the only case that doesn't actually take 2 variables and 3 expressions;
    -- we just pass the 'quantity' string in place of the second variable and the size as the final UE
    op5 "cardinality" v quantity f xs (UEInt n) =
      op3 "filter" v f xs >>= \case
        ListType _ :=> ys -> case quantity of
          "exactly"  -> Right $ BoolType :=> sLength ys .== sConst n
          "at_least" -> Right $ BoolType :=> sLength ys .>= sConst n
          "at_most"  -> Right $ BoolType :=> sLength ys .<= sConst n
          _ -> Left "unknown quantifier in cardinality"
        _ -> error "op3 'filter' did something very weird"
    op5 _ _ _ _ _ _ = Left "unkown or wrongly typed op5"

-- Location IDs can be integers or strings in JSON; both are mapped to String for consistency.
newtype LocationId = LocationId { locId :: String }

instance JSON.FromJSON LocationId where
    parseJSON v = case v of
        JSON.String s -> pure $ LocationId (unpack s)
        JSON.Number n -> pure $ LocationId (show (round n :: Integer))
        _             -> fail $ "expected string or number for LocationId, got: " ++ show v

newtype GateId = GateId { unGateId :: String }

-- Gate IDs can be integers or strings in JSON; both are mapped to String for consistency.
instance JSON.FromJSON GateId where
    parseJSON v = case v of
        JSON.String s -> pure $ GateId (unpack s)
        JSON.Number n -> pure $ GateId (show (round n :: Integer))
        _             -> fail $ "expected string or number for GateId, got: " ++ show v

-- type, and a list of field accessors
newtype VarDefJson = VarDefJson { varDefJsonType :: (Some Type, [(String, Some Expr -> Some Expr)]) }

instance JSON.FromJSON VarDefJson where
  parseJSON = JSON.withObject "VarDefJson" $ fmap VarDefJson . go
    where
      go :: JSON.Object -> JSON.Parser (Some Type, [(String, Some Expr -> Some Expr)])
      go o = do
        tp :: String <- o JSON..: "type"
        case tp of
          "int"     -> k $ Some IntType
          "integer" -> k $ Some IntType
          "bool"    -> k $ Some BoolType
          "boolean" -> k $ Some BoolType
          "string"  -> k $ Some $ ListType CharType
          "char"    -> k $ Some CharType
          "float"   -> k $ Some FloatType
          "array"   -> do
            o' <- o JSON..: "elements"
            (Some t, a) <- go o'
            pure (Some $ ListType t, a)
          "structure" -> do
            JSON.Object o' <- o JSON..: "attributes"
            ((t, a), b) <- mkStructure $ JSON.toList o'
            pure (t, a++b)
          _ -> error "unknown type"
      k = pure . (,[])
      mkStructure :: [(JSON.Key, JSON.Value)] -> JSON.Parser ((Some Type, [(String, Some Expr -> Some Expr)]), [(String, Some Expr -> Some Expr)])
      mkStructure [] = error "empty structure"
      mkStructure [(nm, JSON.Object o)] = do
        (tp,ac) <- go o
        pure ((tp, [(toString nm, id)]), ac)
      mkStructure ((nm, JSON.Object o) : fields) = do
        (Some  (ta :: Type a), a) <- go o
        ((Some (tb :: Type b), accessors), b) <- mkStructure fields
        withExprConstraints ta $ withExprConstraints tb $
          pure ((Some (TupleType ta tb), (toString nm, \(Some e) -> Some $ sFirst @b @a $ safeCoerce "left" e) : map (second (\f (Some e) -> f $ Some $ sSecond @a @b $ safeCoerce "right" e)) accessors), a++b)
      mkStructure _ = error "non-object in attributes"
      -- runtime check whether field accessors are used on expressions of the right type
      safeCoerce :: forall a b. String -> ExprConstraints b => Expr a -> Expr b
      safeCoerce str e = let tb = typeOf' undefined :: Type b in withExprConstraints e case geq (typeOf' e) tb of
        Just Refl -> e
        Nothing -> error $ "failed coerce " <> str <> " " <> show e <> " " <> show (typeOf' e) <> " " <> show tb

data GateDefJson = GateDefJson
    { gateDefJsonShortname :: Maybe String
    , gateDefJsonParams :: [String]
    }

instance JSON.FromJSON GateDefJson where
    parseJSON = JSON.withObject "GateDefJson" $ \o ->
        GateDefJson <$> o JSON..:? "shortname"
                    <*> o JSON..:  "parameters"

data AssignmentDefJson = AssignmentDefJson
    { assignmentJsonVar  :: String
    , assignmentJsonExpr :: UntypedExpr
    }

instance JSON.FromJSON AssignmentDefJson where
    parseJSON = JSON.withObject "AssignmentDefJson" $ \o ->
        AssignmentDefJson <$> o JSON..: "target" <*> o JSON..: "expression"

data SwitchDefJson = SwitchDefJson
    { switchJsonInitLoc     :: LocationId
    , switchJsonGate        :: GateId
    , switchJsonGuard       :: Maybe [String]  -- names of guards to be conjoined
    , switchJsonAssignments :: [String]
    , switchJsonEndLoc      :: LocationId
    }

-- A "guard" field may be a single guard name, or an array of guard names (merged with &&).
instance JSON.FromJSON SwitchDefJson where
    parseJSON = JSON.withObject "SwitchDefJson" $ \o ->
        SwitchDefJson
            <$> o JSON..:  "init_loc"
            <*> o JSON..:  "gate"
            <*> (o JSON..:? "guard" >>= traverse parseGuardNames)
            <*> (o JSON..:? "assignments" JSON..!= [])
            <*> o JSON..:  "end_loc"
      where
        parseGuardNames (JSON.String s) = pure [unpack s]
        parseGuardNames (JSON.Array a)  = mapM parseGuardName (toList a)
        parseGuardNames _               = fail "guard must be a string or an array of strings"
        parseGuardName (JSON.String s) = pure (unpack s)
        parseGuardName _               = fail "guard array elements must be strings"

data STSJsonFormat = STSJsonFormat
    { stsJsonId            :: String
    , stsJsonInitLoc       :: LocationId
    , stsJsonLocVars       :: Map.Map String VarDefJson
    , stsJsonParams        :: Map.Map String VarDefJson
    , stsJsonInitValuation :: Map.Map String JSON.Value
    , stsJsonLocations     :: [LocationId]
    , stsJsonInputGates    :: Map.Map String GateDefJson
    , stsJsonOutputGates   :: Map.Map String GateDefJson
    , stsJsonGuards        :: Map.Map String UntypedExpr
    , stsJsonAssignments   :: Map.Map String AssignmentDefJson
    , stsJsonSwitches      :: Map.Map String SwitchDefJson
    }

instance JSON.FromJSON STSJsonFormat where
    parseJSON = JSON.withObject "STSJsonFormat" $ \o ->
        STSJsonFormat
            <$> (o JSON..:? "id" JSON..!= "")
            <*> o JSON..:  "initial_location"
            <*> o JSON..:  "locationVariables"
            <*> o JSON..:  "parameters"
            <*> (o JSON..:? "initialValuation" JSON..!= Map.empty)
            <*> o JSON..:  "locations"
            <*> o JSON..:  "inputGates"
            <*> o JSON..:  "outputGates"
            <*> o JSON..:  "guards"
            <*> (o JSON..:? "assignments" JSON..!= Map.empty)
            <*> o JSON..:  "switches"

-- STS elements builders

buildVarMap :: Map.Map String VarDefJson -> Either String (Map.Map String (Some Variable), Map.Map String (Some Expr -> Some Expr))
buildVarMap defs = do
  (varmap, accessorss) <- unzip <$> forM (Map.toList defs) (\(name, def) ->
    case varDefJsonType def of
      (Some t', accessors) -> return ((name, Some $ Variable name t'), accessors))
  let accessors = Map.fromList $ concat accessorss
  let varmap' = Map.fromList varmap
  -- for some reason this type is getting evaluated somewhere
  pure (varmap' <> Map.mapWithKey (\nm -> const $ Some $ Variable nm CharType{- error $ "getting the type of a field accessor as if it were a variable: " <> nm -}) accessors, accessors)

buildGateMap
    :: (String -> IOAct String String)
    -> Map.Map String (Some Variable)
    -> Map.Map String GateDefJson
    -> Either String (Map.Map String (SymInteract (IOAct String String)))
buildGateMap mkGate varMap defs = Map.fromList <$> forM (Map.toList defs) (\(name, def) -> do
    let gateName = fromMaybe name (gateDefJsonShortname def)
    params <- forM (gateDefJsonParams def) $ \pname ->
        case Map.lookup pname varMap of
            Just v  -> Right v
            Nothing -> Left $ "unknown parameter '" ++ pname ++ "' in gate '" ++ name ++ "'"
    return (name, SymInteract (mkGate gateName) params))

buildAssignment
    :: VarMap
    -> AccessorMap
    -> String
    -> AssignmentDefJson
    -> Either String (VarModel -> VarModel)
buildAssignment varMap accmap name def = do
    var <- case Map.lookup (assignmentJsonVar def) varMap of
        Just v  -> Right v
        Nothing -> Left $ "unknown variable '" ++ assignmentJsonVar def ++ "' in assignment '" ++ name ++ "'"
    let expr = assignmentJsonExpr def
    case var of
      Some v -> toExpr varMap accmap expr >>= \(tp :=> e) ->
        case geq (varType v) tp of
          Just Refl -> Right $ v =: e
          Nothing -> Left "assigment to variable of wrong type"

buildAssignmentMap
    :: VarMap
    -> AccessorMap
    -> Map.Map String AssignmentDefJson
    -> Either String (Map.Map String (VarModel -> VarModel))
buildAssignmentMap varMap accMap defs =
    Map.fromList <$> forM (Map.toList defs) (\(name, def) ->
        (name,) <$> buildAssignment varMap accMap name def)

buildVarModel
    :: Map.Map String (VarModel -> VarModel)
    -> [String]
    -> String
    -> Either String VarModel
buildVarModel assignMap names switchName = do
    updates <- forM names $ \aname ->
        case Map.lookup aname assignMap of
            Just f  -> Right f
            Nothing -> Left $ "unknown assignment '" ++ aname ++ "' in switch '" ++ switchName ++ "'"
    return (assignment updates)

buildSwitchList
    :: Map.Map String (SymInteract (IOAct String String))
    -> Map.Map String (Expr Bool)
    -> Map.Map String (VarModel -> VarModel)
    -> Map.Map String SwitchDefJson
    -> Either String [(String, SymInteract (IOAct String String), Expr Bool, VarModel, String)]
buildSwitchList gateMap guardMap assignMap switchDefs =
    forM (Map.toList switchDefs) $ \(name, def) -> do
        gate <- case Map.lookup (unGateId (switchJsonGate def)) gateMap of
            Just a  -> Right a
            Nothing -> Left $ "unknown gate '" ++ unGateId (switchJsonGate def) ++ "' in switch '" ++ name ++ "'"
        guard' <- case switchJsonGuard def of
            Nothing     -> Right sTrue
            Just gnames -> foldr (.&&) sTrue <$> forM gnames (\gname -> case Map.lookup gname guardMap of
                Just g  -> Right g
                Nothing -> Left $ "unknown guard '" ++ gname ++ "' in switch '" ++ name ++ "'")
        varModel <- buildVarModel assignMap (switchJsonAssignments def) name
        let initLoc = locId (switchJsonInitLoc def)
            endLoc  = locId (switchJsonEndLoc  def)
        return (initLoc, gate, guard', varModel, endLoc)

-- NOTE: transitions from the same location with matching gates are combined with /\
buildTransitionRel
    :: [(String, SymInteract (IOAct String String), Expr Bool, VarModel, String)]
    -> String
    -> Map.Map (SymInteract (IOAct String String)) (FreeLattice (STStdest, String))
buildTransitionRel switchList loc =
    Map.fromListWith (/\)
        [ (gate, atom (stsTLoc guard' varModel, endLoc))
        | (initLoc, gate, guard', varModel, endLoc) <- switchList
        , initLoc == loc
        ]

buildValuation :: Map.Map String (Some Variable) -> Map.Map String JSON.Value -> Either String Valuation
buildValuation locVarCtx initVal =
    fmap (assignValues . map snd) $ forM (Map.toList locVarCtx) $ \(name, Some var) ->
        case (varType var, Map.lookup name initVal) of
            (IntType,    Just (JSON.Number n)) -> Right (name, insertIntoValuation var (CInt (round n)))
            (BoolType,   Just (JSON.Bool b))   -> Right (name, insertIntoValuation var (CBool b))
            (CharType,   Just (JSON.String (unpack -> [c]))) -> Right (name, insertIntoValuation var (CChar c))
            (FloatType,  Just (JSON.Number n)) -> Right (name, insertIntoValuation var (CFloat (toRealFloat n)))
            (t, Just _)  -> Left $ "wrong type for initial value of '" ++ name ++ "', expected " ++ show t
            (_, Nothing) -> Right (name, insertIntoValuation var (defaultConst (varType var)))
    where
        -- TODO: for now give a default valuation if not present in the json, we can leave it blank and define
        -- this by test in the future
        defaultConst :: Type t -> Constant t
        defaultConst IntType    = CInt 0
        defaultConst FloatType  = CFloat 0.0
        defaultConst BoolType   = CBool False
        defaultConst CharType = CChar 'a'
        defaultConst (ListType t) = CList [] t
        defaultConst (SetType t) = withExprConstraints t $ CSet (RegularSet mempty) t
        defaultConst (TupleType a b) = CTuple (constValue $ defaultConst a) (constValue $ defaultConst b) a b
        defaultConst (SumType a b) = CSum (Left $ constValue $ defaultConst a) a b

convertSTSJson :: STSJsonFormat -> Either String (String, IOSTS FreeLattice String String String, Valuation)
convertSTSJson json = do
    (locVarMap, accessors1) <- buildVarMap (stsJsonLocVars json)
    (paramMap, accessors2)  <- buildVarMap (stsJsonParams json)
    let accMap = accessors1 <> accessors2
    initVal    <- buildValuation locVarMap (stsJsonInitValuation json)
    let varMap = locVarMap `Map.union` paramMap
    inputGateMap  <- buildGateMap In  varMap (stsJsonInputGates json)
    outputGateMap <- buildGateMap Out varMap (stsJsonOutputGates json)
    let gateMap = inputGateMap `Map.union` outputGateMap
        alphabet  = Set.fromList (Map.elems gateMap)
    guardMap' <- traverse (toExpr varMap accMap) (stsJsonGuards json)
    guardMap <- traverse (\(tp :=> e) -> case tp of
      BoolType -> Right e
      _ -> Left "guard with non-bool type") guardMap'
    assignMap <- buildAssignmentMap varMap accMap (stsJsonAssignments json)
    switchList <- buildSwitchList gateMap guardMap assignMap (stsJsonSwitches json)
    let transRel = buildTransitionRel switchList
        initCfg  = atom $ locId (stsJsonInitLoc json)
        sts      = automaton initCfg alphabet transRel
    return (stsJsonId json, sts, initVal)

{-| 
    Read a JSON file and parse an STS from it. Returns a tuple (ID, STS, Initial Valuation) if successful,
    or an error message if parsing fails.
-}
stsFromJSONFile :: FilePath -> IO (Either String (String,IOSTS FreeLattice String String String, Valuation))
stsFromJSONFile path = do
    bytes <- BSL.readFile path
    return $ case JSON.eitherDecode bytes of
        Left  err     -> Left $ "JSON decode error: " ++ err
        Right stsJson -> convertSTSJson stsJson

{-|
    Read a JSON file containing a list of STSs, and parse each one.
-}
stsListFromJSONFile :: FilePath -> IO (Either String [(String, IOSTS FreeLattice String String String, Valuation)])
stsListFromJSONFile path = do
    bytes <- BSL.readFile path
    return $ case JSON.eitherDecode bytes of
        Left  err      -> Left $ "JSON decode error: " ++ err
        Right stsJsons -> forM stsJsons convertSTSJson
