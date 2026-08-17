{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Lattest.Util.STSJSONParser (
    stsFromJSONFile,
) where

import Control.Monad (forM)
import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Map.Strict as Map
import Data.Scientific (floatingOrInteger, toRealFloat, Scientific)
import qualified Data.Set as Set
import Data.Text (unpack)
import Data.Maybe (fromMaybe)
import Lattest.Model.Alphabet (IOAct (..), SymInteract (..))
import Lattest.Model.Automaton (stsTLoc, STStdest)
import Lattest.Model.BoundedMonad (FreeLattice, atom, (/\))
import Lattest.Model.StandardAutomata (IOSTS, automaton)
import Lattest.Model.Symbolic.Expr ((=:), (./), (.%), (.+), (.-), (.*), (.==), (.>=), (.<=), (.<), (.>), (.||), (.&&), sNeg, sNot, assignment, sTrue, sConst, sVar, Expr, ExprNum, Type (..), Variable (..), Valuation, VarModel, Constant(..), insertIntoValuation, assignValues, Constant(..))
import Data.Some (Some (..))
import Data.Type.Equality ((:~:)(..))
import Data.GADT.Compare (GEq(..))
import Lattest.Model.Symbolic.Internal.ExprDefs (withExprConstraints, Constant (..))
import Data.SBV (RCSet (..))

data UntypedExpr
    = UEBool Bool
    | UENumber Scientific
    | UEStr  String
    | UEOp1  String UntypedExpr
    | UEOp2  String UntypedExpr UntypedExpr
    deriving (Show, Eq)

instance JSON.FromJSON UntypedExpr where
    parseJSON (JSON.Bool b)   = pure (UEBool b)
    parseJSON (JSON.Number n) = pure (UENumber n)
    parseJSON (JSON.String s) = pure (UEStr (unpack s))
    parseJSON (JSON.Object o) = do
        (op :: String) <- o JSON..: "op"
        case op of
            "neg" -> UEOp1 op <$> o JSON..: "rhs"
            "not" -> UEOp1 op <$> o JSON..: "rhs"
            _     -> UEOp2 op <$> o JSON..: "lhs" <*> o JSON..: "rhs"
    parseJSON _ = fail "expected expression"

type VarMap = Map.Map String (Some Variable)

lookupVar :: VarMap -> String -> Type t -> (Variable t -> Expr a) -> Either String (Expr a)
lookupVar varmap name expected mk = case Map.lookup name varmap of
    Just (Some v@(Variable _ t)) | Just Refl <- t `geq` expected -> Right (mk v)
    Just (Some (Variable _ t)) -> Left $ "variable '" ++ name ++ "' has type " ++ show t ++ ", expected " ++ show expected
    Nothing             -> Left $ "unknown variable: " ++ name

-- Used for equality and ordering comparisons, where the result is defined based on the type of lhs and rhs.
-- A variable's declared type always takes priority over a literal's type
inferOperandType :: VarMap -> UntypedExpr -> UntypedExpr -> Either String (Some Type)
inferOperandType varmap lhs rhs =
    case (varOperandType lhs, varOperandType rhs) of
        (Just t, _) -> Right t
        (_, Just t) -> Right t
        _ -> case (literalOperandType lhs, literalOperandType rhs) of
            (Just t, _) -> Right t
            (_, Just t) -> Right t
            _           -> Left "cannot determine operand type for operator"
    where
        varOperandType (UEStr name) = (\(Some x) -> Some (varType x)) <$> Map.lookup name varmap
        varOperandType _            = Nothing
        literalOperandType (UEBool _)  = Just $ Some BoolType
        literalOperandType (UENumber n)
          | Left _ <- floatingOrInteger @Double @Integer n = Just $ Some FloatType
          | otherwise = Just $ Some IntType
        literalOperandType _           = Nothing

toBoolExpr :: VarMap -> UntypedExpr -> Either String (Expr Bool)
toBoolExpr _   (UEBool b)          = Right (sConst b)
toBoolExpr varmap (UEStr name)        = lookupVar varmap name BoolType sVar
toBoolExpr varmap (UEOp1 "not" e)    = sNot  <$> toBoolExpr varmap e
toBoolExpr varmap (UEOp2 "&&" e1 e2) = (.&&) <$> toBoolExpr varmap e1 <*> toBoolExpr varmap e2
toBoolExpr varmap (UEOp2 "||" e1 e2) = (.||) <$> toBoolExpr varmap e1 <*> toBoolExpr varmap e2
toBoolExpr varmap (UEOp2 "==" e1 e2) = do
    t <- inferOperandType varmap e1 e2
    case t of
        Some IntType    -> (.==) <$> toIntExpr   varmap e1 <*> toIntExpr   varmap e2
        Some BoolType   -> (.==) <$> toBoolExpr  varmap e1 <*> toBoolExpr  varmap e2
        Some CharType   -> (.==) <$> toCharExpr  varmap e1 <*> toCharExpr   varmap e2
        Some FloatType  -> (.==) <$> toFloatExpr varmap e1 <*> toFloatExpr varmap e2
        Some (ListType tp) -> withExprConstraints tp $ (.==) <$> toListExpr tp varmap e1 <*> toListExpr tp varmap e2
        Some (SetType _) -> error "no eq on rcsets"
        Some (TupleType a b) -> withExprConstraints (TupleType a b) $ (.==) <$> toTupleExpr a b varmap e1 <*> toTupleExpr a b varmap e2
        Some (SumType a b) -> withExprConstraints (SumType a b) $ (.==) <$> toEitherExpr a b varmap e1 <*> toEitherExpr a b varmap e2
toBoolExpr varmap (UEOp2 "!=" e1 e2) = sNot <$> toBoolExpr varmap (UEOp2 "==" e1 e2)
toBoolExpr varmap (UEOp2 "<"  e1 e2) = toComparisonExpr (.<)  varmap e1 e2
toBoolExpr varmap (UEOp2 "<=" e1 e2) = toComparisonExpr (.<=) varmap e1 e2
toBoolExpr varmap (UEOp2 ">"  e1 e2) = toComparisonExpr (.>)  varmap e1 e2
toBoolExpr varmap (UEOp2 ">=" e1 e2) = toComparisonExpr (.>=) varmap e1 e2
toBoolExpr _   e                   = Left $ "not a boolean expression: " ++ show e

-- Numeric ordering comparisons are defined for both Integer and Float operands, but never mixed.
toComparisonExpr :: (forall t. ExprNum t => Expr t -> Expr t -> Expr Bool) -> VarMap -> UntypedExpr -> UntypedExpr -> Either String (Expr Bool)
toComparisonExpr cmp varmap e1 e2 = do
    t <- inferOperandType varmap e1 e2
    case t of
        Some IntType   -> cmp <$> toIntExpr   varmap e1 <*> toIntExpr   varmap e2
        Some FloatType -> cmp <$> toFloatExpr varmap e1 <*> toFloatExpr varmap e2
        Some tp        -> Left $ "comparison operator is not defined for type " ++ show tp

toIntExpr :: VarMap -> UntypedExpr -> Either String (Expr Integer)
toIntExpr _   (UENumber n)
 | Right i <- floatingOrInteger @Double n = Right (sConst i)
toIntExpr varmap (UEStr name)         = lookupVar varmap name IntType sVar
toIntExpr varmap (UEOp1 "neg" e)     = sNeg <$> toIntExpr varmap e
toIntExpr varmap (UEOp2 "+"  e1 e2)  = (.+) <$> toIntExpr varmap e1 <*> toIntExpr varmap e2
toIntExpr varmap (UEOp2 "-"  e1 e2)  = (.-) <$> toIntExpr varmap e1 <*> toIntExpr varmap e2
toIntExpr varmap (UEOp2 "*"  e1 e2)  = (.*) <$> toIntExpr varmap e1 <*> toIntExpr varmap e2
toIntExpr varmap (UEOp2 "/"  e1 e2)  = (./) <$> toIntExpr varmap e1 <*> toIntExpr varmap e2
toIntExpr varmap (UEOp2 "%"  e1 e2)  = (.%) <$> toIntExpr varmap e1 <*> toIntExpr varmap e2
toIntExpr _   e                    = Left $ "not an integer expression: " ++ show e

toListExpr :: Type t -> VarMap -> UntypedExpr -> Either String (Expr [t])
toListExpr t varmap e = case e of
  UEStr name -> lookupVar varmap name (ListType t) sVar
  -- TODO: add operators that return lists
  _ -> Left $ "not a list expression: " ++ show e

toSetExpr :: Type t -> VarMap -> UntypedExpr -> Either String (Expr (RCSet t))
toSetExpr t varmap e = case e of
  UEStr name -> lookupVar varmap name (SetType t) sVar
  -- TODO: add operators that return sets
  _ -> Left $ "not a list expression: " ++ show e

toTupleExpr :: Type a -> Type b -> VarMap -> UntypedExpr -> Either String (Expr (a,b))
toTupleExpr t1 t2 varmap e = case e of
  UEStr name -> lookupVar varmap name (TupleType t1 t2) sVar
  -- TODO: add operators that return tuples
  _ -> Left $ "not a tuple expression: " ++ show e

toEitherExpr :: Type a -> Type b -> VarMap -> UntypedExpr -> Either String (Expr (Either a b))
toEitherExpr t1 t2 varmap e = case e of
  UEStr name -> lookupVar varmap name (SumType t1 t2) sVar
  -- TODO: add operators that return eithers
  _ -> Left $ "not a tuple expression: " ++ show e

toFloatExpr :: VarMap -> UntypedExpr -> Either String (Expr Double)
toFloatExpr _   (UENumber n)          = Right (sConst $ toRealFloat n)
toFloatExpr varmap (UEStr name)         = lookupVar varmap name FloatType sVar
toFloatExpr varmap (UEOp1 "neg" e)     = sNeg <$> toFloatExpr varmap e
toFloatExpr varmap (UEOp2 "+"  e1 e2)  = (.+) <$> toFloatExpr varmap e1 <*> toFloatExpr varmap e2
toFloatExpr varmap (UEOp2 "-"  e1 e2)  = (.-) <$> toFloatExpr varmap e1 <*> toFloatExpr varmap e2
toFloatExpr varmap (UEOp2 "*"  e1 e2)  = (.*) <$> toFloatExpr varmap e1 <*> toFloatExpr varmap e2
toFloatExpr varmap (UEOp2 "/"  e1 e2)  = (./) <$> toFloatExpr varmap e1 <*> toFloatExpr varmap e2
toFloatExpr _   e                    = Left $ "not a real expression: " ++ show e

-- unknown strings are treated as string literals.
toCharExpr :: VarMap -> UntypedExpr -> Either String (Expr Char)
toCharExpr varmap (UEStr name) = error "todo: change untypedexpr? Just match on one-character strings? Would like to have a clear distinction between variables and literal strings/chars"

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

newtype VarDefJson = VarDefJson { varDefJsonType :: String }

instance JSON.FromJSON VarDefJson where
    parseJSON = JSON.withObject "VarDefJson" $ \o ->
        VarDefJson <$> o JSON..: "type"

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
    , switchJsonGuard       :: Maybe String
    , switchJsonAssignments :: [String]
    , switchJsonEndLoc      :: LocationId
    }

instance JSON.FromJSON SwitchDefJson where
    parseJSON = JSON.withObject "SwitchDefJson" $ \o ->
        SwitchDefJson
            <$> o JSON..:  "init_loc"
            <*> o JSON..:  "gate"
            <*> o JSON..:? "guard"
            <*> (o JSON..:? "assignments" JSON..!= [])
            <*> o JSON..:  "end_loc"

data STSJsonFormat = STSJsonFormat
    { stsJsonInitLoc       :: LocationId
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
            <$> o JSON..:  "initial_location"
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

parseVarType :: String -> Either String (Some Type)
parseVarType "integer" = Right $ Some IntType
parseVarType "int"     = Right $ Some IntType
parseVarType "float"   = Right $ Some FloatType
parseVarType "bool"    = Right $ Some BoolType
parseVarType "boolean" = Right $ Some BoolType
parseVarType "char"    = Right $ Some CharType
parseVarType t         = Left $ "unknown variable type: " ++ t

buildVarMap :: Map.Map String VarDefJson -> Either String (Map.Map String (Some Variable))
buildVarMap defs = Map.fromList <$> forM (Map.toList defs) (\(name, def) -> do
    t <- parseVarType (varDefJsonType def)
    case t of
      Some t' -> return (name, Some $ Variable name t'))

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
    -> String
    -> AssignmentDefJson
    -> Either String (VarModel -> VarModel)
buildAssignment varMap name def = do
    var <- case Map.lookup (assignmentJsonVar def) varMap of
        Just v  -> Right v
        Nothing -> Left $ "unknown variable '" ++ assignmentJsonVar def ++ "' in assignment '" ++ name ++ "'"
    let expr = assignmentJsonExpr def
    case var of
      Some v -> case varType v of
        IntType    -> (v =:) <$> toIntExpr  varMap expr
        FloatType  -> (v =:) <$> toFloatExpr varMap expr
        BoolType   -> (v =:) <$> toBoolExpr varMap expr
        CharType -> (v =:) <$> toCharExpr  varMap expr
        ListType t -> (v =:) <$> toListExpr t varMap expr
        SetType t -> (v =:) <$> toSetExpr t varMap expr
        TupleType a b -> (v =:) <$> toTupleExpr a b varMap expr
        SumType a b -> (v =:) <$> toEitherExpr a b varMap expr

buildAssignmentMap
    :: VarMap
    -> Map.Map String AssignmentDefJson
    -> Either String (Map.Map String (VarModel -> VarModel))
buildAssignmentMap varMap defs =
    Map.fromList <$> forM (Map.toList defs) (\(name, def) ->
        (name,) <$> buildAssignment varMap name def)

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
            Nothing    -> Right sTrue
            Just gname -> case Map.lookup gname guardMap of
                Just g  -> Right g
                Nothing -> Left $ "unknown guard '" ++ gname ++ "' in switch '" ++ name ++ "'"
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

convertSTSJson :: STSJsonFormat -> Either String (IOSTS FreeLattice String String String, Valuation)
convertSTSJson json = do
    locVarMap <- buildVarMap (stsJsonLocVars json)
    paramMap  <- buildVarMap (stsJsonParams json)
    initVal    <- buildValuation locVarMap (stsJsonInitValuation json)
    let varMap = locVarMap `Map.union` paramMap
    inputGateMap  <- buildGateMap In  varMap (stsJsonInputGates json)
    outputGateMap <- buildGateMap Out varMap (stsJsonOutputGates json)
    let gateMap = inputGateMap `Map.union` outputGateMap
        alphabet  = Set.fromList (Map.elems gateMap)
    guardMap  <- traverse (toBoolExpr varMap) (stsJsonGuards json)
    assignMap <- buildAssignmentMap varMap (stsJsonAssignments json)
    switchList <- buildSwitchList gateMap guardMap assignMap (stsJsonSwitches json)
    let transRel = buildTransitionRel switchList
        initCfg  = atom $ locId (stsJsonInitLoc json)
        sts      = automaton initCfg alphabet transRel
    return (sts, initVal)

{-| 
    Read a JSON file and parse an STS from it.
-}
stsFromJSONFile :: FilePath -> IO (Either String (IOSTS FreeLattice String String String, Valuation))
stsFromJSONFile path = do
    bytes <- BSL.readFile path
    return $ case JSON.eitherDecode bytes of
        Left  err     -> Left $ "JSON decode error: " ++ err
        Right stsJson -> convertSTSJson stsJson
