{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}


-- ----------------------------------------------------------------------------------------- --
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module Lattest.SMT.TXS2SMT

-- ----------------------------------------------------------------------------------------- --
--
-- Translate TorXakis definitions, declarations, and assertions into SMT
--
-- ----------------------------------------------------------------------------------------- --
-- export

(-- initialEnvNames    
--, insertSort
--, insertCstr
--, insertFunc
--, basicDefinitionsSMT
--, sortdefsToSMT      
--, funcdefsToSMT      
SMTExpr
, assertionsToSMT    
--, declarationsToSMT          
, valexprToSMT       
)

-- ----------------------------------------------------------------------------------------- --
--import

where

import qualified Data.Map      as Map
import           Data.Maybe
import qualified Data.Set      as Set
import qualified Data.List     as List
import           Data.Text     (Text)
import qualified Data.Text     as T

import           Lattest.Model.Symbolic.ValExpr.Constant
--import           CstrDef
--import           CstrId
import           Lattest.Model.Symbolic.ValExpr.FreeMonoidX
--import           FuncDef
--import           FuncId
--import           Lattest.SMT.RegexXSD2SMT
import           Lattest.SMT.SMTData
import           Lattest.SMT.SMTString
--import           SortDef
--import           SortId
import           Lattest.Model.Symbolic.ValExpr.ValExpr
--import           Variable
--import           VarId

-- ----------------------------------------------------------------------------------------- --
-- initialEnvNames
{-
initialEnvNames :: EnvNames
initialEnvNames  = EnvNames
    (Map.fromList [(sortIdBool,       "Bool"),
                   (sortIdInt,        "Int"),
                   (sortIdString,     "String"),
                   (sortIdRegex,      error "Regex is not defined in SMT")])
    Map.empty
    Map.empty
-}
-- ----------------------------------------------------------------------------------------- --
-- initialEnvNames
{-
toFieldName :: CstrId -> Int -> Text
toFieldName cstrid field  =  T.concat [toCstrName cstrid, "$", (T.pack . show) field]

toIsCstrName :: CstrId -> Text
toIsCstrName cstrid  =  "is-" <> toCstrName cstrid

toCstrName :: CstrId -> Text
toCstrName cstrid  =  T.concat [SortId.name (cstrsort cstrid), "$", CstrId.name cstrid]

toSortName :: SortId -> Text
toSortName = SortId.name

toFuncName :: FuncId -> Text
toFuncName funcId  =  T.concat ["f", (T.pack . show) (FuncId.unid funcId), "$", FuncId.name funcId]

insertSort :: (SortId, SortDef) -> EnvNames -> EnvNames
insertSort (sid, _) enames
  = if sid `Map.member` sortNames enames
       then error $ "TXS TXS2SMT insertMap: Sort " ++ show sid ++ " already defined\n"
       else enames { sortNames = Map.insert sid (toSortName sid) (sortNames enames) }
insertCstr :: (CstrId, CstrDef) -> EnvNames -> EnvNames
insertCstr (cd, CstrDef c fs) enames
  =  if cd `Map.member` cstrNames enames
       then error $ "TXS TXS2SMT insertMap: Constructor (" ++ show cd ++ ", CstrDef " ++
                    show c ++ " " ++ show fs ++  ") already defined\n"
       else foldr ( \(f,p) enames' -> enames' { funcNames = Map.insert f (toFieldName cd p) (funcNames enames') } )
                  ( enames { funcNames = Map.insert c (toIsCstrName cd) (funcNames enames)
                           , cstrNames = Map.insert cd (toCstrName cd) (cstrNames enames)
                           } 
                  )
                  (zip fs [0..])

insertFunc :: (FuncId, FuncDef VarId) -> EnvNames -> EnvNames
insertFunc (funcId, FuncDef x y) enames
  =  if funcId `Map.member` funcNames enames
       then error $ "TXS TXS2SMT insertMap: Function  (" ++ show funcId ++ ", FuncDef " ++
                    show x ++ " " ++ show y ++  ") already defined\n"
       else enames { funcNames = Map.insert funcId (toFuncName funcId) (funcNames enames) }
-}
       
-- ----------------------------------------------------------------------------------------- --
-- basic definitions for SMT
-- native Torxakis functions that are not natively supported in SMT
-- ----------------------------------------------------------------------------------------- --
basicDefinitionsSMT :: Text
basicDefinitionsSMT = ""

-- | convert sort definitions to SMT type declarations (as multiple lines of commands)
{-sortdefsToSMT :: EnvNames -> EnvDefs -> Text
sortdefsToSMT enames edefs =
    let sorts = Map.keys (sortDefs edefs) in
        case sorts of
            []      -> ""
            _       -> "(declare-datatypes () (\n"
                       <> foldMap (\s -> "    (" <> justLookupSort s enames <> foldMap cstrToSMT (getCstrs s) <> ")\n" )
                                  sorts
                       <> ") )\n"
    where
        -- get the constructors of an ADT
        getCstrs :: SortId -> [(CstrId, CstrDef)]
        getCstrs s = [(cstrId', cstrDef) | (cstrId', cstrDef) <- Map.toList (cstrDefs edefs), cstrsort cstrId' == s]

        -- convert the given constructor to a SMT constructor declaration
        cstrToSMT :: (CstrId, CstrDef) -> Text
        cstrToSMT (cstrId', CstrDef _ fields) = " (" <> justLookupCstr cstrId' enames
                                                     <> cstrFieldsToSMT cstrId' fields 
                                                     <> ")"

        -- convert the given constructor fields to a SMT constructor declaration
        cstrFieldsToSMT :: CstrId -> [FuncId] -> Text
        cstrFieldsToSMT cstrId' fields =
            case fields of
                []  -> ""
                _   -> " (" <> T.intercalate ") (" (map (\(f,p) -> toFieldName cstrId' p <> " " <> justLookupSort (funcsort f) enames)
                                                        (zip fields [0..]) ) <> ")"
-}

-- | Convert function definitions to SMT type declarations (as multiple lines
-- of commands).
{-funcdefsToSMT :: EnvNames -> Map.Map FuncId (FuncDef VarId) -> Text
funcdefsToSMT enames fdefs =
    toTxs (map toDT (Map.toList fdefs))
  where
    toTxs :: [(Text ,Text)] -> Text
    toTxs [] = ""
    toTxs l = let (lD,lT) = unzip l in
                "(define-funs-rec\n  (\n    " <> T.intercalate "\n    " lD <> "\n  )\n  (\n    " <> T.intercalate "\n    " lT <> "\n  )\n)\n"

    toDT :: (FuncId, FuncDef VarId) -> (Text, Text)
    toDT (funcId, FuncDef vs expr)  = ("(" <> justLookupFunc funcId enames
                                           <> "(" <> T.intercalate " " (map (\v -> "(" <> vname v <> " " <> justLookupSort (varsort v) enames <> ")") vs) <> ") " 
                                           <> justLookupSort (funcsort funcId) enames
                                           <> ")"
                                      , valexprToSMT enames expr
                                      )
-}

-- ----------------------------------------------------------------------------------------- --
-- assertions to SMT
-- ----------------------------------------------------------------------------------------- --
assertionsToSMT :: [ValExprBool] -> Text
assertionsToSMT assertions =
        T.intercalate "\n" (map assertionToSMT assertions)
    where
        assertionToSMT :: ValExprBool -> Text
        assertionToSMT expr = "(assert " <> valexprToSMT expr <> ")"


integer2smt :: Integer -> Text
integer2smt n | n < 0 = "(- " <> (T.pack . show) (abs n) <> ")"
integer2smt n = (T.pack . show) n
-- ----------------------------------------------------------------------------------------- --
-- constToSMT: translate a constant to a SMT text
-- ----------------------------------------------------------------------------------------- --
constToSMT :: Constant -> Text
constToSMT (Cbool b)        = if b
                                then "true"
                                else "false"
constToSMT (Cint n)         = integer2smt n
constToSMT (Cstring s)      =  "\"" <> stringToSMT s <> "\""
--constToSMT (Cregex r)       =  xsd2smt r
--constToSMT (Ccstr cd [])    =        justLookupCstr cd
--constToSMT (Ccstr cd args') = "(" <> justLookupCstr cd <> " " <> T.intercalate " " (map (constToSMT enames) args') <> ")"
constToSMT x                = error ("Illegal input constToSMT - " <> show x)

class SMTExpr t where
    valexprToSMT :: ValExpr t -> Text

-- ----------------------------------------------------------------------------------------- --
-- valexprToSMT: translate a ValExpr to a SMT constraint
-- ----------------------------------------------------------------------------------------- --
instance SMTExpr ValExprIntView where
    --valexprToSMT (view -> Vfunc funcId [])   =         justLookupFunc funcId enames
    --valexprToSMT (view -> Vfunc funcId args') = "(" <> justLookupFunc funcId enames <> " " <> T.intercalate " " (map (valexprToSMT enames) args') <> ")"

    --valexprToSMT (view -> Vcstr cd [])    =        justLookupCstr cd enames
    --valexprToSMT (view -> Vcstr cd args') = "(" <> justLookupCstr cd enames <> " " <> T.intercalate " " (map (valexprToSMT enames) args') <> ")"

    --valexprToSMT (view -> Viscstr cd arg)      = "(" <> toIsCstrName cd <> " " <> valexprToSMT enames arg <> ")"
    --valexprToSMT (view -> Vaccess cd _n p arg) = "(" <> toFieldName cd p <> " " <> valexprToSMT enames arg <> ")"


    valexprToSMT (view -> VIntConst c) = constToSMT c

    valexprToSMT (view -> VIntVar (Variable varName IntType))  =  T.pack varName
    valexprToSMT (view -> VIntVar v)  =  error $ "valexprToSMT: int expression containing variable " ++ show v

    valexprToSMT (view -> VIntIte c expr1 expr2) = "(ite " <> valexprToSMT c <> " "  <> valexprToSMT expr1 <> " " <> valexprToSMT expr2 <> ")"

    valexprToSMT (view -> VIntSum s) =
        let ol = toOccurListT s in
            case ol of
            {  [o] -> arg2smt o
            ;   _  -> "(+ " <> T.intercalate " " (map arg2smt ol) <> ")"
            }
        where
            arg2smt :: (ValExprInt, Integer) -> Text
            arg2smt (vexpr, 1)                              = valexprToSMT vexpr
            arg2smt (vexpr, -1)                             = "(- " <> valexprToSMT vexpr <> ")"
            arg2smt (vexpr, multiplier) |  multiplier /= 0  = "(* " <> integer2smt multiplier <> " " <> valexprToSMT vexpr <> ")"
            arg2smt (_, multiplier)                         = error ("valexprToSMT - arg2smt - illegal multiplier " ++ show multiplier)

    valexprToSMT (view -> VIntProduct p) =
        let ol = toOccurListT p in
            case ol of
            {  [o] -> arg2smt o
            ;   _  -> "(* " <> T.intercalate " " (map arg2smt ol) <> ")"
            }
        where
            arg2smt :: (ValExprInt, Integer) -> Text
            arg2smt (vexpr, 1)                  = valexprToSMT vexpr
            arg2smt (vexpr, power) |  power > 0 = "(^ " <> valexprToSMT vexpr <> " " <> integer2smt power <> ")"
            arg2smt (_, power)                  = error ("valexprToSMT - arg2smt - illegal power " ++ show power)

    valexprToSMT (view -> VIntDivide t n) = "(div " <> valexprToSMT t <> " "  <> valexprToSMT n <> ")"
    valexprToSMT (view -> VIntModulo t n) = "(mod " <> valexprToSMT t <> " "  <> valexprToSMT n <> ")"
    valexprToSMT (view -> VLength expr)  =
        "(str.len " <> valexprToSMT expr <> ")"

instance SMTExpr ValExprBoolView where
    valexprToSMT (view -> VBoolConst c) = constToSMT c

    valexprToSMT (view -> VBoolVar (Variable varName BoolType))  =  T.pack varName
    valexprToSMT (view -> VBoolVar v)  =  error $ "valexprToSMT: bool expression containing variable " ++ show v

    valexprToSMT (view -> VBoolIte c expr1 expr2) = "(ite " <> valexprToSMT c <> " "  <> valexprToSMT expr1 <> " " <> valexprToSMT expr2 <> ")"

    valexprToSMT (view -> VGezInt v)      = "(<= 0 " <> valexprToSMT v <> ")"

    valexprToSMT (view -> VEqualInt expr1 expr2)  =
        "(= " <> valexprToSMT expr1 <> " " <> valexprToSMT expr2 <> ")"

    valexprToSMT (view -> VEqualBool expr1 expr2)  =
        "(= " <> valexprToSMT expr1 <> " " <> valexprToSMT expr2 <> ")"

    valexprToSMT (view -> VEqualString expr1 expr2)  =
        "(= " <> valexprToSMT expr1 <> " " <> valexprToSMT expr2 <> ")"

    valexprToSMT (view -> VNot expr)  =
        "(not " <> valexprToSMT expr <> ")"

    valexprToSMT (view -> VAnd exprs)  =
        "(and " <> T.intercalate " " (map valexprToSMT (Set.toList exprs)) <> ")"

instance SMTExpr ValExprStringView where
    valexprToSMT (view -> VStringConst c) = constToSMT c

    valexprToSMT (view -> VStringVar (Variable varName StringType))  =  T.pack varName
    valexprToSMT (view -> VStringVar v)  =  error $ "valexprToSMT: bool expression containing variable " ++ show v

    valexprToSMT (view -> VStringIte c expr1 expr2) = "(ite " <> valexprToSMT c <> " "  <> valexprToSMT expr1 <> " " <> valexprToSMT expr2 <> ")"

    valexprToSMT (view -> VAt s p)  =
        "(str.at " <> valexprToSMT s <> " " <> valexprToSMT p <> ")"
    valexprToSMT (view -> VConcat vexprs)  =
        "(str.++ " <> T.intercalate " " (map valexprToSMT vexprs) <> ")"
--    valexprToSMT (view -> Vstrinre s r)  =
--        "(str.in.re " <> valexprToSMT s <> " " <> valexprToSMT r <> ")"
    valexprToSMT x = error ("Illegal input valexprToSMT - " ++ show x)

-- ------------------------------                                                                 
justLookupType :: Type -> Text
justLookupType IntType = "Int"
justLookupType BoolType = "Bool"
justLookupType StringType = "String"
{-
justLookupCstr :: CstrId -> EnvNames -> Text
justLookupCstr cd enames = fromMaybe (error $ "CstrId " ++ show cd ++ " not found in mapping with keys: " ++ show (Map.keys (cstrNames enames)) ++ "\n") (Map.lookup cd (cstrNames enames))

justLookupSort :: SortId -> EnvNames -> Text
justLookupSort sd enames = fromMaybe (error $ "SortId " ++ show sd ++ " not found in mapping with keys: " ++ show (Map.keys (sortNames enames)) ++ "\n") (Map.lookup sd (sortNames enames))

justLookupFunc :: FuncId -> EnvNames -> Text
justLookupFunc fd enames = fromMaybe (error $ "FuncId " ++ show fd ++ " not found in mapping with keys: " ++ show (Map.keys (funcNames enames)) ++ "\n") (Map.lookup fd (funcNames enames))
-}
-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --
