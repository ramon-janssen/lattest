{-# OPTIONS_HADDOCK hide, prune #-}
{-
This is a modified version of:
TorXakis - Model Based Testing
See LICENSE in the parent Symbolic folder.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lattest.Model.Symbolic.Internal.ExprDefs
( ExprView(..)
, Expr(..)       -- for local usage only!
, eval
, reduce
, Variable(..)
, Type(..)
, Constant(..)
, constType
, ConstType
, fromConst
, toConst
, ExprType
, typeOf
, typeOf'
, isConst
, freeVars
, ExprConstraints
, List(..)
, withExprConstraints
)
where

import qualified Data.List as List
import           Data.Set         (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Text as Text(pack, unpack)
import           GHC.Integer (divInteger)

import           Lattest.Model.Symbolic.Internal.FreeMonoidX
import qualified Lattest.Model.Symbolic.Internal.FreeMonoidX as FMX
import           Lattest.Model.Symbolic.Internal.Product
import           Lattest.Model.Symbolic.Internal.Sum

import qualified Data.Aeson as JSON
import qualified Data.Aeson.KeyMap as JSON

import qualified Data.Scientific as DS
import qualified Data.Some.Church as Church
import Data.Some (Some(..))
import Data.GADT.Compare (GEq(..), GOrdering (..), GCompare (..))
import Data.Type.Equality ((:~:)(..))
import Data.GADT.Show (GRead (..), GShow (..), defaultGshowsPrec)
import Data.SBV (SymVal, HasKind)
import Data.EqP (EqP (..))
import Data.Maybe (isJust)
import Data.Constraint.Extras (Has (..))
import Data.Constraint.Compose (ComposeC)
import qualified Data.Vector as Vec
import Data.String (IsString(..))
import Control.Monad ((<=<))
import Data.Data (Data)

-- avoids overlapping with String in typeclass instances
newtype List a = List { getList :: [a] }
  deriving (Ord, Eq, Show, Read, Data, HasKind)
data Type a where
  IntType :: Type Integer
  BoolType :: Type Bool
  StringType :: Type String
  ListType :: Type a -> Type (List a)
deriving instance Eq (Type a)
deriving instance Ord (Type a)
instance (Read a, SymVal a, Data a, Show a) => SymVal (List a) where
instance EqP Type where
  eqp x y = isJust $ geq x y
instance GEq Type where
  geq IntType IntType = Just Refl
  geq BoolType BoolType = Just Refl
  geq StringType StringType = Just Refl
  geq (ListType a) (ListType b) = (\Refl -> Refl) <$> geq a b
  geq _ _ = Nothing
instance GCompare Type where
  gcompare = \cases
    IntType IntType -> GEQ
    IntType _ -> GLT
    BoolType BoolType -> GEQ
    BoolType _ -> GLT
    StringType StringType -> GEQ
    StringType _ -> GLT
    (ListType a) (ListType b) -> case gcompare a b of
      GGT -> GGT
      GLT -> GLT
      GEQ -> GEQ
    _ _ -> GGT
instance Show (Type a) where
    show IntType = "Int"
    show BoolType = "Bool"
    show StringType = "String"
    show (ListType a) = "[ " ++ show a ++ " ]"
instance ExprType a => Read (Type a) where
  readsPrec _ =
    readParen False $ \s ->
      let tp = typeOf (undefined :: a)
          target = show tp
          len = length target
          (test, rest) = splitAt len s
      in ([(tp, rest) | test == target])
instance GRead Type where
  greadsPrec _ =
    readParen False $ \s ->
         [ (Church.mkSome StringType, rest)
         | ("String", rest) <- lex s
         ]
      ++ [ (Church.mkSome IntType, rest)
         | ("Int", rest) <- lex s
         ]
      ++ [ (Church.mkSome BoolType, rest)
         | ("Bool", rest) <- lex s
         ]
      ++ do
          ("[", s1) <- lex s
          (t, s2) <- greadsPrec 11 s1
          ("]", rest) <- lex s2
          Church.withSome t $ \(tp :: Type t) -> do
            return (Church.mkSome $ ListType tp, rest)

withExprConstraints :: Type x -> (ExprConstraints x => r) -> r
withExprConstraints t k = has @Data t $ has @Read t $ has @ConstType t $ has @Ord t $ has @Show t $ has @SymVal t $ has @ExprType t k

instance Has ExprType Type where
  has t k = case t of
    IntType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @ExprType t' k

instance Has Eq Type where
  has t k = case t of
    IntType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Eq t' k

instance Has Ord Type where
  has t k = case t of
    IntType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Ord t' k

instance Has Show Type where
  has t k = case t of
    IntType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Show t' k

instance Has Read Type where
  has t k = case t of
    IntType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Read t' k

instance Has Data Type where
  has t k = case t of
    IntType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Data t' k

instance Has SymVal Type where
  has t k = case t of
    IntType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Show t' $ has @Data t' $ has @Read t' $ has @SymVal t' k

class ExprType t where
    typeOf :: t -> Type t
    typeOf' :: f t -> Type t

instance ExprType Integer where
    typeOf _ = IntType
    typeOf' _ = IntType
instance ExprType Bool where
    typeOf _ = BoolType
    typeOf' _ = BoolType
instance ExprType String where
    typeOf _ = StringType
    typeOf' _ = StringType
instance ExprType a => ExprType (List a) where
    typeOf _ = ListType $ typeOf undefined
    typeOf' _ = ListType $ typeOf undefined


data Variable t = Variable {varName :: String, varType :: Type t} deriving (Eq, Ord)
instance GEq Variable where
  geq (Variable lname ltype) (Variable rname rtype)
    | lname == rname
    , Just Refl <- ltype `geq` rtype
    = Just Refl
    | otherwise = Nothing
instance GCompare Variable where
  gcompare (Variable lname ltype) (Variable rname rtype) =
    case compare lname rname of
      LT -> GLT
      GT -> GGT
      EQ -> gcompare ltype rtype
instance GShow Variable where
  gshowsPrec = defaultGshowsPrec
instance Has (ComposeC Eq Expr) Variable where
  has _ k = k
instance Has (ComposeC Ord Expr) Variable where
  has _ k = k
instance Has (ComposeC Show Expr) Variable where
  has _ k = k

instance Show (Variable a) where
    show (Variable name stype) = name ++ ":" ++ show stype

data Constant a where
  Cbool :: Bool -> Constant Bool
  Cint :: Integer -> Constant Integer
  Cstring :: String -> Constant String
  Clist :: Type a -> [Constant a] -> Constant (List a)
deriving instance Eq (Constant a)
deriving instance Ord (Constant a)
instance GEq Constant where
  geq = \cases
    (Cbool a) (Cbool b) | a == b -> Just Refl
    (Cint a) (Cint b) | a == b -> Just Refl
    (Cstring a) (Cstring b) | a == b -> Just Refl
    _ _ -> Nothing
instance GCompare Constant where
  gcompare = \case
    Cbool a -> \case
      Cbool b   -> case compare a b of
        LT -> GLT
        EQ -> GEQ
        GT -> GGT
      Cint{}    -> GLT
      Cstring{} -> GLT
      Clist{} -> GLT

    Cint a -> \case
      Cbool{}   -> GGT
      Cint b    -> case compare a b of
        LT -> GLT
        EQ -> GEQ
        GT -> GGT
      Cstring{} -> GLT
      Clist{} -> GLT

    Cstring a -> \case
      Cbool{}   -> GGT
      Cint{}    -> GGT
      Cstring b -> case compare a b of
        LT -> GLT
        EQ -> GEQ
        GT -> GGT
      Clist{} -> GLT

    Clist ta a -> \case
      Cbool{}   -> GGT
      Cint{}    -> GGT
      Cstring{} -> GLT
      Clist tb b -> case gcompare ta tb of
        GLT -> GLT
        GEQ -> case compare a b of
          LT -> GLT
          EQ -> GEQ
          GT -> GGT
        GGT -> GGT

instance GShow Constant where
  gshowsPrec d = \case
    Cbool b ->
      showParen (d > 10) $
        showString "Cbool " . showsPrec 11 b
    Cint i ->
      showParen (d > 10) $
        showString "Cint " . showsPrec 11 i
    Cstring s ->
      showParen (d > 10) $
        showString "Cstring " . showsPrec 11 s
    Clist t a ->
      showParen (d > 10) $
        showString "Clist @" . showsPrec 11 t . showString " " . showsPrec 11 a
instance GRead Constant where
  greadsPrec _ =
    readParen False $ \s ->
         [ (Church.mkSome (Cbool b), rest)
         | ("Cbool", s1) <- lex s
         , (b, rest) <- readsPrec 11 s1
         ]
      ++ [ (Church.mkSome (Cint i), rest)
         | ("Cint", s1) <- lex s
         , (i, rest) <- readsPrec 11 s1
         ]
      ++ [ (Church.mkSome (Cstring str), rest)
         | ("Cstring", s1) <- lex s
         , (str, rest) <- readsPrec 11 s1
         ]
      ++ do -- List monad: I couldn't get the list comprehension syntax to cooperate wrt Some scoping
      ("Clist", '@':s1) <- lex s
      (t, s2) <- greadsPrec 11 s1
      Church.withSome t $ \(tp :: Type t) -> do
        (xs, rest) <- has @ExprType tp $ readsPrec 11 s2
        return (Church.mkSome $ Clist tp xs, rest)
instance ExprType a => Read (Constant a) where
  readsPrec _ =
    readParen False $ \s ->
      case typeOf (undefined :: a) of
        IntType -> [ (Cint i, rest)
                   | ("Cint", s1) <- lex s
                   , (i, rest) <- readsPrec 11 s1
                   ]
        BoolType -> [ (Cbool b, rest)
                   | ("Cbool", s1) <- lex s
                   , (b, rest) <- readsPrec 11 s1
                   ]
        StringType -> [ (Cstring st, rest)
                   | ("Cstring", s1) <- lex s
                   , (st, rest) <- readsPrec 11 s1
                   ]
        ListType (tp' :: Type t) -> [ (Clist tp' xs, rest)
                   | ("Clist", '@':s1) <- lex s
                   , (_tp, s2)  <- has @ExprType tp' $ readsPrec @(Type t) 11 s1
                   , (xs, rest) <- has @ExprType tp' $ readsPrec 11 s2
                   ]

instance Has ExprType Constant where
  has c k = case c of
    Cint _ -> k
    Cbool _ -> k
    Cstring _ -> k
    Clist t' _ -> has @ExprType t' k

instance JSON.FromJSON (Some Constant) where
    parseJSON (JSON.Object m)
        | not $ JSON.member "value" m = fail "expected Constant with a value field"
        | not $ JSON.member "type" m = fail "expected Constant with a type field"
    parseJSON (JSON.Object m)
        | Just val <- JSON.lookup "type" m = parseType val >>= \case
            Some BoolType -> parseBool $ lkup "value" m
            Some IntType -> parseInt $ lkup "value" m
            Some StringType -> parseString $ lkup "value" m
            Some (ListType t) -> parseList t $ lkup "value" m
        where
        parseType (JSON.String (Text.unpack -> s)) = case s of
          "string" -> pure $ Some StringType
          "int" -> pure $ Some IntType
          "bool" -> pure $ Some BoolType
          '[':(init -> cs) -> (\(Some t) -> Some $ ListType t) <$> parseType (JSON.String (Text.pack cs))
          _ -> fail $ "bad type: " <> s
        parseType _ = fail "type is not a string"
        lkup :: JSON.Key -> JSON.KeyMap v -> v
        lkup k = Maybe.fromJust . JSON.lookup k
        parseBool (JSON.Bool b) = return $ Some $ Cbool b
        parseBool _ = fail "type indicates bool, but value is not of type bool"
        parseInt (JSON.Number (DS.floatingOrInteger @Double -> Right i)) = return $ Some $ Cint i
        parseInt _ = fail "type indicates int, but value is not of type int"
        parseString (JSON.String s) = return $ Some $ Cstring $ Text.unpack s
        parseString _ = fail "type indicates string, but value is not of type string"
        parseList t (JSON.Array xs) = Some . Clist t <$> mapM (
            (\(Some v) -> case has @ExprType v $ typeOf' v `geq` t of
              Nothing -> fail $ "type indicates list of " <> show t <> ", but at least one element was a " <> show (has @ExprType v $ typeOf' v)
              Just Refl -> pure v
            )
            <=< JSON.parseJSON @(Some Constant)
          ) (Vec.toList xs)
        parseList _ _ = fail "type indicates list, but value is not of type array"
    parseJSON _ = fail "expected Constant JSON"

instance JSON.ToJSON (Some Constant) where
    toJSON (Some (Cbool b)) = JSON.Object $ JSON.insert "type" "bool" $ JSON.insert "value" (JSON.Bool b) JSON.empty
    toJSON (Some (Cint i)) = JSON.Object $ JSON.insert "type" "int" $ JSON.insert "value" (JSON.Number $ fromInteger i) JSON.empty
    toJSON (Some (Cstring s)) = JSON.Object $ JSON.insert "type" "string" $ JSON.insert "value" (JSON.String $ Text.pack s) JSON.empty
    toJSON (Some (Clist t xs)) = JSON.Object $ JSON.insert "type" (fromString . showtype $ ListType t)
                                             $ JSON.insert "value" (JSON.Array $ Vec.fromList $ map (JSON.toJSON . Some) xs) JSON.empty
      where
        showtype :: Type a -> String
        showtype BoolType = "bool"
        showtype IntType = "int"
        showtype StringType = "string"
        showtype (ListType tp) = "[" <> showtype tp <> "]"

constType :: Constant a -> Type a
constType c = has @ExprType c $ typeOf' c

instance Show (Constant a) where
  show (Cbool b) = show b
  show (Cint i) = show i
  show (Cstring t) = show t
  show (Clist _ xs) = show xs

-- | convert a Constant to an typed value
class ExprType t => ConstType t where
    fromConst :: Constant t -> t
    toConst :: t -> Constant t

instance ConstType Bool where
    fromConst (Cbool b) = b
    toConst = Cbool

instance ConstType Integer where
    fromConst (Cint i) = i
    toConst = Cint

instance ConstType String where
    fromConst (Cstring s) = s
    toConst = Cstring

instance ConstType a => ConstType (List a) where
    fromConst (Clist _ xs) = List $ map fromConst xs
    toConst (List xs) = Clist (typeOf undefined) $ map toConst xs

instance Has ConstType Type where
  has t k = case t of
    IntType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @ConstType t' k

-- ----------------------------------------------------------------------------------------- --
-- value expression

data ExprView t where
    Var :: {variable :: Variable t} -> ExprView t
    Const :: ExprConstraints t => {constant :: t} -> ExprView t
    Ite :: {conditional :: ExprView Bool, trueBranch :: ExprView t, falseBranch :: ExprView t} -> ExprView t
    Equal :: ExprConstraints t => {eqType :: Type t, left :: ExprView t, right :: ExprView t} -> ExprView Bool
    Divide :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    Modulo :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    Sum :: FreeSum (ExprView Integer) -> ExprView Integer
    Product :: FreeProduct (ExprView Integer) -> ExprView Integer
    Length :: ExprView String -> ExprView Integer
    GezInt :: ExprView Integer -> ExprView Bool
    Not :: ExprView Bool -> ExprView Bool
    And :: Set (ExprView Bool) -> ExprView Bool
    Concat :: [ExprView String] -> ExprView String
    -- NOTE: when adding more fields, check the Eq instance

type ExprConstraints t = (Data t, Eq t, Ord t, Show t, ExprType t, SymVal t, ConstType t, Read t)

instance Eq (ExprView t) where
  Var x == Var y = x == y
  Const x == Const y = x == y
  Ite c1 l1 r1 == Ite c2 l2 r2 = c1 == c2 && l1 == l2 && r1 == r2
  Equal t1 a b == Equal t2 x y
    | Just Refl <- t1 `geq` t2 = a == x && b == y
    | otherwise = False
  Divide a b == Divide x y = a == x && b == y
  Modulo a b == Modulo x y = a == x && b == y
  Sum x == Sum y = x == y
  Product x == Product y = x == y
  Length x == Length y = x == y
  GezInt x == GezInt y = x == y
  Not x == Not y = x == y
  And x == And y = x == y
  Concat x == Concat y = x == y
  _ == _ = False

instance Ord (ExprView t) where
  compare l r =
    case (l, r) of
      (Var a, Var b) -> compare a b
      (Const a, Const b) -> compare a b
      (Ite c1 l1 r1, Ite c2 l2 r2) ->
        compare (c1, l1, r1) (c2, l2, r2)
      (Equal t1 a b, Equal t2 x y) ->
        case gcompare t1 t2 of
          GLT -> LT
          GGT -> GT
          GEQ -> compare (a,b) (x,y)
      (Divide a b, Divide x y) ->
        compare (a, b) (x, y)
      (Modulo a b, Modulo x y) ->
        compare (a, b) (x, y)
      (Sum a, Sum b) ->
        compare a b
      (Product a, Product b) ->
        compare a b
      (Length a, Length b) ->
        compare a b
      (GezInt a, GezInt b) ->
        compare a b
      (Not a, Not b) ->
        compare a b
      (And a, And b) ->
        compare a b
      (Concat a, Concat b) ->
        compare a b
      _ ->
        compare (tag l) (tag r)
    where
      tag :: ExprView t -> Int
      tag = \case
        Var{}     -> 0
        Const{}   -> 1
        Ite{}     -> 2
        Equal{}   -> 3
        Divide{}  -> 4
        Modulo{}  -> 5
        Sum{}     -> 6
        Product{} -> 7
        Length{}  -> 8
        GezInt{}  -> 9
        Not{}     -> 10
        And{}     -> 11
        Concat{}  -> 12

instance Show (ExprView t) where
    show (Var v) = varName v
    show (Const c) = show c
    show (Ite cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (Divide e1 e2) = "(" ++ show e1 ++ ") / (" ++ show e2 ++ ")"
    show (Modulo e1 e2) = "(" ++ show e1 ++ ") % (" ++ show e2 ++ ")"
    show (Sum es) | es == mempty = "∑∅"
    show (Sum es) = "(" ++ showFreeMonoid "+" showSumTerm es ++ ")"
        where
        showSumTerm (-1)     t = "-" ++ t
        showSumTerm 1 t = t
        showSumTerm n t = show n ++ "⋅" ++ t
    show (Product es) | es == mempty = "∏∅"
    show (Product es) = showFreeMonoid "⋅" (\n t -> show n ++ "^" ++ t) es -- "(" ++ show e2 ++ ")" --FreeProduct Expr
    show (Length e) = "length(" ++ show e ++ ")"
    show (Equal _ e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (GezInt e) = "(" ++ show e ++ ") ≥ 0"
    show (Not e) = "¬(" ++ show e ++ ")"
    show (And (Set.toList -> [])) = "⋀∅"
    show (And (Set.toList -> es)) = List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$>  es
    show (Concat []) = "∑'∅"
    show (Concat es) = List.intercalate "++" $ (\e -> "(" ++ show e ++ ")") <$> es

showFreeMonoid :: Show a => String -> (Integer -> String -> String) -> FreeMonoidX a -> String
showFreeMonoid plusRepr multRepr (FMX p) = List.intercalate plusRepr $ showTerm <$> Map.assocs p
    where
    showTerm (x, i) = multRepr i (show x)


-- | Expr: value expression
-- Only 'view' is exported, not the constructor, to safeguard invariants.
newtype Expr t = Expr {view :: ExprView t} deriving (Eq, Ord)
-- TODO: which invariants?

instance Show (Expr t) where
    show = show . view

-- | Evaluate the provided value expression.
-- Either the Right Constant Value is returned or a (Left) error message.
eval :: Expr v -> Either String v
eval = evalView . view

evalView :: ExprView v -> Either String v
evalView (reduce -> Const v) = Right v
evalView _ = Left "Value Expression is not a constant value"

isConst :: ExprView v -> Bool
isConst (Const _) = True
isConst _ = False

reduce :: ExprView v -> ExprView v
reduce (Var v) = Var v
reduce (Const v) = Const v
reduce (Ite (reduce -> Const b) (reduce -> e1) (reduce -> e2)) = if b then e1 else e2
reduce (Ite (reduce -> c) (reduce -> e1) (reduce -> e2)) = Ite c e1 e2
reduce (Sum (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (Sum (mapFreeMonoidX reduce -> es)) = Sum es
reduce (Product (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (Product (mapFreeMonoidX reduce -> es)) = Product es
reduce (Modulo (reduce -> e1) (reduce -> e2@(Const 0))) = Modulo e1 e2 -- leave divisions by zero as expressions
reduce (Modulo (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x `mod` y
reduce (Modulo (reduce -> e1) (reduce -> e2)) = Modulo e1 e2
reduce (Divide (reduce -> e1) (reduce -> e2@(Const 0))) = Divide e1 e2 -- leave divisions by zero as expressions
reduce (Divide (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x `divInteger` y
reduce (Divide (reduce -> e1) (reduce -> e2)) = Divide e1 e2
reduce (Length (reduce -> (Const s))) = Const $ fromIntegral $ length s
reduce (Length (reduce -> e)) = Length e
reduce (Equal _ (reduce -> Const e1) (reduce -> Const e2)) = Const (e1 == e2)
reduce (Equal t (reduce -> e1) (reduce -> e2)) = Equal t e1 e2
reduce (GezInt (reduce -> (Const x))) = Const $ x >= 0
reduce (GezInt (reduce -> e)) = GezInt e
reduce (Not (reduce -> (Const b))) = Const $ not b
reduce (Not (reduce -> e)) = Not e
reduce (And (Set.map reduce -> es)) | all isConst es = Const $ and (Set.map constant es) -- TODO could be optimized further: if not all elements are constant, but if there are multiple constant elements, then the latter could still be combined
reduce (And (Set.map reduce -> es)) = And es
reduce (Concat (fmap reduce -> es)) | all isConst es = Const $ concatMap constant es -- TODO could be optimized further: if not all elements are constant, but if there are multiple successive constant elements, then the latter could still be combined
reduce (Concat (fmap reduce -> e)) = Concat e

-- ----------------------------------------------------------------------------------------- --
--
-- ----------------------------------------------------------------------------------------- --

freeVars :: Expr t -> Set.Set (Some Variable)
freeVars = Set.fromList . freeVars' . view

freeVars' :: ExprView t -> [Some Variable]
freeVars' (Var v) = [Some v]
freeVars' (Const _) = []
freeVars' (Ite cond e1 e2) = freeVars' cond ++ freeVars' e1 ++ freeVars' e2
freeVars' (Divide e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Modulo e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Sum (distinctTermsT -> es)) = concatMap freeVars' es
freeVars' (Product (distinctTermsT -> es)) = concatMap freeVars' es
freeVars' (Length e) = freeVars' e
freeVars' (Equal _ e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (GezInt e) = freeVars' e
freeVars' (Not e) = freeVars' e
freeVars' (And (Set.toList -> es)) = concatMap freeVars' es
freeVars' (Concat es) = concatMap freeVars' es

