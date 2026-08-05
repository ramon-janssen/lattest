{-# OPTIONS_HADDOCK hide, prune #-}
{-
This is a modified version of:
TorXakis - Model Based Testing
See LICENSE in the parent Symbolic folder.
-}
{-# LANGUAGE CPP #-}
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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Lattest.Model.Symbolic.Internal.ExprDefs
( ExprView(..)
, Expr(..)       -- for local usage only!
, eval
, reduce
, Variable(..)
, Type(..)
, Constant(Constant, CInt, CFloat, CBool, CString, CList, CTuple)
, constType
, constValue
, ConstType(..)
, ExprType
, typeOf
, typeOf'
, isConst
, freeVars
, ExprConstraints
, ToSBV
, List(..)
, withExprConstraints
, int
, float
, bool
, string
, list
, tuple
, toSBV
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

import Data.Scientific (fromFloatDigits)
import qualified Data.Scientific as DS
import qualified Data.Some.Church as Church
import Data.Some (Some(..))
import Data.GADT.Compare (GEq(..), GOrdering (..), GCompare (..))
import Data.Type.Equality ((:~:)(..))
import Data.GADT.Show (GRead (..), GShow (..), defaultGshowsPrec)
import Data.SBV (SymVal(..), HasKind)
import qualified Data.SBV.Internals as SBVI
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Data.EqP (EqP (..))
import Data.Maybe (isJust)
import Data.Constraint.Extras (Has (..))
import Data.Constraint.Compose (ComposeC)
import qualified Data.Vector as Vec
import Data.String (IsString(..))
import Control.Monad ((<=<))
import Data.Data (Data)
import Data.Bifunctor (Bifunctor(..))
import qualified Data.Aeson.Types as JSON

-- avoids overlapping with String in typeclass instances
newtype List a = List { getList :: [a] }
  deriving (Ord, Eq, Show, Read, Data, HasKind)
data Type a where
  IntType :: Type Integer
  FloatType :: Type Double
  BoolType :: Type Bool
  StringType :: Type String
  ListType :: Type a -> Type (List a)
  TupleType :: Type a -> Type b -> Type (a,b)
deriving instance Eq (Type a)
deriving instance Ord (Type a)
instance (SymVal a, ExprConstraints a) => SymVal (List a) where
  literal (List xs) = case literal xs of
    SBVI.SBV sval -> SBVI.SBV sval
  fromCV xs = List (fromCV xs)
#if MIN_VERSION_sbv(12,0,0)
  -- This field was added to SymVal in sbv-12.0, and the default instance requires Bounded (which a list is not)
  minMaxBound = Nothing
#endif
instance Arbitrary a => Arbitrary (List a) where
  arbitrary = List <$> arbitrary
instance EqP Type where
  eqp x y = isJust $ geq x y
instance GEq Type where
  geq IntType IntType = Just Refl
  geq FloatType FloatType = Just Refl
  geq BoolType BoolType = Just Refl
  geq StringType StringType = Just Refl
  geq (ListType a) (ListType b) = (\Refl -> Refl) <$> geq a b
  geq (TupleType a b) (TupleType x y) = (\Refl Refl -> Refl) <$> geq a x <*> geq b y
  geq _ _ = Nothing
instance GCompare Type where
  gcompare = \cases
    IntType IntType -> GEQ
    IntType _ -> GLT
    FloatType FloatType -> GEQ
    FloatType _ -> GLT
    BoolType BoolType -> GEQ
    BoolType _ -> GLT
    StringType StringType -> GEQ
    StringType _ -> GLT
    (ListType a) (ListType b) -> case gcompare a b of
      GGT -> GGT
      GLT -> GLT
      GEQ -> GEQ
    _ _ -> GGT
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
      ++ [ (Church.mkSome FloatType, rest)
         | ("Float", rest) <- lex s
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
      -- TODO test lists, make tuples

withExprConstraints :: Type x -> (ExprConstraints x => r) -> r
withExprConstraints t k = has @Data t $ has @Read t $ has @ConstType t $ has @Ord t $ has @Show t $ has @ExprType t $ has @SymValToSBV t $ has @EqToSBV t k

class Eq (ToSBV a) => EqToSBV a
instance Eq (ToSBV a) => EqToSBV a
class SymVal (ToSBV a) => SymValToSBV a
instance SymVal (ToSBV a) => SymValToSBV a

instance Has ExprType Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @ExprType t' k
    TupleType a b -> has @ExprType a $ has @ExprType b k

instance Has Eq Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Eq t' k
    TupleType a b -> has @Eq a $ has @Eq b k

instance Has Ord Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Ord t' k
    TupleType a b -> has @Ord a $ has @Ord b k

instance Has Show Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Show t' k
    TupleType a b -> has @Show a $ has @Show b k

instance Has Read Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Read t' k
    TupleType a b -> has @Read a $ has @Read b k

instance Has Data Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @Data t' k
    TupleType a b -> has @Data a $ has @Data b k

instance Has SymVal Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> withExprConstraints t' $ has @SymVal t' k
    TupleType a b -> has @SymVal a $ has @SymVal b k

instance Has EqToSBV Type where
  has IntType     k = k
  has FloatType   k = k
  has BoolType    k = k
  has StringType  k = k
  has (ListType t) k = has @EqToSBV t k
  has (TupleType a b) k =
    has @EqToSBV a $
    has @EqToSBV b k

instance Has SymValToSBV Type where
  has IntType     k = k
  has FloatType   k = k
  has BoolType    k = k
  has StringType  k = k
  has (ListType t) k = has @SymValToSBV t k
  has (TupleType a b) k =
    has @SymValToSBV a $
    has @SymValToSBV b k

class ExprType t where
    typeOf :: t -> Type t
    typeOf' :: f t -> Type t

instance ExprType Integer where
    typeOf _ = IntType
    typeOf' _ = IntType
instance ExprType Bool where
    typeOf _ = BoolType
    typeOf' _ = BoolType
instance ExprType Double where
    typeOf _ = FloatType
    typeOf' _ = FloatType
instance ExprType String where
    typeOf _ = StringType
    typeOf' _ = StringType
instance ExprType a => ExprType (List a) where
    typeOf _ = ListType $ typeOf undefined
    typeOf' _ = ListType $ typeOf undefined
instance (ExprType a, ExprType b) => ExprType (a,b) where
    typeOf _ = TupleType (typeOf undefined) (typeOf undefined)
    typeOf' _ = TupleType (typeOf undefined) (typeOf undefined)

instance Show (Type a) where
    show IntType = "Int"
    show BoolType = "Bool"
    show StringType = "String"
    show FloatType = "Float"
    show (ListType t) = "[" ++ show t ++ "]"
    show (TupleType a b) = "(" ++ show a ++ ", " ++ show b ++ ")"

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
  Constant :: { constType :: Type a , constValue :: a } -> Constant a
deriving instance Eq a => Eq (Constant a)
deriving instance Ord a => Ord (Constant a)
deriving instance Show a => Show (Constant a)
deriving instance (Read a, ExprType a) => Read (Constant a)

{-# COMPLETE CBool, CInt, CFloat, CString, CList, CTuple #-}
pattern CBool :: () => (a ~ Bool) => a -> Constant a
pattern CBool b = Constant BoolType b
pattern CInt :: () => (a ~ Integer) => a -> Constant a
pattern CInt i = Constant IntType i
pattern CFloat :: () => (a ~ Double) => a -> Constant a
pattern CFloat f = Constant FloatType f
pattern CString :: () => (a ~ String) => a -> Constant a
pattern CString s = Constant StringType s
pattern CList :: () => (xs ~ List x) => [x] -> Type x -> Constant xs
pattern CList xs t = (Constant (ListType t) (List xs))
pattern CTuple :: () => (ab ~ (a,b)) => a -> b -> Type a -> Type b -> Constant ab
pattern CTuple a b ta tb = (Constant (TupleType ta tb) (a,b))

int :: Integer -> Some Constant
int i = Some (CInt i)
bool :: Bool -> Some Constant
bool b = Some (CBool b)
float :: Double -> Some Constant
float f = Some (CFloat f)
string :: String -> Some Constant
string s = Some (CString s)
list :: ExprType a => [a] -> Some Constant
list xs = Some (CList xs (typeOf' xs))
tuple :: (ExprType a, ExprType b) => a -> b -> Some Constant
tuple a b = Some (CTuple a b (typeOf a) (typeOf b))

instance GEq Constant where
  a `geq` b = case constType a `geq` constType b of
    Just Refl -> if has @Eq (constType a) $ constValue a == constValue b then Just Refl else Nothing
    Nothing -> Nothing
instance GCompare Constant where
  gcompare a b = case gcompare (constType a) (constType b) of
    GLT -> GLT
    GGT -> GGT
    GEQ -> case has @Ord a $ compare a b of
      LT -> GLT
      GT -> GGT
      EQ -> GEQ

instance GShow Constant where
  gshowsPrec i c = has @Show c $ defaultGshowsPrec i c
instance GRead Constant where
  greadsPrec _ =
    readParen False $ \s -> do
    ("Constant", s1) <- lex s
    (tp', s2) <- greadsPrec 11 s1
    Church.withSome tp' $ \tp -> do
      (x, rest) <- has @Read tp $ readsPrec 11 s2
      return (Church.mkSome (Constant tp x), rest)

instance Has c Type => Has c Constant where
  has (Constant t _) = has @c t

instance JSON.FromJSON (Some Constant) where
    parseJSON (JSON.Object m)
        | not $ JSON.member "value" m = fail "expected Constant with a value field"
        | not $ JSON.member "type" m = fail "expected Constant with a type field"
    parseJSON (JSON.Object m)
        | Just val <- JSON.lookup "type" m = parseType val >>= \case
            Some BoolType -> parseBool $ lkup "value" m
            Some IntType -> parseInt $ lkup "value" m
            Some FloatType -> parseFloat $ lkup "value" m
            Some StringType -> parseString $ lkup "value" m
            Some (ListType t) -> parseList t $ lkup "value" m
            Some (TupleType a b) -> parseTuple a b $ lkup "value" m
        where
        parseType (JSON.String (Text.unpack -> s)) = case s of
          "string" -> pure $ Some StringType
          "int" -> pure $ Some IntType
          "float" -> pure $ Some FloatType
          "bool" -> pure $ Some BoolType
          '[':(init -> cs) -> (\(Some t) -> Some $ ListType t) <$> parseType (JSON.String (Text.pack cs))
          '(':(parseTupleType 0 . init -> (a,b))
            -> (\(Some a') (Some b') -> Some $ TupleType a' b')
                      <$> parseType (JSON.String (Text.pack a))
                      <*> parseType (JSON.String (Text.pack b))
          _ -> fail $ "bad type: " <> s
        parseType _ = fail "type is not a string"
        -- splits the string at the first comma that isn't part of a new tuple
        -- inefficient, but simple, and types should never be complicated
        parseTupleType :: Int -> String -> (String, String)
        parseTupleType 0 (',':xs) = ("",xs)
        parseTupleType n ('(':xs) = first ('(':) $ parseTupleType (n+1) xs
        parseTupleType n (')':xs) = first (')':) $ parseTupleType (n-1) xs
        parseTupleType n (x:xs)   = first (x:) $ parseTupleType n xs
        parseTupleType _ [] = error "comma not found in tuple"
        lkup :: JSON.Key -> JSON.KeyMap v -> v
        lkup k = Maybe.fromJust . JSON.lookup k
        parseBool (JSON.Bool b) = return $ bool b
        parseBool _ = fail "type indicates bool, but value is not of type bool"
        parseInt (JSON.Number (DS.floatingOrInteger @Double -> Right i)) = return $ int i
        parseInt _ = fail "type indicates int, but value is not of type int"
        parseString (JSON.String s) = return $ string $ Text.unpack s
        parseString _ = fail "type indicates string, but value is not of type string"
        parseFloat (JSON.Number (DS.toRealFloat -> f)) = return $ float f
        parseFloat _ = fail "type indicates float, but value is not of type float"
        parseList t (JSON.Array xs) = has @ExprType t list <$> mapM (unSome t <=< JSON.parseJSON @(Some Constant)) (Vec.toList xs)
          where
            unSome :: Type a -> Some Constant -> JSON.Parser a
            unSome tp (Some (Constant tp' v)) = case tp' `geq` tp of
              Nothing -> fail $ "type indicates list of " <> show tp <> ", but at least one element was a " <> show tp'
              Just Refl -> pure v
        parseList _ _ = fail "type indicates list, but value is not of type array"
        parseTuple :: Type a -> Type b -> JSON.Value -> JSON.Parser (Some Constant)
        parseTuple a b (JSON.Object m')
          | Just x <- JSON.lookup "left" m'
          , Just y <- JSON.lookup "right" m'
          = do
          Some (Constant xt xv) <- JSON.parseJSON x
          Some (Constant yt yv) <- JSON.parseJSON y
          case a `geq` xt of
            Nothing -> fail "type of left element of tuple doesn't match"
            Just Refl -> case b `geq` yt of
              Nothing -> fail "type of right element of tuple doesn't match"
              Just Refl -> has @ExprType xt $ has @ExprType yt $ return $ tuple xv yv
        parseTuple _ _ _ = fail "type indicates pair, but value is not of type object"
    parseJSON _ = fail "expected Constant JSON"

instance JSON.ToJSON (Some Constant) where
    toJSON (Some v) = case v of
      CBool b -> JSON.Object $ JSON.insert "type" "bool" $ JSON.insert "value" (JSON.Bool b) JSON.empty
      CInt i -> JSON.Object $ JSON.insert "type" "int" $ JSON.insert "value" (JSON.Number $ fromInteger i) JSON.empty
      CFloat f -> JSON.Object $ JSON.insert "type" "float" $ JSON.insert "value" (JSON.Number $ fromFloatDigits f) JSON.empty
      CString s -> JSON.Object $ JSON.insert "type" "string" $ JSON.insert "value" (JSON.String $ Text.pack s) JSON.empty
      CList xs t -> JSON.Object
        $ JSON.insert "type" (fromString . showtype $ ListType t)
        $ JSON.insert "value" (JSON.Array $ Vec.fromList $ map (JSON.toJSON . Some . Constant t) xs)
        JSON.empty
      CTuple x y a b -> JSON.Object
        $ JSON.insert "type" (fromString . showtype $ TupleType a b)
        $ JSON.insert "value" (JSON.Object $ JSON.insert "left" (JSON.toJSON . Some $ Constant a x) $ JSON.insert "right" (JSON.toJSON . Some $ Constant b y) JSON.empty)
        JSON.empty
      where
        showtype :: Type a -> String
        showtype BoolType = "bool"
        showtype IntType = "int"
        showtype FloatType = "float"
        showtype StringType = "string"
        showtype (ListType tp) = "[" <> showtype tp <> "]"
        showtype (TupleType a b) = "(" <> showtype a <> "," <> showtype b <> ")"

-- | convert a Constant to an typed value
class ExprType t => ConstType t where
    fromConst :: Constant t -> t
    toConst :: t -> Constant t

instance ExprType a => ConstType a where
  fromConst (Constant _ x) = x
  toConst x = Constant (typeOf x) x

instance Has ConstType Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    BoolType -> k
    StringType -> k
    ListType t' -> has @ConstType t' k
    TupleType a b -> has @ConstType a $ has @ConstType b k

-- ----------------------------------------------------------------------------------------- --
-- value expression

data ExprView t where
    Var :: {variable :: Variable t} -> ExprView t
    Const :: ExprConstraints t => {constant :: t} -> ExprView t
    Ite :: {conditional :: ExprView Bool, trueBranch :: ExprView t, falseBranch :: ExprView t} -> ExprView t
    Equal :: ExprConstraints t => {eqType :: Type t, left :: ExprView t, right :: ExprView t} -> ExprView Bool
    Divide :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    Modulo :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    DivideFloat :: {dividendF :: ExprView Double, divisorF :: ExprView Double} -> ExprView Double
    Sum :: FreeSum (ExprView Integer) -> ExprView Integer
    SumFloat :: FreeSum (ExprView Double) -> ExprView Double
    Product :: FreeProduct (ExprView Integer) -> ExprView Integer
    ProductFloat :: FreeProduct (ExprView Double) -> ExprView Double
    StrLength :: ExprView String -> ExprView Integer
    GezInt :: ExprView Integer -> ExprView Bool
    GezFloat :: ExprView Double -> ExprView Bool
    Not :: ExprView Bool -> ExprView Bool
    And :: Set (ExprView Bool) -> ExprView Bool
    Concat :: [ExprView String] -> ExprView String
    Cons :: ExprView x -> ExprView (List x) -> ExprView (List x)
    Append :: ExprView (List a) -> ExprView (List a) -> ExprView (List a)
    Length :: Type a -> ExprView (List a) -> ExprView Integer
    LElem :: Type a -> ExprView a -> ExprView (List a) -> ExprView Bool
    Take :: ExprView Integer -> ExprView (List a) -> ExprView (List a)
    Drop :: ExprView Integer -> ExprView (List a) -> ExprView (List a)
    -- TODO: 'map' needs a function type
    -- NOTE: when adding more fields, check the Eq instance

type ExprConstraints t = (Data t, Eq t, Ord t, Show t, ExprType t, SymVal (ToSBV t), Eq (ToSBV t), ConstType t, Read t)

type family ToSBV a where
  ToSBV (List a) = [ToSBV a]
  ToSBV (a,b) = (ToSBV a, ToSBV b)
  ToSBV a = a

toSBV :: Type a -> a -> ToSBV a
toSBV t x = case t of
  ListType t' -> let List xs = x in map (toSBV t') xs
  TupleType at bt -> bimap (toSBV at) (toSBV bt) x
  IntType -> x
  FloatType -> x
  BoolType -> x
  StringType -> x

instance Eq (ExprView t) where
  Var x == Var y = x == y
  Const x == Const y = x == y
  Ite c1 l1 r1 == Ite c2 l2 r2 = c1 == c2 && l1 == l2 && r1 == r2
  Equal t1 a b == Equal t2 x y
    | Just Refl <- t1 `geq` t2 = a == x && b == y
    | otherwise = False
  Divide a b == Divide x y = a == x && b == y
  DivideFloat a b == DivideFloat x y = a == x && b == y
  Modulo a b == Modulo x y = a == x && b == y
  Sum x == Sum y = x == y
  SumFloat x == SumFloat y = x == y
  Product x == Product y = x == y
  ProductFloat x == ProductFloat y = x == y
  StrLength x == StrLength y = x == y
  Length a x == Length b y
    | Just Refl <- a `geq` b = x == y
  GezInt x == GezInt y = x == y
  GezFloat x == GezFloat y = x == y
  Not x == Not y = x == y
  And x == And y = x == y
  Concat x == Concat y = x == y
  Cons x xs == Cons y ys = x == y && xs == ys
  Append x xs == Append y ys = x == y && xs == ys
  LElem t1 x y == LElem t2 a b
    | Just Refl <- t1 `geq` t2 = x == a && y == b
    | otherwise = False
  Take x xs == Take y ys = x == y && xs == ys
  Drop x xs == Drop y ys = x == y && xs == ys
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
      (DivideFloat a b, DivideFloat x y) ->
        compare (a, b) (x, y)
      (Modulo a b, Modulo x y) ->
        compare (a, b) (x, y)
      (Sum a, Sum b) ->
        compare a b
      (SumFloat a, SumFloat b) ->
        compare a b
      (Product a, Product b) ->
        compare a b
      (ProductFloat a, ProductFloat b) ->
        compare a b
      (StrLength a, StrLength b) ->
        compare a b
      (Length a x, Length b y) -> case gcompare a b of
        GLT -> LT
        GGT -> GT
        GEQ -> compare x y
      (GezInt a, GezInt b) ->
        compare a b
      (GezFloat a, GezFloat b) ->
        compare a b
      (Not a, Not b) ->
        compare a b
      (And a, And b) ->
        compare a b
      (Concat a, Concat b) ->
        compare a b
      (Cons x xs, Cons y ys) ->
        compare (x,xs) (y,ys)
      (Append as bs, Append xs ys) ->
        compare (as,bs) (xs,ys)
      (LElem t1 x xs, LElem t2 y ys) ->
        case gcompare t1 t2 of
          GLT -> LT
          GGT -> GT
          GEQ -> compare (x,xs) (y,ys)
      (Take i xs, Take j ys) ->
        compare (i,xs) (j,ys)
      (Drop i xs, Drop j ys) ->
        compare (i,xs) (j,ys)
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
        Cons{}    -> 13
        Append{}  -> 14
        LElem{}   -> 15
        Take{}    -> 16
        Drop{}    -> 17
        DivideFloat{} -> 18
        SumFloat{} -> 19
        ProductFloat{} -> 20
        GezFloat{} -> 21
        StrLength{} -> 22


instance Show (ExprView t) where
    show (Var v) = varName v
    show (Const c) = show c
    show (Ite cond e1 e2) = "if (" ++ show cond ++ ") then (" ++ show e1 ++ ") else (" ++ show e2 ++ ")"
    show (Divide e1 e2) = "(" ++ show e1 ++ ") / (" ++ show e2 ++ ")"
    show (Modulo e1 e2) = "(" ++ show e1 ++ ") % (" ++ show e2 ++ ")"
    show (DivideFloat e1 e2) = "(" ++ show e1 ++ ") / (" ++ show e2 ++ ")"
    show (Sum es) | es == mempty = "∑∅"
    show (Sum es) = "(" ++ showFreeMonoid "+" showSumTerm es ++ ")"
        where
        showSumTerm (-1)     t = "-" ++ t
        showSumTerm 1 t = t
        showSumTerm n t = show n ++ "⋅" ++ t
    show (Product es) | es == mempty = "∏∅"
    show (Product es) = showFreeMonoid "⋅" (\n t -> show n ++ "^" ++ t) es -- "(" ++ show e2 ++ ")" --FreeProduct Expr
    show (SumFloat es) | es == mempty = "∑∅"
    show (SumFloat es) = "(" ++ showFreeMonoid "+" showSumTerm es ++ ")"
        where
        showSumTerm (-1)     t = "-" ++ t
        showSumTerm 1 t = t
        showSumTerm n t = show n ++ "⋅" ++ t
    show (ProductFloat es) | es == mempty = "∏∅"
    show (ProductFloat es) = showFreeMonoid "⋅" (\n t -> show n ++ "^" ++ t) es
    show (StrLength e) = "length(" ++ show e ++ ")"
    show (Length _ e) = "length(" ++ show e ++ ")"
    show (Equal _ e1 e2) = "(" ++ show e1 ++ ") = (" ++ show e2 ++ ")"
    show (GezInt e) = "(" ++ show e ++ ") ≥ 0"
    show (GezFloat e) = "(" ++ show e ++ ") ≥ 0"
    show (Not e) = "¬(" ++ show e ++ ")"
    show (And (Set.toList -> [])) = "⋀∅"
    show (And (Set.toList -> es)) = List.intercalate "∧" $ (\e -> "(" ++ show e ++ ")") <$>  es
    show (Concat []) = "∑'∅"
    show (Concat es) = List.intercalate "++" $ (\e -> "(" ++ show e ++ ")") <$> es
    show (Cons x xs) = show x ++ ":" ++ show xs
    show (Append xs ys) = show xs ++ "++" ++ show ys
    show (LElem _ x xs) = show x ++ "`elem`" ++ show xs
    show (Take i xs) = "take " ++ show i ++ " " ++ show xs
    show (Drop i xs) = "drop " ++ show i ++ " " ++ show xs

instance Has ExprType ExprView where
  has e k = case e of
    Var v -> has @ExprType (varType v) k
    Const _ -> k
    Ite _ x _ -> has @ExprType x k
    Equal t _ _ -> has @ExprType t k
    Divide _ _ -> k
    DivideFloat _ _ -> k
    Modulo _ _ -> k
    Sum _ -> k
    SumFloat _ -> k
    Product _ -> k
    ProductFloat _ -> k
    StrLength _ -> k
    Length t _ -> has @ExprType t k
    GezInt _ -> k
    GezFloat _ -> k
    Not _ -> k
    And _ -> k
    Concat _ -> k
    Cons _ x -> has @ExprType x k
    Append _ x -> has @ExprType x k
    LElem t _ _ -> has @ExprType t k
    Take _ x -> has @ExprType x k
    Drop _ x -> has @ExprType x k

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
reduce (SumFloat (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (SumFloat (mapFreeMonoidX reduce -> es)) = SumFloat es
reduce (Product (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (Product (mapFreeMonoidX reduce -> es)) = Product es
reduce (ProductFloat (mapFreeMonoidX reduce -> es)) | allFreeMonoidX isConst es = Const $ FMX.fold $ mapFreeMonoidX constant es
reduce (ProductFloat (mapFreeMonoidX reduce -> es)) = ProductFloat es
reduce (Modulo (reduce -> e1) (reduce -> e2@(Const 0))) = Modulo e1 e2 -- leave divisions by zero as expressions
reduce (Modulo (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x `mod` y
reduce (Modulo (reduce -> e1) (reduce -> e2)) = Modulo e1 e2
reduce (Divide (reduce -> e1) (reduce -> e2@(Const 0))) = Divide e1 e2 -- leave divisions by zero as expressions
reduce (Divide (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x `divInteger` y
reduce (Divide (reduce -> e1) (reduce -> e2)) = Divide e1 e2
reduce (DivideFloat (reduce -> e1) (reduce -> e2@(Const 0))) = DivideFloat e1 e2 -- leave divisions by zero as expressions
reduce (DivideFloat (reduce -> (Const x)) (reduce -> (Const y))) = Const $ x / y
reduce (DivideFloat (reduce -> e1) (reduce -> e2)) = DivideFloat e1 e2
reduce (StrLength (reduce -> (Const s))) = Const $ fromIntegral $ length s
reduce (StrLength (reduce -> e)) = StrLength e
reduce (Length _ (reduce -> Const (List xs))) = Const $ fromIntegral $ length xs
reduce (Length t (reduce -> e)) = Length t e
reduce (Equal _ (reduce -> Const e1) (reduce -> Const e2)) = Const (e1 == e2)
reduce (Equal t (reduce -> e1) (reduce -> e2)) = Equal t e1 e2
reduce (GezInt (reduce -> (Const x))) = Const $ x >= 0
reduce (GezInt (reduce -> e)) = GezInt e
reduce (GezFloat (reduce -> (Const x))) = Const $ x >= 0
reduce (GezFloat (reduce -> e)) = GezFloat e
reduce (Not (reduce -> (Const b))) = Const $ not b
reduce (Not (reduce -> e)) = Not e
reduce (And (Set.map reduce -> es)) | all isConst es = Const $ and (Set.map constant es) -- TODO could be optimized further: if not all elements are constant, but if there are multiple constant elements, then the latter could still be combined
reduce (And (Set.map reduce -> es)) = And es
reduce (Concat (fmap reduce -> es)) | all isConst es = Const $ concatMap constant es -- TODO could be optimized further: if not all elements are constant, but if there are multiple successive constant elements, then the latter could still be combined
reduce (Concat (fmap reduce -> e)) = Concat e
reduce (Cons (reduce -> x) (reduce -> xs))
  | Const a <- x
  , Const (List as) <- xs = Const $ List $ a : as
  | otherwise = Cons x xs
reduce (Append (reduce -> xs) (reduce -> ys))
  | Const (List as) <- xs
  , Const (List bs) <- ys = Const $ List $ as ++ bs
  | otherwise = Append xs ys
reduce (LElem t (reduce -> x) (reduce -> xs))
  | Const a <- x
  , Const (List as) <- xs = Const $ a `elem` as
  | otherwise = LElem t x xs
reduce (Take (reduce -> i) (reduce -> xs))
  | Const j <- i
  , Const (List as) <- xs = Const $ List $ take (fromInteger j) as
  | otherwise = Take i xs
reduce (Drop (reduce -> i) (reduce -> xs))
  | Const j <- i
  , Const (List as) <- xs = Const $ List $ drop (fromInteger j) as
  | otherwise = Drop i xs

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
freeVars' (DivideFloat e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Sum (distinctTermsT -> es)) = concatMap freeVars' es
freeVars' (SumFloat (distinctTermsT -> es)) = concatMap freeVars' es
freeVars' (Product (distinctTermsT -> es)) = concatMap freeVars' es
freeVars' (ProductFloat (distinctTermsT -> es)) = concatMap freeVars' es
freeVars' (Length _ e) = freeVars' e
freeVars' (StrLength e) = freeVars' e
freeVars' (Equal _ e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (GezInt e) = freeVars' e
freeVars' (GezFloat e) = freeVars' e
freeVars' (Not e) = freeVars' e
freeVars' (And (Set.toList -> es)) = concatMap freeVars' es
freeVars' (Concat es) = concatMap freeVars' es
freeVars' (Cons e es) = freeVars' e ++ freeVars' es
freeVars' (Append e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (LElem _ e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Take e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Drop e1 e2) = freeVars' e1 ++ freeVars' e2

