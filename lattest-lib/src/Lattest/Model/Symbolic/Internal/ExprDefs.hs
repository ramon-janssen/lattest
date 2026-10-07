{-# OPTIONS_HADDOCK hide, prune #-}
{-
This is a modified version of:
TorXakis - Model Based Testing
See LICENSE in the parent Symbolic folder.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{- HLINT ignore "Use typeRep" -}

module Lattest.Model.Symbolic.Internal.ExprDefs
( ExprView(..)
, Expr(..)       -- for local usage only!
, Variable(..)
, Type(..)
, Constant(Constant, CInt, CFloat, CRational, CReal, CUnit, CBool, CString, CList, CTuple, CSet, CSum, CChar)
, constType
, constValue
, ConstType(..)
, ExprType
, typeOf
, typeOf'
, isConst
, freeVars
, freeVars'
, ExprConstraints
, withExprConstraints
, withExprNumConstraint
, int
, unit
, float
, rational
, real
, bool
, char
, string
, list
, set
, tuple
, option
, inhabitants
, enumIndex
, prettyValue
, prettyConstant
)
where

import qualified Data.List as List
import           Data.Set         (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Text as Text(pack, unpack)

import           Lattest.Model.Symbolic.Internal.FreeMonoidX
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
import Data.SBV (SymVal(..), RCSet (..), SBV, OrdSymbolic (..), sFalse, SBool, sNot, (.&&), AlgReal)
import Data.EqP (EqP (..))
import Data.Maybe (isJust, maybeToList)
import Data.Constraint.Extras (Has (..))
import Data.Constraint.Compose (ComposeC)
import qualified Data.Vector as Vec
import Data.String (IsString(..))
import Control.Monad ((<=<))
import Data.Data (Data)
import Data.Bifunctor (Bifunctor(..))
import qualified Data.Aeson.Types as JSON
import Data.List (stripPrefix)

data Type a where
  IntType :: Type Integer
  FloatType :: Type Double
  RationalType :: Type Rational
  RealType :: Type AlgReal
  BoolType :: Type Bool
  CharType :: Type Char
  UnitType :: Type ()
  ListType :: Type a -> Type [a]
  SetType :: Type a -> Type (RCSet a)
  TupleType :: Type a -> Type b -> Type (a,b)
  SumType :: Type a -> Type b -> Type (Either a b)

deriving instance Eq (Type a)
deriving instance Ord (Type a)
instance EqP Type where
  eqp x y = isJust $ geq x y
instance GEq Type where
  geq IntType IntType = Just Refl
  geq FloatType FloatType = Just Refl
  geq RationalType RationalType = Just Refl
  geq RealType RealType = Just Refl
  geq BoolType BoolType = Just Refl
  geq CharType CharType = Just Refl
  geq UnitType UnitType = Just Refl
  geq (ListType a) (ListType b) = (\Refl -> Refl) <$> geq a b
  geq (SetType a) (SetType b) = (\Refl -> Refl) <$> geq a b
  geq (TupleType a b) (TupleType x y) = (\Refl Refl -> Refl) <$> geq a x <*> geq b y
  geq (SumType a b) (SumType x y) = (\Refl Refl -> Refl) <$> geq a x <*> geq b y
  geq _ _ = Nothing
instance GCompare Type where
  gcompare a b = case (a, b) of
    (ListType a', ListType b')   -> case gcompare a' b' of
      GLT -> GLT
      GEQ -> GEQ
      GGT -> GGT
    (SetType a', SetType b')     -> case gcompare a' b' of
      GLT -> GLT
      GEQ -> GEQ
      GGT -> GGT
    (TupleType a1 b1, TupleType a2 b2) -> case gcompare a1 a2 of
      GLT -> GLT
      GEQ -> case gcompare b1 b2 of
        GLT -> GLT
        GEQ -> GEQ
        GGT -> GGT
      GGT -> GGT
    (SumType a1 b1, SumType a2 b2) -> case gcompare a1 a2 of
      GLT -> GLT
      GEQ -> case gcompare b1 b2 of
        GLT -> GLT
        GEQ -> GEQ
        GGT -> GGT
      GGT -> GGT
    _ -> case compare (typeTag a) (typeTag b) of
        LT -> GLT
        EQ -> case a `geq` b of
          Just Refl -> GEQ
          Nothing -> error "tags match but geq doesn't; forgot to add a new type to gcompare or geq?"
        GT -> GGT
    where
      -- NOTE: when adding a new recursive case below, make sure to add it above too!
      typeTag :: Type a -> Int
      typeTag IntType    = 0
      typeTag FloatType  = 1
      typeTag BoolType   = 2
      typeTag CharType   = 3
      typeTag UnitType   = 4
      typeTag (ListType _)   = 5
      typeTag (SetType _)    = 6
      typeTag (TupleType _ _) = 7
      typeTag (SumType _ _)   = 8
      typeTag RationalType = 9
      typeTag RealType = 10

instance Show (Type a) where
    show IntType = "Int"
    show UnitType = "()"
    show BoolType = "Bool"
    show CharType = "Char"
    show FloatType = "Float"
    show RationalType = "Rational"
    show RealType = "Real"
    show (ListType t) = "[" ++ show t ++ "]"
    show (SetType t) = "{" ++ show t ++ "}"
    show (TupleType a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (SumType a b) = "<" ++ show a ++ ", " ++ show b ++ ">"
instance GShow Type where
  gshowsPrec = defaultGshowsPrec

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
         [ (Church.mkSome CharType, rest)
         | rest <- mylex "Char" s
         ]
      ++ [ (Church.mkSome IntType, rest)
         | rest <- mylex "Int" s
         ]
      ++ [ (Church.mkSome FloatType, rest)
         | rest <- mylex "Float" s
         ]
      ++ [ (Church.mkSome RationalType, rest)
         | rest <- mylex "Rational" s
         ]
      ++ [ (Church.mkSome RealType, rest)
         | rest <- mylex "Real" s
         ]
      ++ [ (Church.mkSome BoolType, rest)
         | rest <- mylex "Bool" s
         ]
      ++ [ (Church.mkSome UnitType, rest)
         | rest <- mylex "()" s
         ]
      ++ do
          s1 <- mylex "[" s
          (t, s2) <- greadsPrec 11 s1
          rest <- mylex "]" s2
          Church.withSome t $ \(tp :: Type t) ->
            return (Church.mkSome $ ListType tp, rest)
      ++ do
          s1 <- mylex "{" s
          (t, s2) <- greadsPrec 11 s1
          rest <- mylex "}" s2
          Church.withSome t $ \(tp :: Type t) ->
            return (Church.mkSome $ SetType tp, rest)
      ++ do
          s1 <- mylex "(" s
          (a, s2) <- greadsPrec 11 s1
          s3 <- mylex ", " s2
          (b, s4) <- greadsPrec 11 s3
          rest <- mylex ")" s4
          Church.withSome a $ \(ta :: Type a) ->
            Church.withSome b $ \(tb :: Type b) ->
              return (Church.mkSome $ TupleType ta tb, rest)
      ++ do
          s1 <- mylex "<" s
          (a, s2) <- greadsPrec 11 s1
          s3 <- mylex ", " s2
          (b, s4) <- greadsPrec 11 s3
          rest <- mylex ">" s4
          Church.withSome a $ \(ta :: Type a) ->
            Church.withSome b $ \(tb :: Type b) ->
              return (Church.mkSome $ SumType ta tb, rest)
    where
      mylex prefix = maybeToList . stripPrefix prefix

instance ExprType a => Eq (RCSet a) where
  a == b = withExprConstraints (typeOf' a) $ case a of
    RegularSet as -> case b of
      RegularSet bs -> as == bs
      ComplementSet bs -> case typeOf' a of
        SetType x -> case inhabitants x of
          Nothing -> False -- infinitely large complement
          Just i -> Set.size as + Set.size bs == i && Set.intersection as bs == mempty
        _ -> error "not a set"
    ComplementSet as -> case b of
      RegularSet bs -> case typeOf' a of
        SetType x -> case inhabitants x of
          Nothing -> False -- infinitely large complement
          Just i -> Set.size as + Set.size bs == i && Set.intersection as bs == mempty
        _ -> error "not a set"
      ComplementSet bs -> as == bs
instance ExprType a => Ord (RCSet a) where
  -- To ensure transitivity, we choose a < b iff size a < size b, where the size of a complement shrinks as the embedded set grows
  compare a b = withExprConstraints (typeOf' a) $ case a of
    RegularSet as -> case b of
      RegularSet bs -> case compare (Set.size as) (Set.size bs) of
        EQ -> compare as bs
        x -> x
      ComplementSet bs -> case typeOf' a of
        SetType x -> case inhabitants x of
          Just i
           | Set.size as + Set.size bs == i && Set.intersection as bs == mempty
           -> EQ
          _ -> LT -- the size of the complementset is infinite
        _ -> error "not a set"
    ComplementSet as -> case b of
      RegularSet bs -> case typeOf' a of
        SetType x -> case inhabitants x of
          Just i
           | Set.size as + Set.size bs == i && Set.intersection as bs == mempty
           -> EQ
          _ -> GT -- the size of the complementset is infinite
        _ -> error "not a set"
      -- flipping as and bs when comparing two complements
      ComplementSet bs -> case compare (Set.size bs) (Set.size as) of
        EQ -> compare bs as
        x -> x
-- count the inhabitants of a type; to define Eq and Ord instances for RCSet, and to compute the size of a complementset
inhabitants :: forall e. Type e -> Maybe Int
inhabitants = \case
  IntType -> Nothing
  FloatType -> Nothing
  RationalType -> Nothing
  RealType -> Nothing
  BoolType -> Just 2
  CharType -> Nothing -- maxBound - minBound + 1 = 1114112, I think we'd have overflow issues (in e.g. sums/products of chars) more often than that we'd have such large complement sets
  ListType _ -> Nothing
  SetType _ -> Nothing
  TupleType x y -> (*) <$> inhabitants x <*> inhabitants y
  SumType x y -> (+) <$> inhabitants x <*> inhabitants y
  UnitType -> Just 1

instance (Ord a, Read a) => Read (RCSet a) where
  readsPrec _ str =
    (first RegularSet <$> readSet str)
    <> case str of
          'U':' ':'-':' ':rest -> first ComplementSet <$> readSet rest
          'U':rest -> [(ComplementSet mempty, rest)]
          _ -> []

readSet :: forall a. (Ord a, Read a) => ReadS (Set a)
readSet ('{':s) = go [] s
  where
    go xs ('}':rest) = [(Set.fromList xs, rest)]
    go xs str = do
      (x, ',':str') <- reads str
      go (x:xs) str'
readSet _ = []

withExprConstraints :: Has ExprType f => f a -> (ExprConstraints a => r) -> r
withExprConstraints f k = let t = has @ExprType f (typeOf' f) in has @Data t $ has @Read t $ has @ConstType t $ has @Ord t $ has @Show t $ has @ExprType t $ has @SymVal t $ has @Eq t $ hasOrdSymbolic t k

withExprNumConstraint :: (Has ExprType f, Num a) => f a -> (Num (SBV a) => r) -> r
withExprNumConstraint f k = case has @ExprType f (typeOf' f) of
  IntType -> k
  FloatType -> k
  RationalType -> k
  RealType -> k
  _ -> error "impossible Num instance"

instance Has ExprType Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    RationalType -> k
    RealType -> k
    BoolType -> k
    UnitType -> k
    CharType -> k
    ListType t' -> has @ExprType t' k
    SetType t' -> has @ExprType t' k
    TupleType a b -> has @ExprType a $ has @ExprType b k
    SumType a b -> has @ExprType a $ has @ExprType b k

instance Has Eq Type where
  has t k = case t of
    IntType -> k
    UnitType -> k
    FloatType -> k
    RationalType -> k
    RealType -> k
    BoolType -> k
    CharType -> k
    ListType t' -> has @Eq t' k
    SetType t' -> withExprConstraints t' k
    TupleType a b -> has @Eq a $ has @Eq b k
    SumType a b -> has @Eq a $ has @Eq b k

instance Has Ord Type where
  has t k = case t of
    IntType -> k
    UnitType -> k
    FloatType -> k
    RationalType -> k
    RealType -> k
    BoolType -> k
    CharType -> k
    ListType t' -> has @Ord t' k
    SetType t' -> withExprConstraints t' k
    TupleType a b -> has @Ord a $ has @Ord b k
    SumType a b -> has @Ord a $ has @Ord b k

hasOrdSymbolic :: Type a -> (OrdSymbolic (SBV a) => r) -> r
hasOrdSymbolic t k = case t of
  IntType -> k
  FloatType -> k
  RationalType -> k
  RealType -> k
  CharType -> k
  UnitType -> k
  BoolType -> k
  ListType t' -> has @SymVal t' k
  SetType _ -> error "TODO: implement ordsymbolic for sets (or delete RCSets)"
  TupleType a b -> has @SymVal a $ has @SymVal b k
  SumType a b -> has @SymVal a $ has @SymVal b $ hasOrdSymbolic a $ hasOrdSymbolic b k
instance OrdSymbolic (SBV ()) where
  (.<) _ _ = sFalse
instance OrdSymbolic SBool where
  x .< y = y .&& sNot x

instance Has Show Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    RationalType -> k
    RealType -> k
    BoolType -> k
    UnitType -> k
    CharType -> k
    ListType t' -> has @Show t' k
    SetType t' -> has @Show t' k
    TupleType a b -> has @Show a $ has @Show b k
    SumType a b -> has @Show a $ has @Show b k

instance Has SymVal Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    RationalType -> k
    RealType -> k
    BoolType -> k
    UnitType -> k
    CharType -> k
    ListType t' -> has @SymVal t' k
    SetType t' -> has @SymVal t' $ has @Ord t' k
    TupleType a b -> has @SymVal a $ has @SymVal b k
    SumType a b -> has @SymVal a $ has @SymVal b k

instance Has Read Type where
  has t k = case t of
    IntType -> k
    FloatType -> k
    RationalType -> k
    RealType -> k
    UnitType -> k
    BoolType -> k
    CharType -> k
    ListType t' -> has @Read t' k
    SetType t' -> has @Ord t' $ has @Read t' k
    TupleType a b -> has @Read a $ has @Read b k
    SumType a b -> has @Read a $ has @Read b k

instance Read AlgReal where
  readsPrec = error "TODO"

instance Has Data Type where
  has t k = case t of
    IntType -> k
    UnitType -> k
    FloatType -> k
    RationalType -> k
    RealType -> k
    BoolType -> k
    CharType -> k
    ListType t' -> has @Data t' k
    SetType t' -> has @Data t' $ has @Ord t' k
    TupleType a b -> has @Data a $ has @Data b k
    SumType a b -> has @Data a $ has @Data b k

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
instance ExprType Rational where
    typeOf _ = RationalType
    typeOf' _ = RationalType
instance ExprType AlgReal where
    typeOf _ = RealType
    typeOf' _ = RealType
instance ExprType Char where
    typeOf _ = CharType
    typeOf' _ = CharType
instance ExprType a => ExprType [a] where
    typeOf _ = ListType $ typeOf undefined
    typeOf' _ = ListType $ typeOf undefined
instance ExprType a => ExprType (RCSet a) where
    typeOf _ = SetType $ typeOf undefined
    typeOf' _ = SetType $ typeOf undefined
instance (ExprType a, ExprType b) => ExprType (a,b) where
    typeOf _ = TupleType (typeOf undefined) (typeOf undefined)
    typeOf' _ = TupleType (typeOf undefined) (typeOf undefined)
instance (ExprType a, ExprType b) => ExprType (Either a b) where
    typeOf _ = SumType (typeOf undefined) (typeOf undefined)
    typeOf' _ = SumType (typeOf undefined) (typeOf undefined)
instance ExprType () where
    typeOf _ = UnitType
    typeOf' _ = UnitType

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
instance Has ExprType Variable where
  has v = has @ExprType (varType v)

instance Show (Variable a) where
    show (Variable name stype) = name ++ ":" ++ show stype

data Constant a where
  Constant :: { constType :: Type a , constValue :: a } -> Constant a
deriving instance Eq a => Eq (Constant a)
deriving instance Ord a => Ord (Constant a)
deriving instance Show a => Show (Constant a)
deriving instance (Read a, ExprType a) => Read (Constant a)

{-# COMPLETE CBool, CUnit, CInt, CFloat, CRational, CReal, CChar, CList, CTuple, CSet, CSum #-}
pattern CBool :: () => (a ~ Bool) => a -> Constant a
pattern CBool b = Constant BoolType b
pattern CUnit :: () => (a ~ ()) => Constant a
pattern CUnit = Constant UnitType ()
pattern CInt :: () => (a ~ Integer) => a -> Constant a
pattern CInt i = Constant IntType i
pattern CFloat :: () => (a ~ Double) => a -> Constant a
pattern CFloat f = Constant FloatType f
pattern CRational :: () => (a ~ Rational) => a -> Constant a
pattern CRational f = Constant RationalType f
pattern CReal :: () => (a ~ AlgReal) => a -> Constant a
pattern CReal f = Constant RealType f
pattern CChar :: () => (a ~ Char) => a -> Constant a
pattern CChar c = Constant CharType c
pattern CString :: () => (a ~ String) => a -> Constant a
pattern CString s = Constant (ListType CharType) s
pattern CList :: () => (xs ~ [x]) => [x] -> Type x -> Constant xs
pattern CList xs t = (Constant (ListType t) xs)
pattern CSet :: () => (xs ~ RCSet x) => RCSet x -> Type x -> Constant xs
pattern CSet xs t = (Constant (SetType t) xs)
pattern CTuple :: () => (ab ~ (a,b)) => a -> b -> Type a -> Type b -> Constant ab
pattern CTuple a b ta tb = (Constant (TupleType ta tb) (a,b))
pattern CSum :: () => (ab ~ (Either a b)) => Either a b -> Type a -> Type b -> Constant ab
pattern CSum ab ta tb = (Constant (SumType ta tb) ab)

int :: Integer -> Some Constant
int i = Some (CInt i)
unit :: Some Constant
unit = Some CUnit
bool :: Bool -> Some Constant
bool b = Some (CBool b)
float :: Double -> Some Constant
float f = Some (CFloat f)
rational :: Rational -> Some Constant
rational f = Some (CRational f)
real :: AlgReal -> Some Constant
real f = Some (CReal f)
char :: Char -> Some Constant
char c = Some (CChar c)
string :: String -> Some Constant
string s = Some (CString s)
list :: ExprType a => [a] -> Some Constant
list xs = Some (CList xs (typeOf' xs))
set :: ExprType a => RCSet a -> Some Constant
set xs = Some (CSet xs (typeOf' xs))
tuple :: (ExprType a, ExprType b) => a -> b -> Some Constant
tuple a b = Some (CTuple a b (typeOf a) (typeOf b))
option :: (ExprType a, ExprType b) => Either a b -> Some Constant
option x = Some (CSum x (typeOf undefined) (typeOf undefined))

-- | Recovers the position of the enum in the original range.
enumIndex :: Type a -> a -> Maybe Int
enumIndex (SumType UnitType _) (Left ()) = Just 0
enumIndex (SumType UnitType UnitType) (Right ()) = Just 1
enumIndex (SumType UnitType t) (Right x) = (+1) <$> enumIndex t x
enumIndex _ _ = Nothing

-- | Show a value, printing enums as their position in the original range.
prettyValue :: Type a -> a -> String
prettyValue t x | Just i <- enumIndex t x = show i
prettyValue (ListType CharType) s = show s
prettyValue (ListType t) xs = "[" ++ List.intercalate "," (map (prettyValue t) xs) ++ "]"
prettyValue (TupleType a b) (x, y) = "(" ++ prettyValue a x ++ "," ++ prettyValue b y ++ ")"
prettyValue (SumType a _) (Left x) = "Left " ++ prettyValue a x
prettyValue (SumType _ b) (Right y) = "Right " ++ prettyValue b y
prettyValue t x = has @Show t $ show x

prettyConstant :: Some Constant -> String
prettyConstant (Some (Constant t x)) = prettyValue t x

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
            Some RationalType -> parseRational $ lkup "value" m
            Some RealType -> parseReal $ lkup "value" m
            Some UnitType -> parseUnit $ lkup "value" m
            Some CharType -> parseChar $ lkup "value" m
            Some (ListType t) -> parseList t $ lkup "value" m
            Some (SetType t) -> parseSet t $ lkup "value" m
            Some (TupleType a b) -> parseTuple a b $ lkup "value" m
            Some (SumType a b) -> parseSum a b $ lkup "value" m
        where
        parseType (JSON.String (Text.unpack -> s)) = case s of
          "char" -> pure $ Some CharType
          "int" -> pure $ Some IntType
          "float" -> pure $ Some FloatType
          "rational" -> pure $ Some RationalType
          "real" -> pure $ Some RealType
          "bool" -> pure $ Some BoolType
          "()" -> pure $ Some UnitType
          '[':(init -> cs) -> (\(Some t) -> Some $ ListType t) <$> parseType (JSON.String (Text.pack cs))
          '{':(init -> cs) -> (\(Some t) -> Some $ SetType t)  <$> parseType (JSON.String (Text.pack cs))
          '(':(parseTupleType 0 . init -> (a,b))
            -> (\(Some a') (Some b') -> Some $ TupleType a' b')
                      <$> parseType (JSON.String (Text.pack a))
                      <*> parseType (JSON.String (Text.pack b))
          '<':(parseTupleType 0 . init -> (a,b))
            -> (\(Some a') (Some b') -> Some $ SumType a' b')
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
        parseUnit (JSON.String s)
          | "()" <- Text.unpack s = return unit
        parseUnit _ = fail "failed to parse a unit"
        parseChar (JSON.String s)
         | [c] <- Text.unpack s
         = return $ char c
        parseChar _ = fail "type indicates char, but value is not of type char"
        parseFloat (JSON.Number (DS.toRealFloat -> f)) = return $ float f
        parseFloat _ = fail "type indicates float, but value is not a number"
        parseRational (JSON.Number f) = return $ rational $ toRational f
        parseRational _ = fail "type indicates rational, but value is not a number"
        parseReal (JSON.Number f) = return $ real $ fromRational $ toRational f
        parseReal _ = fail "type indicates rational, but value is not a number"
        parseList t (JSON.Array xs) = has @ExprType t list <$> mapM (unSome t <=< JSON.parseJSON @(Some Constant)) (Vec.toList xs)
          where
            unSome :: Type a -> Some Constant -> JSON.Parser a
            unSome tp (Some (Constant tp' v)) = case tp' `geq` tp of
              Nothing -> fail $ "type indicates list of " <> show tp <> ", but at least one element was a " <> show tp'
              Just Refl -> pure v
        parseList _ _ = fail "type indicates list, but value is not of type array"
        parseSet :: Type t -> JSON.Value -> JSON.Parser (Some Constant)
        parseSet t (JSON.Object m')
          | Just x <- JSON.lookup "regularset" m'
          = do
            Some (CList xs t') <- parseList t x
            case geq t t' of
              Nothing -> error "unexpected element type in set"
              Just Refl -> withExprConstraints t $ pure $ Some $ CSet (RegularSet $ Set.fromList xs) t
          | Just x <- JSON.lookup "complement" m'
          = do
            Some (CList xs t') <- parseList t x
            case geq t t' of
              Nothing -> error "unexpected element type in set"
              Just Refl -> withExprConstraints t $ pure $ Some $ CSet (ComplementSet $ Set.fromList xs) t
        parseSet _ _ = error "no regular or complement fields in json of set"
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
        parseSum :: Type a -> Type b -> JSON.Value -> JSON.Parser (Some Constant)
        parseSum a b (JSON.Object m')
          | Just x <- JSON.lookup "left" m'
          = do
          Some (Constant xt xv) <- JSON.parseJSON x
          case a `geq` xt of
            Nothing -> fail "type of left element of tuple doesn't match"
            Just Refl -> has @ExprType xt $ return $ Some $ CSum (Left xv) a b
          | Just y <- JSON.lookup "right" m'
          = do
          Some (Constant yt yv) <- JSON.parseJSON y
          case b `geq` yt of
            Nothing -> fail "type of right element of tuple doesn't match"
            Just Refl -> has @ExprType yt $ return $ Some $ CSum (Right yv) a b
        parseSum _ _ _ = fail "type indicates either, but value is not of type object"
    parseJSON _ = fail "expected Constant JSON"

instance JSON.ToJSON (Some Constant) where
    toJSON (Some v) = case v of
      CBool b -> JSON.Object $ JSON.insert "type" "bool" $ JSON.insert "value" (JSON.Bool b) JSON.empty
      CUnit -> JSON.Object $ JSON.insert "type" "()" $ JSON.insert "value" (JSON.String $ Text.pack "()") JSON.empty
      CInt i -> JSON.Object $ JSON.insert "type" "int" $ JSON.insert "value" (JSON.Number $ fromInteger i) JSON.empty
      CFloat f -> JSON.Object $ JSON.insert "type" "float" $ JSON.insert "value" (JSON.Number $ fromFloatDigits f) JSON.empty
      CRational f -> JSON.Object $ JSON.insert "type" "rational" $ JSON.insert "value" (JSON.Number $ fst $ DS.fromRationalRepetendUnlimited f) JSON.empty
      CReal f -> JSON.Object $ JSON.insert "type" "real" $ JSON.insert "value" (JSON.Number $ fromRational $ toRational f) JSON.empty
      CChar c -> JSON.Object $ JSON.insert "type" "string" $ JSON.insert "value" (JSON.String $ Text.pack [c]) JSON.empty
      CList xs t -> JSON.Object
        $ JSON.insert "type" (fromString . show $ ListType t)
        $ JSON.insert "value" (JSON.Array $ Vec.fromList $ map (JSON.toJSON . Some . Constant t) xs)
        JSON.empty
      CSet xs t -> JSON.Object
        $ JSON.insert "type" (fromString . show $ SetType t)
        $ JSON.insert "value" (case xs of
          RegularSet    x -> JSON.Object $ JSON.insert "regularset" (JSON.Array $ Vec.fromList $ map (JSON.toJSON . Some . Constant t) $ Set.toList x) JSON.empty
          ComplementSet x -> JSON.Object $ JSON.insert "complement" (JSON.Array $ Vec.fromList $ map (JSON.toJSON . Some . Constant t) $ Set.toList x) JSON.empty
          ) JSON.empty
      --(JSON.Array $ Vec.fromList $ map (JSON.toJSON . Some . Constant t) xs)
      CTuple x y a b -> JSON.Object
        $ JSON.insert "type" (fromString . show $ TupleType a b)
        $ JSON.insert "value" (JSON.Object $ JSON.insert "left" (JSON.toJSON . Some $ Constant a x) $ JSON.insert "right" (JSON.toJSON . Some $ Constant b y) JSON.empty)
        JSON.empty
      CSum xy a b -> JSON.Object
        $ JSON.insert "type" (fromString . show $ SumType a b)
        $ JSON.insert "value" (case xy of
          Left  x -> JSON.Object $ JSON.insert "left"  (JSON.toJSON . Some $ Constant a x) JSON.empty
          Right y -> JSON.Object $ JSON.insert "right" (JSON.toJSON . Some $ Constant b y) JSON.empty)
        JSON.empty

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
    RationalType -> k
    RealType -> k
    BoolType -> k
    CharType -> k
    UnitType -> k
    ListType t' -> has @ConstType t' k
    SetType t' -> has @ConstType t' k
    TupleType a b -> has @ConstType a $ has @ConstType b k
    SumType a b -> has @ConstType a $ has @ConstType b k

-- ----------------------------------------------------------------------------------------- --
-- value expression

data ExprView t where
    Var :: {variable :: Variable t} -> ExprView t
    Const :: ExprConstraints t => {constant :: t} -> ExprView t
    Ite :: {conditional :: ExprView Bool, trueBranch :: ExprView t, falseBranch :: ExprView t} -> ExprView t
    Equal :: ExprConstraints t => {eqType :: Type t, left :: ExprView t, right :: ExprView t} -> ExprView Bool
    Divide :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    Modulo :: {dividend2 :: ExprView Integer, divisor2 :: ExprView Integer} -> ExprView Integer
    DivideFloat :: Fractional a => {dividendF :: ExprView a, divisorF :: ExprView a} -> ExprView a
    Sum :: Num a => Type a -> FreeSum (ExprView a) -> ExprView a
    Product :: Num a => Type a -> FreeProduct (ExprView a) -> ExprView a
    Gez :: Num a => ExprView a -> ExprView Bool
    Not :: ExprView Bool -> ExprView Bool
    And :: Set (ExprView Bool) -> ExprView Bool
    Concat :: ExprConstraints a => ExprView [[a]] -> ExprView [a]
    Cons :: ExprView x -> ExprView [x] -> ExprView [x]
    Append :: ExprView [a] -> ExprView [a] -> ExprView [a]
    Length :: Type a -> ExprView [a] -> ExprView Integer
    LElem :: Type a -> ExprView a -> ExprView [a] -> ExprView Bool
    Take :: ExprView Integer -> ExprView [a] -> ExprView [a]
    Drop :: ExprView Integer -> ExprView [a] -> ExprView [a]
    First :: Type b -> ExprView (a,b) -> ExprView a
    Second :: Type a -> ExprView (a,b) -> ExprView b
    Pair :: ExprView a -> ExprView b -> ExprView (a,b)
    Head :: ExprConstraints x => ExprView [x] -> ExprView x
    Tail :: ExprConstraints x => ExprView [x] -> ExprView [x]
    ELeft  :: (ExprConstraints a, ExprConstraints b) => ExprView a -> ExprView (Either a b)
    ERight  :: (ExprConstraints a, ExprConstraints b) => ExprView b -> ExprView (Either a b)
    SElem :: Type a -> ExprView a -> ExprView (RCSet a) -> ExprView Bool
    SInsert :: ExprConstraints a => ExprView a -> ExprView (RCSet a) -> ExprView (RCSet a)
    Zip :: Type a -> Type b -> ExprView [a] -> ExprView [b] -> ExprView [(a,b)]
    -- Adding Lam and App would make it impossible to implement some typeclasses that SBV wants,
    -- and is also stronger than we need: we don't need lists of functions, top-level functions, etc.
    -- Lam :: Variable t -> ExprView a -> ExprView (a -> t)
    -- App :: Type a -> ExprView (a -> b) -> ExprView a -> ExprView b
    -- Instead, 'Map', 'Filter', 'Fold's, and 'Either' (the only places where we want a function)
    -- just inline the definition of Lam: they carry the bound variable and the function body (which may reference this variable)
    Map :: (ExprConstraints a, ExprConstraints b) => Variable a -> ExprView b -> ExprView [a] -> ExprView [b]
    Filter :: ExprConstraints a => Variable a -> ExprView Bool -> ExprView [a] -> ExprView [a]
    -- for folds, the first `ExprView b` is the function and the second is the initial value
    Foldr :: ExprConstraints a => Variable a -> Variable b -> ExprView b -> ExprView b -> ExprView [a] -> ExprView b
    Foldl :: ExprConstraints a => Variable b -> Variable a -> ExprView b -> ExprView b -> ExprView [a] -> ExprView b
    -- The first 'ExprView x' has the 'Variable a' in scope, the second 'ExprView x' has the 'Variable b' in scope.
    -- This is the `either` deconstructor in Haskell: (a -> x) -> (b -> x) -> Either a b -> x
    Either :: (ExprConstraints a, ExprConstraints b, ExprConstraints x) => Variable a -> Variable b -> ExprView x -> ExprView x -> ExprView (Either a b) -> ExprView x
    -- NOTE: when adding more fields, check the Eq instance

type ExprConstraints t = (Data t, Eq t, Ord t, OrdSymbolic (SBV t), Show t, ExprType t, SymVal t, Eq t, ConstType t, Read t)

viewType :: ExprView a -> Type a
viewType v = withExprConstraints v $ typeOf' v

instance Eq (ExprView t) where
  Var x == Var y = x == y
  Const x == Const y = x == y
  Ite c1 l1 r1 == Ite c2 l2 r2 = c1 == c2 && l1 == l2 && r1 == r2
  Equal t1 a b == Equal t2 x y
    | Just Refl <- t1 `geq` t2 = a == x && b == y
  Divide a b == Divide x y = a == x && b == y
  Modulo a b == Modulo x y = a == x && b == y
  DivideFloat a b == DivideFloat x y = a == x && b == y
  Sum _ x == Sum _ y = x == y
  Product _ x == Product _ y = x == y
  Gez x == Gez y
    | Just Refl <- viewType x `geq` viewType y = x == y
  Not x == Not y = x == y
  And x == And y = x == y
  Concat x == Concat y = x == y
  Cons x xs == Cons y ys = x == y && xs == ys
  Append x xs == Append y ys = x == y && xs == ys
  Length a x == Length b y
    | Just Refl <- a `geq` b = x == y
  LElem t1 x y == LElem t2 a b
    | Just Refl <- t1 `geq` t2 = x == a && y == b
  Take x xs == Take y ys = x == y && xs == ys
  Drop x xs == Drop y ys = x == y && xs == ys
  First t1 x == First t2 y
   | Just Refl <- geq t1 t2
   = x == y
  Second t1 x == Second t2 y
   | Just Refl <- geq t1 t2
   = x == y
  Pair a b == Pair x y = a == x && b == y
  Head x == Head y = x == y
  Tail x == Tail y = x == y
  ELeft x == ELeft y
    | Just Refl <- geq (typeOf' x) (typeOf' y) = x == y
  ERight x == ERight y
    | Just Refl <- geq (typeOf' x) (typeOf' y) = x == y
  SElem t1 x y == SElem t2 a b
    | Just Refl <- t1 `geq` t2 = x == a && y == b
  SInsert x y == SInsert a b = x == a && y == b
  Zip ta tb x y == Zip ta' tb' x' y'
    | Just Refl <- ta `geq` ta'
    , Just Refl <- tb `geq` tb'
    = x == x' && y == y'
  Map v1 f xs == Map v2 g ys
    | Just Refl <- geq v1 v2
    = f == g && xs == ys
  Foldr v1 v2 f x xs == Foldr v1' v2' g y ys
    | Just Refl <- geq (typeOf' xs) (typeOf' ys)
    = v1 == v1' && v2 == v2' && f == g && x == y && xs == ys
  Foldl v1 v2 f x xs == Foldl v1' v2' g y ys
    | Just Refl <- geq (typeOf' xs) (typeOf' ys)
    = v1 == v1' && v2 == v2' && f == g && x == y && xs == ys
  Filter v f xs == Filter v' g ys = v == v' && f == g && xs == ys
  Either ta tb a b c == Either tx ty x y z
    | Just Refl <- geq ta tx
    , Just Refl <- geq tb ty
    = a == x && b == y && c == z
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
      (DivideFloat a b, DivideFloat x y) ->
        compare (a, b) (x, y)
      (Sum _ x, Sum _ y) ->
        compare x y
      (Product _ x, Product _ y) ->
        compare x y
      (Gez a, Gez b) ->
        case gcompare (viewType a) (viewType b) of
          GLT -> LT
          GGT -> GT
          GEQ -> compare a b
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
      (Length a x, Length b y) -> case gcompare a b of
        GLT -> LT
        GGT -> GT
        GEQ -> compare x y
      (LElem t1 x xs, LElem t2 y ys) ->
        case gcompare t1 t2 of
          GLT -> LT
          GGT -> GT
          GEQ -> compare (x,xs) (y,ys)
      (Take i xs, Take j ys) ->
        compare (i,xs) (j,ys)
      (Drop i xs, Drop j ys) ->
        compare (i,xs) (j,ys)
      (First t1 x, First t2 a) ->
        case gcompare t1 t2 of
          GLT -> LT
          GGT -> GT
          GEQ -> compare x a
      (Second t1 x, Second t2 a) ->
        case gcompare t1 t2 of
          GLT -> LT
          GGT -> GT
          GEQ -> compare x a
      (Pair x y, Pair a b) ->
        compare (x,y) (a,b)
      (Head x, Head a) ->
        compare x a
      (Tail x, Tail a) ->
        compare x a
      (ELeft x, ELeft y) -> case gcompare (typeOf' x) (typeOf' y) of
        GLT -> LT
        GGT -> GT
        GEQ -> compare x y
      (ERight x, ERight y) -> case gcompare (typeOf' x) (typeOf' y) of
        GLT -> LT
        GGT -> GT
        GEQ -> compare x y
      (SElem tx x xs, SElem ty y ys) -> case gcompare tx ty of
        GLT -> LT
        GGT -> GT
        GEQ -> case compare x y of
          EQ -> compare xs ys
          c -> c
      (SInsert x xs, SInsert y ys) -> case gcompare (typeOf' x) (typeOf' y) of
        GLT -> LT
        GGT -> GT
        GEQ -> case compare x y of
          EQ -> compare xs ys
          c -> c
      (Zip ta tb a b, Zip tx ty x y) ->
        case gcompare ta tx of
          GLT -> LT
          GGT -> GT
          GEQ -> case gcompare tb ty of
            GLT -> LT
            GGT -> GT
            GEQ -> compare (a,b) (x,y)
      (Either ta tb a b c, Either tx ty x y z) ->
        case gcompare ta tx of
          GLT -> LT
          GGT -> GT
          GEQ -> case gcompare tb ty of
            GLT -> LT
            GGT -> GT
            GEQ -> compare (a,b,c) (x,y,z)
      (Map x y z, Map a b c) ->
        case gcompare x a of
          GLT -> LT
          GGT -> GT
          GEQ -> compare (y,z) (b,c)
      (Foldr v1 v2 f x xs, Foldr v1' v2' g y ys) ->
        case gcompare v1 v1' of
          GLT -> LT
          GGT -> GT
          GEQ -> compare (v2, f, x, xs) (v2', g, y, ys)
      (Foldl v1 v2 f x xs, Foldl v1' v2' g y ys) ->
        case gcompare v2 v2' of
          GLT -> LT
          GGT -> GT
          GEQ -> compare (v1, f, x, xs) (v1', g, y, ys)
      (Filter v1 f xs, Filter v2 g ys) -> compare (v1, f, xs) (v2, g, ys)
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
        Gez{}     -> 9
        Not{}     -> 10
        And{}     -> 11
        Concat{}  -> 12
        Cons{}    -> 13
        Append{}  -> 14
        LElem{}   -> 15
        Take{}    -> 16
        Drop{}    -> 17
        DivideFloat{} -> 18
        Filter{} -> 22
        ELeft{} -> 23
        ERight{} -> 24
        First{} -> 25
        Second{} -> 26
        Pair{} -> 27
        Head{} -> 28
        Tail{} -> 29
        Either{} -> 30
        Map{} -> 31
        SElem{} -> 32
        SInsert{} -> 33
        Foldr{} -> 34
        Foldl{} -> 35
        Zip{} -> 36


instance Show (ExprView t) where
  show = \case
    (Var v) -> varName v
    (Const c) -> show c
    (Ite cond e1 e2) -> "if " ++ bshow cond ++ " then " ++ bshow e1 ++ " else " ++ bshow e2
    (Divide e1 e2) -> bshow e1 ++ " / " ++ bshow e2
    (Modulo e1 e2) -> bshow e1 ++ " % " ++ bshow e2
    (DivideFloat e1 e2) -> bshow e1 ++ " / " ++ bshow e2
    (Sum _ es) | es == mempty -> "∑∅"
    (Sum _ es) -> showFreeMonoid "+" bshowSumTerm es
      where
      bshowSumTerm (-1)     t = "-" ++ t
      bshowSumTerm 1 t = t
      bshowSumTerm n t = bshow n ++ "⋅" ++ t
    (Product _ es) | es == mempty -> "∏∅"
    (Product _ es) -> showFreeMonoid "⋅" (\n t -> bshow n ++ "^" ++ t) es -- "(" ++ bshow e2 ++ ")" --FreeProduct Expr
    (Length _ e) -> "length " ++ bshow e
    (Equal _ e1 e2) -> bshow e1 ++ " = " ++ bshow e2
    (Gez e) -> bshow e ++ " ≥ 0"
    (Not e) -> "¬" ++ bshow e
    (And (Set.toList -> [])) -> "⋀∅"
    (And (Set.toList -> es)) -> List.intercalate "∧" $ bshow <$> es
    (Concat es) -> "concat " <> bshow es
    (Cons x xs) -> bshow x ++ ":" ++ bshow xs
    (Append xs ys) -> bshow xs ++ "++" ++ bshow ys
    (LElem _ x xs) -> bshow x ++ "`elem`" ++ bshow xs
    (Take i xs) -> "take " ++ bshow i ++ " " ++ bshow xs
    (Drop i xs) -> "drop " ++ bshow i ++ " " ++ bshow xs
    (Head x) -> "head " <> bshow x
    (Tail x) -> "tail " <> bshow x
    (First _ x) -> "fst " <> bshow x
    (Second _ x) -> "snd " <> bshow x
    (Pair x y) -> "(" <> show x <> ", " <> show y <> ")"
    (Either _ _ l r x) -> "either " <> bshow l <> " " <> bshow r <> " " <> bshow x
    (Zip _ _ x y) -> "zip " <> bshow x <> " " <> bshow y
    (Map v f xs) -> "map (\\" <> show v <> " -> " <> show f <> ") " <> bshow xs
    (ELeft x) -> "Left " <> bshow x
    (ERight x) -> "Right " <> bshow x
    (SElem _ x xs) -> bshow x <> "`Set.elem`" <> bshow xs
    (SInsert x xs) -> "Set.insert " <> bshow x <> " " <> bshow xs
    (Filter _ f xs) -> "filter " <> bshow f <> " " <> bshow xs
    (Foldr _ _ f i xs) -> "foldr " <> bshow f <> " " <> bshow i <> " " <> bshow xs
    (Foldl _ _ f i xs) -> "foldl " <> bshow f <> " " <> bshow i <> " " <> bshow xs
    where
      bshow x = let y = show x in if isJust (List.elemIndex ' ' y) then '(' : y <> ")" else y

instance Has ExprType Expr where
  has (Expr v) = has @ExprType v

instance Has ExprType ExprView where
  has e k = case e of
    Var v -> has @ExprType (varType v) k
    Const _ -> k
    Ite _ x _ -> has @ExprType x k
    Equal t _ _ -> has @ExprType t k
    Divide _ _ -> k
    DivideFloat x _ -> has @ExprType x k
    Modulo _ _ -> k
    Sum t _ -> has @ExprType t k
    Product t _ -> has @ExprType t k
    Length t _ -> has @ExprType t k
    Gez _ -> k
    Not _ -> k
    And _ -> k
    Concat _ -> k
    Cons _ x -> has @ExprType x k
    Append _ x -> has @ExprType x k
    LElem t _ _ -> has @ExprType t k
    Take _ x -> has @ExprType x k
    Drop _ x -> has @ExprType x k
    First _ x -> case has @ExprType x $ typeOf' x of
      TupleType t _ -> has @ExprType t k
    Second _ x -> case has @ExprType x $ typeOf' x of
      TupleType _ t -> has @ExprType t k
    Pair x y -> has @ExprType x $ has @ExprType y k
    Head x -> case typeOf' x of
      ListType t -> has @ExprType t k
    Tail x -> case typeOf' x of
      ListType t -> has @ExprType t k
    Zip x y _ _ -> has @ExprType x $ has @ExprType y k
    Either _ _ x _ _ -> has @ExprType x k
    Map _ x _ -> has @ExprType x k
    ELeft x -> has @ExprType x k
    ERight x -> has @ExprType x k
    SElem{} -> k
    SInsert x _ -> has @ExprType x k
    Filter _ _ x -> has @ExprType x k
    Foldr _ x _ _ _ -> has @ExprType x k
    Foldl x _ _ _ _ -> has @ExprType x k

showFreeMonoid :: Show a => String -> (Integer -> String -> String) -> FreeMonoidX a -> String
showFreeMonoid plusRepr multRepr (FMX p) = List.intercalate plusRepr $ showTerm <$> Map.assocs p
    where
    showTerm (x, i) = multRepr i (show x)


-- | Expr: value expression
-- Only 'view' is exported, not the constructor, to safeguard invariants.
newtype Expr t = Expr {view :: ExprView t} deriving (Eq, Ord)
-- TODO: which invariants? I can't find any other mention of them,
-- so I've been assuming that any representable ExprView is fair game

instance Show (Expr t) where
  show = show . view

instance GShow Expr where
  gshowsPrec = defaultGshowsPrec

instance GEq Expr where
  geq x y = withExprConstraints x $ withExprConstraints y $ geq (typeOf' x) (typeOf' y)

instance GCompare Expr where
  gcompare x y = withExprConstraints x $ withExprConstraints y $ case gcompare (typeOf' x) (typeOf' y) of
    GLT -> GLT
    GGT -> GGT
    GEQ -> case compare x y of
      GT -> GGT
      LT -> GLT
      EQ -> GEQ


isConst :: ExprView v -> Bool
isConst (Const _) = True
isConst _ = False


freeVars :: Expr t -> Set.Set (Some Variable)
freeVars = Set.fromList . freeVars' . view

freeVars' :: ExprView t -> [Some Variable]
freeVars' (Var v) = [Some v]
freeVars' (Const _) = []
freeVars' (Ite cond e1 e2) = freeVars' cond ++ freeVars' e1 ++ freeVars' e2
freeVars' (Divide e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Modulo e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (DivideFloat e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Sum _ (distinctTermsT -> es)) = concatMap freeVars' es
freeVars' (Product _ (distinctTermsT -> es)) = concatMap freeVars' es
freeVars' (Length _ e) = freeVars' e
freeVars' (Equal _ e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Gez e) = freeVars' e
freeVars' (Not e) = freeVars' e
freeVars' (And (Set.toList -> es)) = concatMap freeVars' es
freeVars' (Concat es) = freeVars' es
freeVars' (Cons e es) = freeVars' e ++ freeVars' es
freeVars' (Append e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (LElem _ e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Take e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (Drop e1 e2) = freeVars' e1 ++ freeVars' e2
freeVars' (First _ x) = freeVars' x
freeVars' (Second _ x) = freeVars' x
freeVars' (Pair x y) = freeVars' x ++ freeVars' y
freeVars' (Head xs) = freeVars' xs
freeVars' (Tail xs) = freeVars' xs
freeVars' (ELeft x) = freeVars' x
freeVars' (ERight x) = freeVars' x
freeVars' (SElem _ x xs) = freeVars' x ++ freeVars' xs
freeVars' (SInsert x xs) = freeVars' x ++ freeVars' xs
freeVars' (Zip _ _ x y) = freeVars' x ++ freeVars' y
-- v, vl, and vr are not free
freeVars' (Map v f xs) = filter (/= Some v) (freeVars' f) ++ freeVars' xs
freeVars' (Either vl vr l r x) = filter (/= Some vl) (freeVars' l) ++ filter (/= Some vr) (freeVars' r) ++ freeVars' x
freeVars' (Filter v f xs) = filter (/= Some v) (freeVars' f) ++ freeVars' xs
freeVars' (Foldr v1 v2 f i xs) = filter (not . flip elem [Some v1, Some v2]) (freeVars' f) ++ freeVars' i ++ freeVars' xs
freeVars' (Foldl v1 v2 f i xs) = filter (not . flip elem [Some v1, Some v2]) (freeVars' f) ++ freeVars' i ++ freeVars' xs

