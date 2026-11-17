{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lattest.Util.PrettyExpr (
  prettyExpr,
  prettyVal,
) where

import Data.Bifunctor (Bifunctor(..))
import Data.Constraint.Extras (Has(..))
import Data.Some (Some (..))
import Lattest.Model.Symbolic.Expr (Variable (..), Val (..), Type (..), ExprType (..), ExprView(..), prettyValue)
import Lattest.Model.Symbolic.Internal.ExprDefs (Expr(..))
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Lattest.Model.Symbolic.Internal.FreeMonoidX as FMX

-- | The text of a value, as that of a constant in 'prettyExpr'.
prettyVal :: Map.Map String (Some Expr) -> Map.Map (Some Type, [Bool]) String -> Val t -> String
prettyVal enums fields (Val x) = prettyExpr enums fields (Expr (Const x))

-- | The text of an expression, in a readable form. Given are the enums and the names of the fields of the structures (as
-- given by the parser): a constant that is an enum is written as its name, and a projection of a structure as its field.
prettyExpr :: Map.Map String (Some Expr) -> Map.Map (Some Type, [Bool]) String -> Expr t -> String
prettyExpr enums fields = pretty 0 . view
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
