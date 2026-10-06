{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

-- | Minimal unique-cause MC/DC test generation for singular Boolean
-- expressions (SBEs).
module Lattest.Model.Internal.MCDCGeneration
  ( -- * Expressions
    Expr (..)
  , atoms
  , isSingular
  , eval
    -- * Test generation
  , Row
  , mcdc
  , mcdcRows
  , gen
    -- * Substitution
  , subst
  , neg
    -- * Checking
  , validate
  , independencePairs
  ) where

import           Data.Foldable   (toList)
import           Data.List       (tails)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Maybe      (fromMaybe)
import qualified Data.Set        as S

-- | A Boolean expression over atoms. The algorithm only compares atoms for
-- equality, so an atom can be a name or a full predicate such as @x > 5@.
data Expr a
  = Atom a
  | Not (Expr a)
  | And (Expr a) (Expr a)
  | Or  (Expr a) (Expr a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | The atoms of an expression, in left-to-right order, with duplicates.
atoms :: Expr a -> [a]
atoms = toList

-- | True if no atom occurs more than once. The check is syntactic only.
isSingular :: Ord a => Expr a -> Bool
isSingular = go S.empty . toList
  where
    go _ []       = True
    go seen (a:as)
      | a `S.member` seen = False
      | otherwise         = go (S.insert a seen) as

-- | An assignment of truth values to atoms.
type Row a = Map a Bool

-- | Evaluate an expression under a row. An atom that is not in the row is
-- 'False'.
eval :: Ord a => Row a -> Expr a -> Bool
eval r (Atom a)  = fromMaybe False (M.lookup a r)
eval r (Not e)   = not (eval r e)
eval r (And x y) = eval r x && eval r y
eval r (Or  x y) = eval r x || eval r y

-- | Generate the MC/DC rows of an expression, each with the value of the
-- expression on that row. An expression with @n@ atoms gives @n+1@ different
-- rows. For each atom, two of the rows differ in that atom only and give
-- different values (a unique-cause independence pair).
gen :: Ord a => Expr a -> [(Row a, Bool)]
gen (Atom a)  = [(M.singleton a True, True), (M.singleton a False, False)]
gen (Not e)   = [(r, not v) | (r, v) <- gen e]
gen (And x y) = glue True  x y
gen (Or  x y) = glue False x y

-- | Combine the rows of @x@ and @y@ for @x && y@ (@ident = True@) or
-- @x || y@ (@ident = False@). A /neutralVal/ is a row on which a child has the value
-- @ident@. While one child is on its neutralVal, the node has the value of the other
-- child, so the independence pairs of that child stay valid. The two halves
-- share the row @neutralValX <> neutralValY@, which gives @(n1+1) + (n2+1) - 1@ rows.
glue :: Ord a => Bool -> Expr a -> Expr a -> [(Row a, Bool)]
glue ident x y =
     [ (rx `M.union` neutralValY, v) | (rx, v) <- rowsX ] -- all rows of x, with y on its neutralVal
  ++ [ (neutralValX `M.union` ry, w) | (ry, w) <- restY ] -- the other rows of y, with x on its neutralVal
  where
    rowsX          = gen x
    rowsY          = gen y
    (neutralValX, _)      = takeFirstNeutral ident rowsX
    (neutralValY, restY)  = takeFirstNeutral ident rowsY

-- | Take out the first row with the given value. Return it and the other rows.
takeFirstNeutral :: Bool -> [(Row a, Bool)] -> (Row a, [(Row a, Bool)])
takeFirstNeutral ident rows =
  case break ((== ident) . snd) rows of
    (before, (h, _) : after) -> (h, before ++ after)
    (_,      [])             -> -- unreachable: 'gen' always gives a true row and a false row
      error $ "MCDCGeneration.takeFirstNeutral: no row with value " ++ show ident

-- | The rows of 'gen', or 'Left' if the expression is not singular.
mcdcRows :: Ord a => Expr a -> Either String [(Row a, Bool)]
mcdcRows e
  | isSingular e = Right (gen e)
  | otherwise    = Left "not a singular Boolean expression: some atom occurs more than once"

-- | The minimal unique-cause MC\/DC test suite.
mcdc :: Ord a => Expr a -> Either String [Expr a]
mcdc e = map (flip subst e . fst) <$> mcdcRows e

-- | Replace each atom that is 'False' in the row by its negation. The shape
-- of the expression does not change.
subst :: Ord a => Row a -> Expr a -> Expr a
subst r (Atom a)  = if fromMaybe True (M.lookup a r) then Atom a else neg (Atom a)
subst r (Not e)   = neg (subst r e)
subst r (And x y) = And (subst r x) (subst r y)
subst r (Or  x y) = Or  (subst r x) (subst r y)

-- | Negation that removes a double negative: @neg (Not e) = e@.
neg :: Expr a -> Expr a
neg (Not e) = e
neg e       = Not e

-- | For each atom, the pairs of rows that differ in that atom only and give
-- different values of the expression.
independencePairs :: Ord i => Expr i -> [Row i] -> [(i, [(Row i, Row i)])]
independencePairs e rows =
  [ (i, [ (x, y)
        | (x, y) <- distinctPairs rows
        , M.lookup i x /= M.lookup i y  -- x_i != y_i
        , M.delete i x == M.delete i y  -- forall j != i . x_j == y_j
        , eval x e /= eval y e          -- F(x) == F(y)
        ])
  | i <- S.toList (S.fromList (atoms e))
  ]
  where
    distinctPairs xs = [ (x, y) | (x : rest) <- tails xs, y <- rest ]

-- | Check that the rows are a unique-cause MCDC suite: each row assigns all
-- atoms, all rows are different, and each atom has an independence pair.
validate :: Ord a => Expr a -> [Row a] -> Bool
validate e rows = all total rows && distinct && all (not . null . snd) prs
  where
    as       = S.fromList (atoms e)
    total r  = M.keysSet r == as
    distinct = S.size (S.fromList rows) == length rows
    prs      = independencePairs e rows