{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}

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
import qualified Data.Set as Set
import Data.Bifunctor (Bifunctor(..))

-- | A Boolean expression over atoms. The algorithm only compares atoms for
-- equality, so an atom can be a name or a full predicate such as @x > 5@.
data Expr a
  = Atom a
  | Not (Expr a)
  | And (Expr a) (Expr a)
  | Or  (Expr a) (Expr a)
    -- | A condition on the number of sub-expressions that hold.
  | Count [Bool] [Expr a]
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
eval r (Count table es) = table !! length (filter (eval r) es)

-- | Generate the MC/DC rows of an expression, each with the value of the
-- expression on that row. An expression with @n@ atoms gives @n+1@ different
-- rows. For each atom, two of the rows differ in that atom only and give
-- different values (a unique-cause independence pair).
gen :: Ord a => Expr a -> Set.Set (Row a, Bool)
gen (Atom a)  = Set.fromList [(M.singleton a True, True), (M.singleton a False, False)]
gen (Not e)   = Set.map (second not) (gen e)
gen (And x y) = glue True  x y
gen (Or  x y) = glue False x y
gen (Count table es) = glueCount table es

-- | Combine the rows of @x@ and @y@ for @x && y@ (@ident = True@) or
-- @x || y@ (@ident = False@). A /neutralVal/ is a row on which a child has the value
-- @ident@. While one child is on its neutralVal, the node has the value of the other
-- child, so the independence pairs of that child stay valid. The two halves
-- share the row @neutralValX <> neutralValY@, which gives @(n1+1) + (n2+1) - 1@ rows.
glue :: Ord a => Bool -> Expr a -> Expr a -> Set.Set (Row a, Bool)
glue ident x y =
     Set.map (first (`M.union` neutralValY)) rowsX
  <> Set.map (first (neutralValX `M.union`)) rowsY
  where
    rowsX          = gen x
    rowsY          = gen y
    neutralValX    = takeFirstNeutral ident rowsX
    neutralValY    = takeFirstNeutral ident rowsY

-- | Combine the rows of the sub-expressions of a count. Let @k@ be a number for
-- which the count has different values on @k@ and on @k+1@ sub-expressions
-- that hold. While @k@ of the other sub-expressions hold, the count follows the
-- value of the remaining one, so the independence pairs of that one stay valid.
-- The others are on their first true row or their first false row. For
-- sub-expressions that are atoms, this gives one row more than there are atoms.
glueCount :: Ord a => [Bool] -> [Expr a] -> Set.Set (Row a, Bool)
glueCount table es = Set.fromList
  [ (row `M.union` M.unions [ if j `elem` holding i then firstTrue j else firstFalse j | j <- indices, j /= i ]
    , table !! (k + fromEnum v))
  | i <- indices, (row, v) <- Set.toList $ rows !! i ]
  where
    indices      = [0 .. length es - 1]
    rows         = map gen es
    firstTrue j  = takeFirstNeutral True  (rows !! j)
    firstFalse j = takeFirstNeutral False (rows !! j)
    k = case [ n | (n, (v, w)) <- zip [0 ..] (zip table (drop 1 table)), v /= w ] of
      n : _ -> n
      []    -> error "MCDCGeneration.glueCount: the count has the same value for any number of sub-expressions" -- unreachable after 'isWellFormed'
    -- the k other sub-expressions that hold while sub-expression i varies, taken from the first k+1 of them
    holding i = [ j | j <- [0 .. k], j /= (if i <= k then i else 0) ]

-- | True if each count has a table of the right size, and a value that depends
-- on the number of sub-expressions that hold.
isWellFormed :: Expr a -> Bool
isWellFormed (Atom _)  = True
isWellFormed (Not e)   = isWellFormed e
isWellFormed (And x y) = isWellFormed x && isWellFormed y
isWellFormed (Or  x y) = isWellFormed x && isWellFormed y
isWellFormed (Count table es) =
  length table == length es + 1 && or table && not (and table) && all isWellFormed es

-- | Take out the first row with the given value. Return it and the other rows.
takeFirstNeutral :: Bool -> Set.Set (Row a, Bool) -> Row a
takeFirstNeutral ident rows = case Set.filter ((== ident) . snd) rows of
  (Set.toList -> []) -> error $ "MCDCGeneration.takeFirstNeutral: no row with value " ++ show ident
  (Set.toList -> (x:_)) -> fst x

-- | The rows of 'gen', or 'Left' if the expression is not singular.
mcdcRows :: Ord a => Expr a -> Either String [(Row a, Bool)]
mcdcRows e
  | not (isSingular e)   = Left "not a singular Boolean expression: some atom occurs more than once"
  | not (isWellFormed e) = Left "a count does not depend on the number of sub-expressions that hold"
  | otherwise            = Right (Set.toList $ gen e)

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
subst r (Count table es) = Count table (map (subst r) es)

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
validate e rows = all total rows && distinct && not (any (null . snd) prs)
  where
    as       = S.fromList (atoms e)
    total r  = M.keysSet r == as
    distinct = S.size (S.fromList rows) == length rows
    prs      = independencePairs e rows

