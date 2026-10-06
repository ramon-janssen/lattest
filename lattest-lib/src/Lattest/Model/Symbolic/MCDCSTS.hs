{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}

-- | Split the guarded input switches of an STS into their unique-cause MC/DC
-- rows. A test suite that covers every switch of the result has MC/DC coverage
-- of the original guards.
module Lattest.Model.Symbolic.MCDCSTS
  ( completeMCDC
  , splitGuard
  ) where

import           Control.Monad   (forM_, when)
import qualified Data.Foldable   as Foldable
import           Data.List       (partition)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import qualified Debug.Trace

import           Lattest.Model.Alphabet (IOAct (In), SymGuard, SymInteract (SymInteract))
import           Lattest.Model.Automaton (STStdest (STSLoc), automaton, alphabet, initConf,
                                           reachable, stsTLoc, transRel)
import           Lattest.Model.BoundedMonad (BoundedMonad, MeetSemiLattice ((/\)), ordBind,
                                             ordReturn)
import qualified Lattest.Model.Internal.MCDCGeneration as MCDC
import           Lattest.Model.StandardAutomata (STS)
import           Lattest.Model.Symbolic.Expr (freeVars, (.&&), (.-), (.==), (.||))
import           Lattest.Model.Symbolic.Internal.ExprDefs (Expr (Expr),
                                                            ExprView (And, Const, Equal, Filter, GezInt, Length, Not, Product, Sum),
                                                            Type (IntType), view)
import           Lattest.Model.Symbolic.Internal.FreeMonoidX (distinctTermsT)
import           Lattest.Model.Symbolic.Internal.ExprImpls (sAnd, sNot, sTrue)
import           Lattest.Model.Symbolic.SolveSymPrim (solveGuard)

-- | Convert a guard to an MC/DC decision. Each sub-expression that is not a
-- 'Not' or an 'And' is an atom. There is no 'Or' case: the smart constructors
-- store @a || b@ as @Not (And [Not a, Not b])@.
toDecision :: ExprView Bool -> MCDC.Expr (ExprView Bool)
toDecision (Not e)  = MCDC.Not (toDecision e)
toDecision (And es) = case Set.toList es of
  [] -> MCDC.Atom (And Set.empty) -- unreachable: sAnd never builds an empty And
  es' -> foldl1 MCDC.And (map toDecision es')
toDecision leaf = MCDC.Atom leaf

-- | Convert a row to a guard: the conjunction of its literals.
rowGuard :: MCDC.Row (ExprView Bool) -> SymGuard
rowGuard row = sAnd $ Set.fromList [ literal a v | (a, v) <- Map.toList row ]
  where
    literal a True  = Expr a
    literal a False = sNot (Expr a)

{- |
    Split a guard with @N@ atoms into its @N+1@ unique-cause MC/DC rows. The
    result is @(true rows, false rows)@. E.g. @x > 1 || y > 1@ gives

    > ([x > 1 && not (y > 1), not (x > 1) && y > 1], [not (x > 1) && not (y > 1)])
-}
splitGuard :: SymGuard -> Either String ([SymGuard], [SymGuard])
splitGuard guard
  | view guard == Const True = Right ([guard], []) -- no decision to cover: its own single true row
  | otherwise = do
      rows <- MCDC.mcdcRows (toDecision (view guard))
      let (trueRows, falseRows) = partition snd rows
      -- a true row with list counts is split further
      expandedTrueRows <- concat <$> mapM (expandCounts . fst) trueRows
      return (expandedTrueRows, map (rowGuard . fst) falseRows)

-- | Find the counts @length (filter x cond xs)@ in an integer comparison. The
-- search looks through sums and products only.
counts :: ExprView t -> Set.Set (ExprView Integer)
counts e@(Length _ (Filter {}))        = Set.singleton e
counts (Equal _ l r)                   = counts l `Set.union` counts r
counts (GezInt e)                      = counts e
counts (Sum (distinctTermsT -> es))     = Set.unions (map counts es)
counts (Product (distinctTermsT -> es)) = Set.unions (map counts es)
counts _                               = Set.empty

{- |
    Split a row on each count @length (filter x cond xs)@ in it. Each variant
    puts all elements that satisfy @cond@ on one true row of @cond@, and all
    other elements on one false row. E.g. for @cond = x > 1 && x < 5@, the row
    @count == 1@ gives two variants: all other elements are
    @not (x > 1) && x < 5@, or all other elements are @x > 1 && not (x < 5)@.

    The number of variants does not depend on the length of the list. A row
    without counts is its own single variant.
-}
expandCounts :: MCDC.Row (ExprView Bool) -> Either String [SymGuard]
expandCounts row = do
    variantsPerCount <- mapM countVariants (Set.toList $ Set.unions $ map counts $ Map.keys row)
    return [ foldl (.&&) (rowGuard row) variant | variant <- foldr pairUp [[]] variantsPerCount ]
  where
    holds atom = Map.lookup atom row == Just True

    countVariants :: ExprView Integer -> Either String [SymGuard]
    countVariants count@(Length t (Filter x cond xs)) = do
      rows <- MCDC.mcdcRows (toDecision cond)
      let (trueRows, falseRows) = partition snd rows
          matching = Expr count
          total = Expr (Length t xs)
          countOf r = Expr (Length t (Filter x (view (rowGuard r)) xs))
          allMatching r = if countOf r == matching then sTrue else countOf r .== matching -- cond may be its own only true row
          allOthers r = countOf r .== total .- matching
          isZero = holds (Equal IntType count (Const 0)) || holds (Equal IntType (Const 0) count)
          isAll = holds (Equal IntType count (Length t xs)) || holds (Equal IntType (Length t xs) count)
      return $ if
        -- no element matches: only the false rows vary
        | isZero    -> [ allOthers f | (f, _) <- falseRows ]
        -- all elements match: only the true rows vary
        | isAll     -> [ allMatching r | (r, _) <- trueRows ]
        -- pair up (no cross product), so that each row of cond is in a variant
        | otherwise -> map (foldl1 (.&&)) $
                         pairUp (map (allMatching . fst) trueRows) [ [allOthers f] | (f, _) <- falseRows ]
    countVariants _ = Right [] -- unreachable: 'counts' only yields counts

    -- pair up the elements of both lists, repeating those of the shorter one
    pairUp :: [a] -> [[a]] -> [[a]]
    pairUp xs yss = take (max (length xs) (length yss)) $ zipWith (:) (cycle xs) (cycle yss)

{- |
    Replace each switch on the given input gates by one switch per true row of
    its guard. Each new switch keeps the assignment and the destination.

    Use the result to steer test generation, not as a specification: values
    that satisfy the original guard but are not an MCDC row become
    underspecified.

    The other switches on the same gate and location must cover the false rows
    of a guard. An error is raised if, at a reachable location,

      * an atom occurs more than once in a guard,
      * a guard other than the constant @True@ always holds,
      * two guards can hold at the same time, or
      * a false row is not covered by the other guards.
-}
completeMCDC
  :: (Ord loc, Show loc, Ord i, Show i, Ord o, Show o, BoundedMonad m, Foldable m,
      MeetSemiLattice (m (STStdest, loc)))
  => STS m loc (IOAct i o) -> [i] -> IO (STS m loc (IOAct i o))
completeMCDC aut inputGates = do
  -- 'reachable' excludes the initial locations unless another switch leads back to them
  let locs = reachable aut `Set.union` Set.fromList (Foldable.toList (initConf aut))
  -- check all selected gates first, then split
  forM_ locs $ \loc ->
    forM_ (Map.toList (transRel aut loc)) $ \(gate, mval) ->
      if selected gate then checkGate loc gate (guards mval) else return ()
  return $ automaton (initConf aut) (alphabet aut) (Map.mapWithKey splitGate . transRel aut)
  where
    selected (SymInteract (In i) _) = i `elem` inputGates
    selected _                      = False

    guards mval = [ guard | (STSLoc (guard, _), _) <- Foldable.toList mval ]

    splitGate gate mval
      | selected gate = mval `ordBind` splitSwitch
      | otherwise     = mval

    splitSwitch (STSLoc (guard, assign), destLoc) = case splitGuard guard of
      Right (trueRows, _) -> foldr1 (/\) [ ordReturn (stsTLoc row assign, destLoc) | row <- trueRows ]
      Left err            -> errorWithoutStackTrace $ "completeMCDC: " ++ err -- unreachable after 'checkGate'

-- | Check the guards of one gate at one location.
checkGate :: (Show loc, Show gate) => loc -> gate -> [SymGuard] -> IO ()
checkGate loc gate guards = do
    -- a guard that always holds has no false outcome, so no atom of it can have an independence pair
    forM_ indexed $ \(i, guard) -> when (view guard /= Const True) $ do
      counterexample <- solve (sNot guard)
      when (null counterexample) $ failWith $
        "guard #" ++ show i ++ " (" ++ show guard ++ ") is a tautology, so it can not have MC/DC coverage"
    -- the guards must be pairwise disjoint
    forM_ pairs $ \((i, gi), (j, gj)) -> do
      overlap <- solve (gi .&& gj)
      forM_ overlap $ \model -> failWith $
        "guard #" ++ show i ++ " (" ++ show gi ++ ") and guard #" ++ show j ++ " (" ++ show gj ++
        ") are not disjoint -- both hold when " ++ show model
    forM_ indexed $ \(i, guard) -> case splitGuard guard of
      Left err -> failWith $ "guard #" ++ show i ++ " (" ++ show guard ++ "): " ++ err
      Right (trueRows, falseRows) -> do
        -- warn about each row that has no solution
        forM_ (trueRows ++ falseRows) $ \row -> do
          solution <- solve row
          when (null solution) $ warn $
            "MC/DC row " ++ show row ++ " of guard #" ++ show i ++ " (" ++ show guard ++
            ") has no solution, so it can not be covered; no unique-cause MC/DC coverage of this guard"
        -- the other guards must cover each false row
        forM_ falseRows $ \row -> do
          let others = [ g | (j, g) <- indexed, j /= i ]
          uncovered <- solve (if null others then row else row .&& sNot (foldl1 (.||) others))
          forM_ uncovered $ \model -> failWith $
            "false MC/DC row " ++ show row ++ " of guard #" ++ show i ++ " (" ++ show guard ++
            ") is not covered by any other switch"
  where
    indexed = zip [0 :: Int ..] guards
    pairs = [ (a, b) | a@(i, _) <- indexed, b@(j, _) <- indexed, i < j ]
    solve = solveGuard (Set.toList $ Set.unions (map freeVars guards))
    failWith msg = errorWithoutStackTrace $ context ++ msg
    warn msg = Debug.Trace.trace ("warning: " ++ context ++ msg) (return ())
    context = "completeMCDC: at location " ++ show loc ++ ", gate " ++ show gate ++ ": "
