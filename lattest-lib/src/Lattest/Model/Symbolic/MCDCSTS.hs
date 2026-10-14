{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Split the guarded input switches of an STS into their unique-cause MC/DC
-- rows. A test suite that covers every switch of the result has MC/DC coverage
-- of the original guards.
module Lattest.Model.Symbolic.MCDCSTS
  ( completeMCDC
  , completeMCDCWith
  , completeMCDCReport
  , completeMCDCReportWith
  , SplitMode (..)
  , MCDCReport (..)
  , GuardReport (..)
  , RowReport (..)
  , RowStatus (..)
  , prettyMCDCReport
  , defaultListLengths
  , splitGuard
  ) where

import           Control.Monad   (filterM, forM, forM_, unless, when, (<=<))
import           Data.Bifunctor  (first)
import qualified Data.Foldable   as Foldable
import           Data.Function   (on)
import           Data.GADT.Compare (geq)
import           Data.IORef      (modifyIORef', newIORef, readIORef)
import           Data.List       (groupBy, intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import           Data.Some       (Some (Some))
import           Data.Type.Equality ((:~:) (Refl))

import           Lattest.Model.Alphabet (IOAct (In), SymGuard, SymInteract (SymInteract))
import           Lattest.Model.Automaton (AutSyntax, STStdest (STSLoc), automaton, alphabet, initConf,
                                           stsTLoc, transRel)
import           Lattest.Model.BoundedMonad (BoundedMonad, MeetSemiLattice ((/\)), ordBind,
                                             ordReturn)
import qualified Lattest.Model.Internal.MCDCGeneration as MCDC
import           Lattest.Model.StandardAutomata (STS)
import           Lattest.Model.Symbolic.Expr (Variable, freeVars, varType, (.&&), (.==), (.||))
import           Lattest.Model.Symbolic.Internal.ExprDefs (Expr (Expr),
                                                            ExprConstraints,
                                                            ExprView (And, Const, Equal, Filter, Foldr, Gez, Length, Map, Not, Product, Sum, Var),
                                                            Type (BoolType), view, withExprConstraints)
import qualified Lattest.Model.Symbolic.Internal.FreeMonoidX as FMX
import           Lattest.Model.Symbolic.Internal.FreeMonoidX (distinctTermsT)
import           Lattest.Model.Symbolic.Internal.ExprImpls (assign, noAssignment, reduce, sAnd, sConst, sFalse,
                                                             sHead, sIfThenElse, sIsNonNegative, sLength, sNot,
                                                             sProduct, sSum, sTail, sTrue, sVar, subst)
import           Lattest.Model.Symbolic.SolveSymPrim (isGuardSatisfiable)

{- |
    A guard, or a part of a guard, after opening its lists for a fixed length.
    A list of length @n@ is opened into its @n@ elements: a condition on all
    elements becomes a condition per element, and the length of the list is a
    constant. The length of a list is then never an atom.
-}
data Opened
  = Known Bool -- ^ a constant for this length
  | Counted (ExprView Integer) [Bool] -- ^ a condition on a count @length (filter x cond xs)@: its value per number of elements that satisfy @cond@
  | Decision (MCDC.Expr (ExprView Bool))

-- | True for the list parameters of the gate: the lists that are opened.
isOpenList :: Set.Set (Some Variable) -> ExprView [a] -> Bool
isOpenList params (Var v) = Some v `Set.member` params
isOpenList _ _            = False

lengthOf :: ExprView [a] -> ExprView Integer
lengthOf xs = view (sLength (Expr xs))

-- | The lengths @length xs@ of the lists that a guard is opened on. These are
-- the list parameters with a condition on all elements (@forall@ or @exists@),
-- a count of elements, or a length in the guard.
openLists :: Set.Set (Some Variable) -> ExprView t -> Set.Set (ExprView Integer)
openLists params e = case e of
  Not x                           -> openLists params x
  And es                          -> Set.unions (map (openLists params) (Set.toList es))
  Foldr _ _ _ _ (Map _ cond xs)
    | isOpenList params xs        -> Set.insert (lengthOf xs) (openLists params cond)
  Length _ (Filter _ cond xs)
    | isOpenList params xs        -> Set.insert (lengthOf xs) (openLists params cond)
  Length _ xs
    | isOpenList params xs        -> Set.singleton e
  Equal _ l r                     -> openLists params l `Set.union` openLists params r
  Gez x                           -> openLists params x
  Sum _ (distinctTermsT -> es)     -> Set.unions (map (openLists params) es)
  Product _ (distinctTermsT -> es) -> Set.unions (map (openLists params) es)
  _                               -> Set.empty

-- | The lengths and counts of opened lists in an integer comparison. The search
-- looks through sums and products only.
lengthTerms :: Set.Set (Some Variable) -> ExprView t -> Set.Set (ExprView Integer)
lengthTerms params e = case e of
  Length _ (Filter _ _ xs)
    | isOpenList params xs        -> Set.singleton e
  Length _ xs
    | isOpenList params xs        -> Set.singleton e
  Equal _ l r                     -> lengthTerms params l `Set.union` lengthTerms params r
  Gez x                           -> lengthTerms params x
  Sum _ (distinctTermsT -> es)     -> Set.unions (map (lengthTerms params) es)
  Product _ (distinctTermsT -> es) -> Set.unions (map (lengthTerms params) es)
  _                               -> Set.empty

-- | True for a comparison with the length of a fold over an opened list, such
-- as the uniqueness of its elements. The search looks through sums and
-- products only.
hasFoldLength :: Set.Set (Some Variable) -> ExprView t -> Bool
hasFoldLength params e = case e of
  Length _ (Foldr _ _ _ _ xs)      -> isOpenList params xs
  Equal _ l r                      -> hasFoldLength params l || hasFoldLength params r
  Gez x                            -> hasFoldLength params x
  Sum _ (distinctTermsT -> es)     -> any (hasFoldLength params) es
  Product _ (distinctTermsT -> es) -> any (hasFoldLength params) es
  _                                -> False

{- |
    Split a guard into @(side conditions, rest)@. A side condition is a
    length guard or a domain guard, met by all possible values of a parameter,
    regardless of MC/DC rows.

    A domain conjunct on the length of an opened list is not a side condition:
    it is a constant for each length, like any other condition on the length.
-}
sideConditions :: Set.Set (Some Variable) -> Set.Set (ExprView Bool) -> SymGuard -> (SymGuard, SymGuard)
sideConditions params domain guard = case view guard of
  And es -> let (side, rest) = Set.partition isSide es in (conj side, conj rest)
  e | isSide e  -> (guard, sTrue)
    | otherwise -> (sTrue, guard)
  where
    isSide :: ExprView Bool -> Bool
    isSide e = hasFoldLength params e || (e `Set.member` domain && Set.null (lengthTerms params e))
    conj es = if Set.null es then sTrue else sAnd (Set.map Expr es)

-- | The conjuncts of the given domain guards: guards that restrict the values
-- of a parameter to its domain, such as the range of the elements of a list.
domainConjuncts :: [SymGuard] -> Set.Set (ExprView Bool)
domainConjuncts guards = Set.unions [ conjuncts (view guard) | guard <- guards ]
  where
    conjuncts (And es) = es
    conjuncts e        = Set.singleton e

isCount :: ExprView Integer -> Bool
isCount (Length _ (Filter {})) = True
isCount _                      = False

-- | Replace lengths in an integer comparison by constants. The search looks
-- through sums and products only.
replaceLengths :: (ExprView Integer -> Maybe Integer) -> ExprView t -> Expr t
replaceLengths value e = case e of
  Length _ _
    | Just k <- value e -> sConst k
  Sum t s               -> withExprConstraints t $ sSum $ FMX.fromOccurListT $
                             map (first (replaceLengths value)) $ FMX.toDistinctAscOccurListT s
  Product t p           -> withExprConstraints t $ sProduct $ FMX.fromOccurListT $
                             map (first (replaceLengths value)) $ FMX.toDistinctAscOccurListT p
  Equal _ l r           -> replaceLengths value l .== replaceLengths value r
  Gez x                 -> sIsNonNegative (replaceLengths value x)
  _                     -> Expr e

-- | The condition on each of the first @n@ elements of a list: the element is
-- substituted for the variable of the condition.
elementConditions :: ExprConstraints a => Int -> Variable a -> ExprView Bool -> ExprView [a] -> [ExprView Bool]
elementConditions n x cond xs =
  [ view $ subst (assign x (sHead (iterate sTail (Expr xs) !! i)) noAssignment) (Expr cond) | i <- [0 .. n - 1] ]

{- |
    Open a guard for lists of length @n@. Each sub-expression that is not a
    'Not', an 'And', or a condition on all elements of an opened list is an
    atom. There is no 'Or' case: the constructors store @a || b@ as
    @Not (And [Not a, Not b])@.

      * @forall@ and @exists@ over an opened list become the conjunction and
        the disjunction of the condition on each element.

      * A comparison with a count @length (filter x cond xs)@ of an opened list
        becomes a count ('MCDC.Count') of the condition on each element.
        Conditions on the same count are combined, e.g.
        @count >= 1 && count <= 2@.
-}
openGuard :: Int -> Set.Set (Some Variable) -> ExprView Bool -> Either String Opened
openGuard n params = close <=< open
  where
    open :: ExprView Bool -> Either String Opened
    open (Not e)  = negation <$> open e
    open (And es) = conjunction =<< mapM open (Set.toList es)
    open e@(Foldr x y body (Const start) (Map z cond xs))
      | Just Refl <- varType x `geq` BoolType, isOpenList params xs, start, Expr body == (sVar x .&& sVar y) =
          conjunction =<< mapM open (elementConditions n z cond xs)
      | Just Refl <- varType x `geq` BoolType, isOpenList params xs, not start, Expr body == (sVar x .|| sVar y) =
          fmap negation . conjunction . map negation =<< mapM open (elementConditions n z cond xs)
      | otherwise = openAtom e
    open e = openAtom e

    openAtom :: ExprView Bool -> Either String Opened
    openAtom e
      | Set.null terms = Right (Decision (MCDC.Atom e))
      | otherwise = case filter isCount (Set.toList terms) of
          [] -> Right $ case at 0 of
            Const b -> Known b
            e'      -> Decision (MCDC.Atom e')
          [count] -> fmap (Counted count) $ forM [0 .. toInteger n] $ \k -> case at k of
            Const b -> Right b
            _       -> Left $ "a count of list elements can only be compared with constants and list lengths, in " ++ show (Expr e)
          _ -> Left $ "more than one count of list elements in " ++ show (Expr e)
      where
        terms = lengthTerms params e
        -- the atom for k elements that satisfy the condition of the count
        at k = reduce $ view $ replaceLengths (value k) e
        value k term
          | isCount term            = Just k
          | term `Set.member` terms = Just (toInteger n)
          | otherwise               = Nothing -- not the length of an opened list

    negation :: Opened -> Opened
    negation (Known b)         = Known (not b)
    negation (Counted c table) = Counted c (map not table)
    negation (Decision d)      = Decision (MCDC.Not d)

    -- conditions on the same count are combined before the count is closed
    conjunction :: [Opened] -> Either String Opened
    conjunction parts
      | not (null [ () | Known False <- combined ]) = Right (Known False)
      | otherwise = case [ part | part <- combined, not (isKnown part) ] of
          []     -> Right (Known True)
          [part] -> Right part
          parts'
            | not (null [ () | Counted {} <- parts' ]) -> conjunction =<< mapM close parts'
            | otherwise -> Right $ Decision $ foldl1 MCDC.And [ d | Decision d <- parts' ]
      where
        counted = Map.fromListWith (zipWith (&&)) [ (c, table) | Counted c table <- parts ]
        combined = [ Counted c table | (c, table) <- Map.toList counted ] ++ [ part | part <- parts, not (isCounted part) ]

    isKnown (Known _) = True
    isKnown _         = False

    isCounted (Counted {}) = True
    isCounted _            = False

    -- a count becomes a constant, or a decision on the elements of the list
    close :: Opened -> Either String Opened
    close (Counted count table)
      | and table || not (or table) = Right (Known (and table))
      | otherwise = case count of
          Length _ (Filter x cond xs) -> do
            elements <- mapM (close <=< open) (elementConditions n x cond xs)
            decisions <- forM elements $ \element -> case element of
              Decision d -> Right d
              _          -> Left $ "the condition of a count of list elements is a constant, in " ++ show (Expr count)
            Right (Decision (MCDC.Count table decisions))
          _ -> Left "MCDCSTS.openGuard: not a count" -- unreachable: 'isCount' holds
    close opened = Right opened

-- | Convert a row to a guard: the conjunction of its literals.
rowGuard :: MCDC.Row (ExprView Bool) -> SymGuard
rowGuard row = sAnd $ Set.fromList [ literal a v | (a, v) <- Map.toList row ]
  where
    literal a True  = Expr a
    literal a False = sNot (Expr a)

-- | Convert a decision back to a guard.
decisionGuard :: MCDC.Expr (ExprView Bool) -> SymGuard
decisionGuard (MCDC.Atom a)  = Expr a
decisionGuard (MCDC.Not e)   = sNot (decisionGuard e)
decisionGuard (MCDC.And x y) = decisionGuard x .&& decisionGuard y
decisionGuard (MCDC.Or x y)  = decisionGuard x .|| decisionGuard y
decisionGuard (MCDC.Count table es) = foldr (.||) sFalse [ holding .== sConst k | (k, True) <- zip [0 ..] table ]
  where
    holding = sSum $ FMX.fromOccurListT [ (sIfThenElse (decisionGuard e) (sConst 1) (sConst (0 :: Integer)), 1) | e <- es ]

{- |
    A guard as it is on lists of length @n@: opened like the rows of that
    length, so without conditions on all elements of a list. The solver can
    compare this with a row, which is on the elements of the list. The side
    conditions of the guard are kept as they are.

    The guard is not changed if it has no opened list, or an opened list other
    than the given ones, which are the lists that have length @n@.
-}
guardAtLength :: Int -> Set.Set (Some Variable) -> Set.Set (ExprView Bool) -> Set.Set (ExprView Integer) -> SymGuard
              -> SymGuard
guardAtLength n params domain lists guard
  | Set.null ownLists || not (ownLists `Set.isSubsetOf` lists) = guard
  | otherwise = case openGuard n params (view decided) of
      Right (Known b)    -> if b then side else sFalse
      Right (Decision d) -> decisionGuard d .&& side
      _                  -> guard
  where
    ownLists = openLists params (view guard)
    (side, decided) = sideConditions params domain guard

-- | An MC/DC row of a guard as a guard, with its outcome. A false row has the
-- atoms that it is the false row of an independence pair for: flipping such an
-- atom gives a true row. A row of a guard on lists has the length of the lists.
-- The last part is the value of each atom on the row, in the order of the guard.
type GuardRow = (SymGuard, Bool, [ExprView Bool], Maybe Int, [(ExprView Bool, Bool)])

{- |
    The unique-cause MC/DC rows of a guard. A guard without list parameters
    with @N@ atoms has @N+1@ rows.

    A guard on a list parameter of the given gate parameters is opened once for
    each of the given list lengths, with the atoms of each element as separate atoms. 
    Each row also fixes the length of the list.

    The side conditions of a guard, such as the uniqueness of the elements and the 
    domain conjuncts, are not part of the MC/DC decision. They are added to each row.
-}
guardRows :: [Int] -> Set.Set (Some Variable) -> Set.Set (ExprView Bool) -> SymGuard -> Either String [GuardRow]
guardRows lengths params domain guard
  | view guard == Const True = Right [(guard, True, [], Nothing, [])] -- no decision to cover: its own single true row
  | Set.null lists           = if view side == Const True then rowsFor guard guard id Nothing 0
                                                           else rowsFor decided side (.&& side) Nothing 0
  | otherwise               = concat <$> mapM (\n -> rowsFor decided (hasLength n .&& side) (atLength n . (.&& side)) (Just n) n) lengths
  where
    lists = openLists params (view guard)
    (side, decided) = sideConditions params domain guard
    hasLength n = sAnd $ Set.map (\len -> Expr len .== sConst (toInteger n)) lists
    -- the elements of a row do not exist in a shorter list, so they are only evaluated on a list of this length
    atLength n row = sIfThenElse (hasLength n) row sFalse
    rowsFor decision always wrap len n = do
      -- a guard with side conditions only has no decision to cover
      opened <- if view decision == Const True then Right (Known True) else openGuard n params (view decision)
      case opened of
        Known True  -> Right [(always, True, [], len, [])]
        Known False -> Right []
        Counted {}  -> Left "MCDCSTS.guardRows: count is not closed" -- unreachable: 'openGuard' closes counts
        Decision opened' -> do
          rows <- MCDC.mcdcRows opened'
          let trueRows = Set.fromList [ row | (row, True) <- rows ]
              causes row = [ a | a <- Map.keys row, Map.adjust not a row `Set.member` trueRows ]
              values row = [ (a, v) | a <- MCDC.atoms opened', v <- Foldable.toList (Map.lookup a row) ]
          return [ (wrap (rowGuard row), value, if value then [] else causes row, len, values row) | (row, value) <- rows ]

{- |
    Split a guard into its unique-cause MC/DC rows, for the given lengths of
    the lists in the given gate parameters. The result is @(true rows, false rows)@. 
    E.g. @x > 1 || y > 1@ gives

    > ([x > 1 && not (y > 1), not (x > 1) && y > 1], [not (x > 1) && not (y > 1)])
-}
splitGuard :: [Int] -> [Some Variable] -> SymGuard -> Either String ([SymGuard], [SymGuard])
splitGuard lengths params guard = do
  rows <- guardRows lengths (Set.fromList params) Set.empty guard
  return ([ row | (row, True, _, _, _) <- rows ], [ row | (row, False, _, _, _) <- rows ])

-- | The list lengths that 'completeMCDC' opens the list parameters for.
-- TODO: This is a temporary workaround. The correct thing would be to infere the possible lengths based
-- on the length guard (if existent) or other guards.
defaultListLengths :: [Int]
defaultListLengths = [0 .. 3]

-- | 'completeMCDCWith' for lists of the 'defaultListLengths'.
completeMCDC
  :: (Ord loc, Show loc, Ord i, Show i, Ord o, Show o, BoundedMonad m, Foldable m,
      MeetSemiLattice (m (STStdest, loc)))
  => STS m loc (IOAct i o) -> [i] -> IO (STS m loc (IOAct i o))
completeMCDC = completeMCDCWith defaultListLengths

-- | 'completeMCDCReportWith' without the report.
completeMCDCWith
  :: (Ord loc, Show loc, Ord i, Show i, Ord o, Show o, BoundedMonad m, Foldable m,
      MeetSemiLattice (m (STStdest, loc)))
  => [Int] -> STS m loc (IOAct i o) -> [i] -> IO (STS m loc (IOAct i o))
completeMCDCWith lengths aut inputGates = fst <$> completeMCDCReportWith SplitEverywhere lengths [] aut inputGates

-- | 'completeMCDCReportWith' for lists of the 'defaultListLengths'.
completeMCDCReport
  :: (Ord loc, Show loc, Ord i, Show i, Ord o, Show o, BoundedMonad m, Foldable m,
      MeetSemiLattice (m (STStdest, loc)))
  => STS m loc (IOAct i o) -> [i] -> IO (STS m loc (IOAct i o), MCDCReport)
completeMCDCReport = completeMCDCReportWith SplitEverywhere defaultListLengths []

-- | The locations at which 'completeMCDCReportWith' splits the switches of a guard.
data SplitMode
  = SplitEverywhere -- ^ every location
  | SplitInitial    -- ^ the locations of the initial configuration only
  deriving (Eq, Show)

-- | What happened to an MC/DC row of a guard.
data RowStatus
  = Added      -- ^ a true row: a switch is added for it
  | NoSolution -- ^ no values satisfy the row; a true row still has its switch, but no test can take it
  | Covered    -- ^ a false row that is covered by the other switches on the gate
  | NotCovered -- ^ a false row that is underspecified, so no test exercises it
  | Skipped    -- ^ a false row for atoms without a gate parameter: a test can not choose their value
  deriving (Eq, Ord, Show)

-- | An MC/DC row of a guard.
data RowReport = RowReport
  { rowLength  :: Maybe Int          -- ^ the length of the lists, for a guard on list parameters
  , rowValues  :: [(SymGuard, Bool)] -- ^ the value of each atom, in the order of the guard
  , rowOutcome :: Bool               -- ^ the value of the guard on the row
  , rowCauses  :: [SymGuard]         -- ^ for a false row, the atoms that it is the false row of an independence pair for
  , rowStatus  :: RowStatus
  } deriving (Eq, Ord)

-- | The MC/DC rows of the guard of a switch. Switches with the same gate,
-- guard and rows are reported once.
data GuardReport = GuardReport
  { reportGate         :: String
  , reportGuard        :: SymGuard
  , reportSwitches     :: [(String, String)] -- ^ the source and destination location of each split switch with this guard
  , reportEmptyLengths :: [Int]              -- ^ the list lengths for which the guard does not hold for any list
  , reportRows         :: [RowReport]
  } deriving (Eq, Ord)

-- | The rows of all switches that 'completeMCDCReportWith' has split.
newtype MCDCReport = MCDCReport [GuardReport]

{- |
    Show a report as one truth table per guard and list length, with a row per
    MC/DC row and a column per atom, and a summary of the rows that have no
    solution and the false rows that are not covered.
-}
prettyMCDCReport :: MCDCReport -> String
prettyMCDCReport (MCDCReport guards) = unlines $ concatMap prettyGuard guards ++ [summary]
  where
    names = [ "c" ++ show k | k <- [1 :: Int ..] ]

    prettyGuard g =
      [ "gate " ++ reportGate g ++ ", guard " ++ show (reportGuard g)
      , "  " ++ splitAt' (reportSwitches g) ++ " split into " ++ show (switchesFor g) ++ " switch(es)"
      ] ++
      concatMap section (groupBy ((==) `on` rowLength) (reportRows g)) ++
      [ "  length " ++ show n ++ ": the guard does not hold for any list" | n <- reportEmptyLengths g ] ++
      [ "" ]

    section [] = []
    section rows@(r : _) =
      [ "  length " ++ show n ++ ":" | Just n <- [rowLength r] ] ++
      case map fst (rowValues r) of
        []    -> [ "    no conditions, the guard holds: " ++ status [] row | row <- rows ]
        atoms ->
          let named = zip names atoms
              cell row (name, atom) = pad (length name) (maybe "-" truth (lookup atom (rowValues row)))
          in [ "    " ++ name ++ " = " ++ show atom | (name, atom) <- named ] ++
             [ "    " ++ unwords (map fst named) ++ " | out | status" ] ++
             [ "    " ++ unwords (map (cell row) named) ++ " |  " ++ truth (rowOutcome row) ++ "  | " ++ status named row
             | row <- rows ]

    -- the locations of a few switches, the number of many
    splitAt' switches
      | length switches <= 3 = "at " ++ intercalate ", " [ from ++ " -> " ++ to | (from, to) <- switches ] ++ ","
      | otherwise            = show (length switches) ++ " switch(es), each"

    truth True  = "T"
    truth False = "F"

    pad width s = s ++ replicate (width - length s) ' '

    status named row = case rowStatus row of
      Added      -> "added"
      NoSolution -> if rowOutcome row then "added, but no solution" else "no solution"
      Covered    -> "covered" ++ causes
      NotCovered -> "NOT COVERED" ++ causes
      Skipped    -> "skipped, no gate parameter" ++ causes
      where
        causes = case [ name | (name, atom) <- named, atom `elem` rowCauses row ] of
          []  -> ""
          cs  -> " (false row for " ++ intercalate ", " cs ++ ")"

    -- a guard without true rows keeps one switch, that is never taken
    switchesFor g = max 1 (length (filter rowOutcome (reportRows g)))

    count s = length [ () | g <- guards, row <- reportRows g, rowStatus row == s ]

    summary =
      "summary: " ++ show (sum (map (length . reportSwitches) guards)) ++ " switch(es) split into " ++
      show (sum [ length (reportSwitches g) * switchesFor g | g <- guards ]) ++ "; " ++
      show (count NoSolution) ++ " row(s) without solution, " ++
      show (count NotCovered) ++ " false row(s) not covered by any other switch, in " ++
      show (length guards) ++ " distinct guard(s)"

{- |
    Replace each switch on the given input gates by one switch per true row of
    its guard. Each new switch keeps the assignment and the destination.

    With 'SplitInitial', only the switches at the locations of the initial
    configuration are split. The switches at the other locations are kept as
    they are, and they are not in the report.

    A guard on a list parameter of the gate is split once for each of the given
    list lengths, with the atoms of each element of the list as separate atoms. 
    A list of another length is underspecified.

    Use the result to steer test generation, not as a specification: values
    that satisfy the original guard but are not an MCDC row become
    underspecified.

    The false rows of a guard should be covered by the other switches with the
    same gate in the given location. A false row that is not covered is 
    underspecified, so no test exercises it; the report marks it as
    'NotCovered'. Only the parameters of the gate can be controlled by a test,
    so a false row is ignored if the atoms that it is a false row for have no
    gate parameter.

    The report has the rows of each split guard, including the rows that have
    no solution.

    The given domain guards restrict the values of a parameter to its domain,
    such as the range of the elements of a list. A conjunct of a guard that
    is a conjunct of a domain guard is a side condition: it holds on every 
    row and it has no atoms, so no row has a value outside the domain.

    An error is raised if, at a reachable location,

      * an atom occurs more than once in a guard,
      * a guard other than the constant @True@ always holds, or
      * two guards of the same location can hold at the same time.

    Guards of different locations in a configuration may overlap.
-}
completeMCDCReportWith
  :: (Ord loc, Show loc, Ord i, Show i, Ord o, Show o, BoundedMonad m, Foldable m,
      MeetSemiLattice (m (STStdest, loc)))
  => SplitMode -> [Int] -> [SymGuard] -> STS m loc (IOAct i o) -> [i] -> IO (STS m loc (IOAct i o), MCDCReport)
completeMCDCReportWith mode lengths domainGuards aut inputGates = do
  -- the same guards and rows occur at several locations, so each of them is solved once
  solved <- newIORef Map.empty
  let satisfiable guard = do
        known <- Map.lookup guard <$> readIORef solved
        case known of
          Just result -> return result
          Nothing -> do
            result <- isGuardSatisfiable (Set.toList (freeVars guard)) guard
            modifyIORef' solved (Map.insert guard result)
            return result
      configs = Set.toList (reachableConfigs aut)
      selectedGates =
        [ (loc, gate, mval) | loc <- Set.toList (Set.unions configs), (gate, mval) <- Map.toList (transRel aut loc)
                            , selected gate ]
      initLocs = Set.fromList (Foldable.toList (initConf aut))
      isSplit loc = case mode of
        SplitEverywhere -> True
        SplitInitial    -> loc `Set.member` initLocs
  -- check all selected gates first, then split
  unsolvable <- forM selectedGates $ \(loc, gate, mval) -> do
    rows <- checkGate satisfiable (rowsOf gate) loc gate (guards mval)
    return ((loc, gate), rows)
  -- per location and gate, the guards of that gate elsewhere in a configuration; equal checks are done once
  let elsewhereIn config loc gate =
        [ guard | loc' <- Set.toList config, loc' /= loc, mval <- Foldable.toList (Map.lookup gate (transRel aut loc'))
                , guard <- guards mval ]
      coverChecks = Map.fromList
        [ ((loc, gate, Set.fromList (elsewhereIn config loc gate)), config)
        | config <- configs, loc <- Set.toList config, gate <- Map.keys (transRel aut loc), selected gate ]
  uncovered <- forM (Map.keys coverChecks) $ \(loc, gate, elsewhere) -> do
    rows <- checkCovered satisfiable (rowsOf gate) domain (params gate)
      (guards (transRel aut loc Map.! gate)) (Set.toList elsewhere)
    return ((loc, gate), rows)
  let unsolvableAt = Map.fromList unsolvable
      -- a false row is not covered if it is not covered in one of the configurations of the location
      uncoveredAt = Map.fromListWith (zipWith Set.union) uncovered
      rowsAt rows key = Map.findWithDefault (repeat Set.empty) key rows
      -- split switches with the same gate, guard and rows are reported once, with all their locations
      reports = Map.fromListWith (flip (++))
        [ (GuardReport (show gate) guard [] (emptyLengths gate guard rows)
             (zipWith (rowReport (Set.fromList (params gate)) noSolution notCovered) [0 ..] rows), [(show loc, show dest)])
        | (loc, gate, mval) <- selectedGates
        , ((guard, dest), noSolution, notCovered) <-
            zip3 (switches mval) (rowsAt unsolvableAt (loc, gate)) (rowsAt uncoveredAt (loc, gate))
        , isSplit loc
        , Right rows <- [rowsOf gate guard] ]
      report = MCDCReport [ guard { reportSwitches = at } | (guard, at) <- Map.toList reports ]
  return (automaton (initConf aut) (alphabet aut) (\loc -> Map.mapWithKey (splitGate (isSplit loc)) (transRel aut loc)), report)
  where
    selected (SymInteract (In i) _) = i `elem` inputGates
    selected _                      = False

    params (SymInteract _ vars) = vars

    domain = domainConjuncts domainGuards

    rowsOf gate = guardRows lengths (Set.fromList (params gate)) domain

    switches mval = [ (guard, dest) | (STSLoc (guard, _), dest) <- Foldable.toList mval ]

    guards = map fst . switches

    -- the lengths of an opened guard that have no rows
    emptyLengths gate guard rows
      | Set.null (openLists (Set.fromList (params gate)) (view guard)) = []
      | otherwise = [ n | n <- lengths, Just n `notElem` [ len | (_, _, _, len, _) <- rows ] ]

    splitGate split gate mval
      | split && selected gate = mval `ordBind` splitSwitch gate
      | otherwise              = mval

    splitSwitch gate (STSLoc (guard, assign'), destLoc) = case rowsOf gate guard of
      Right rows -> case [ row | (row, True, _, _, _) <- rows ] of
        []       -> ordReturn (stsTLoc sFalse assign', destLoc) -- the guard does not hold for any list of the given lengths
        trueRows -> foldr1 (/\) [ ordReturn (stsTLoc row assign', destLoc) | row <- trueRows ]
      Left err   -> errorWithoutStackTrace $ "completeMCDC: " ++ err -- unreachable after 'checkGate'

{- |
    The location configurations that are syntactically reachable from the
    initial configuration, each as the set of its locations. The successor of a
    configuration for a transition label is the set of all destinations of that
    label from its locations.

    Like 'reachable', this does not interpret the automaton: guards are ignored,
    and so is the lattice structure of a configuration. A configuration may thus
    contain locations that never occur together.
-}
reachableConfigs :: (Ord loc, Ord t, Foldable m) => AutSyntax m loc t tdest -> Set.Set (Set.Set loc)
reachableConfigs aut = explore Set.empty [Set.fromList (Foldable.toList (initConf aut))]
  where
    explore seen [] = seen
    explore seen (config : todo)
      | Set.null config || config `Set.member` seen = explore seen todo
      | otherwise = explore (Set.insert config seen) (Map.elems (configSuccessors aut config) ++ todo)

-- | The successor of a configuration for each transition label.
configSuccessors :: (Ord loc, Ord t, Foldable m) => AutSyntax m loc t tdest -> Set.Set loc -> Map.Map t (Set.Set loc)
configSuccessors aut config = Map.unionsWith Set.union
  [ Map.map (Set.fromList . map snd . Foldable.toList) (transRel aut loc) | loc <- Set.toList config ]

-- | The report of the row with the given index, given the indices of the rows
-- of its guard that have no solution and of those that are not covered.
rowReport :: Set.Set (Some Variable) -> Set.Set Int -> Set.Set Int -> Int -> GuardRow -> RowReport
rowReport params noSolution notCovered k (_, outcome, causes, len, values) =
    RowReport len [ (Expr a, v) | (a, v) <- values ] outcome (map Expr causes) status
  where
    status
      | k `Set.member` noSolution        = NoSolution
      | outcome                          = Added
      | not (controllable params causes) = Skipped
      | k `Set.member` notCovered        = NotCovered
      | otherwise                        = Covered

-- | True if a test can choose the value of one of the atoms that a false row
-- is a false row for: the atom has one of the given gate parameters.
controllable :: Set.Set (Some Variable) -> [ExprView Bool] -> Bool
controllable params causes = null causes || any hasParam causes
  where
    hasParam a = not $ Set.null $ freeVars (Expr a) `Set.intersection` params

-- | Check the guards of one gate at one location, apart from the coverage of
-- their false rows. The result is, per guard, the indices of its rows that
-- have no solution.
checkGate :: (Show loc, Show gate)
          => (SymGuard -> IO Bool) -> (SymGuard -> Either String [GuardRow]) -> loc -> gate -> [SymGuard]
          -> IO [Set.Set Int]
checkGate satisfiable rowsOf loc gate guards = do
    -- a guard that always holds has no false outcome, so no atom of it can have an independence pair
    forM_ indexed $ \(i, guard) -> when (view guard /= Const True) $ do
      falsifiable <- satisfiable (sNot guard)
      unless falsifiable $ failWith $
        "guard #" ++ show i ++ " (" ++ show guard ++ ") is a tautology, so it can not have MC/DC coverage"
    -- the guards must be pairwise disjoint
    forM_ pairs $ \((i, gi), (j, gj)) -> do
      overlap <- satisfiable (gi .&& gj)
      when overlap $ failWith $
        "guard #" ++ show i ++ " (" ++ show gi ++ ") and guard #" ++ show j ++ " (" ++ show gj ++
        ") are not disjoint"
    forM indexed $ \(i, guard) -> case rowsOf guard of
      Left err -> failWith $ "guard #" ++ show i ++ " (" ++ show guard ++ "): " ++ err
      Right rows -> do
        unsolvable <- filterM (fmap not . satisfiable . snd) (zip [0 :: Int ..] [ row | (row, _, _, _, _) <- rows ])
        return (Set.fromList (map fst unsolvable))
  where
    indexed = zip [0 :: Int ..] guards
    pairs = [ (a, b) | a@(i, _) <- indexed, b@(j, _) <- indexed, i < j ]
    failWith :: String -> IO a
    failWith msg = errorWithoutStackTrace $ context ++ msg
    context = "completeMCDC: at location " ++ show loc ++ ", gate " ++ show gate ++ ": "

{- |
    The false rows of the guards of one gate at one location that are not
    covered: neither by the other guards at that location, nor by the given
    guards of that gate elsewhere in the location configuration. The result
    is, per guard, the indices of these rows.

    A false row is skipped if none of the atoms that it is a false row for has
    one of the given gate parameters: its atoms depend on the location variables
    only, so a test can not choose their value.
-}
checkCovered :: (SymGuard -> IO Bool) -> (SymGuard -> Either String [GuardRow]) -> Set.Set (ExprView Bool)
             -> [Some Variable] -> [SymGuard] -> [SymGuard] -> IO [Set.Set Int]
checkCovered satisfiable rowsOf domain params guards elsewhere =
    forM indexed $ \(i, guard) -> case rowsOf guard of
      Left _ -> return Set.empty -- unreachable after 'checkGate'
      Right rows -> do
        let others = [ g | (j, g) <- indexed, j /= i ] ++ elsewhere
            lists = openLists paramSet (view guard)
            -- on a row for lists of some length, the other guards are compared as they are on lists of that length
            othersAt len = map (maybe id (\n -> guardAtLength n paramSet domain lists) len) others
            outsideOthers (row, _, len)
              | null others = row
              | otherwise   = row .&& sNot (foldl1 (.||) (othersAt len))
            falseRows = [ (k, (row, causes, len)) | (k, (row, False, causes, len, _)) <- zip [0 :: Int ..] rows
                                                  , controllable paramSet causes ]
        uncovered <- filterM (satisfiable . outsideOthers . snd) falseRows
        return (Set.fromList (map fst uncovered))
  where
    indexed = zip [0 :: Int ..] guards
    paramSet = Set.fromList params
