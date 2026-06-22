{- |
   Non-deterministic model definitions, where observable behaviour may lead to a set of states.
   These are equivalent to using Lattices with only `(\/)`, and defined in this separate module
   because `(/\)` is more often the intended meaning.
-}
module Lattest.Model.Internal.NonDeterministic (
  NonDet(..),
  nonDet,
  nonDetConcTransFromListRel
) where
import qualified Data.Set as Set
import Lattest.Model.BoundedMonad (BoundedConfiguration (..), BooleanConfiguration (..), JoinSemiLattice (..), OrdFunctor (..), OrdMonad (..))
import Lattest.Model.Symbolic.Expr (sOr, sTrue)
import Lattest.Model.Automaton (Completable (..))
import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.OrdMonad ((<#>))
import qualified Data.Map as Map

-- | Non-deterministic state configuration. This means that an automaton non-deterministically in a number of states, where zero states indicates the forbidden configuration, or in an explicit underspecified configuration.
data NonDet q = NonDet (Set.Set q) | UnderspecNonDet

nonDet :: Ord q => [q] -> NonDet q
nonDet = NonDet . Set.fromList

instance BoundedConfiguration NonDet where
    isForbidden (NonDet s) = Set.null s
    isForbidden _ = False
    isUnderspecified UnderspecNonDet = True
    isUnderspecified _ = False
    forbidden = NonDet Set.empty
    underspecified = UnderspecNonDet

instance OrdFunctor NonDet where
    ordMap f (NonDet ss) = NonDet $ ordMap f ss
    ordMap _ UnderspecNonDet = UnderspecNonDet

instance OrdMonad NonDet where
    ordBind (NonDet ss) f = foldr (\/) (NonDet Set.empty) $ Set.map f ss
    ordBind UnderspecNonDet _ = UnderspecNonDet
    ordReturn s = NonDet $ Set.singleton s

instance Foldable NonDet where
    foldr f q (NonDet qs) = foldr f q qs
    foldr _ q _ = q

instance Show a => Show (NonDet a) where
    show (NonDet a)
        | Set.null a = "⊥"
        | otherwise = show $ Set.toList a
    show UnderspecNonDet = "⊤"

instance Ord a => Eq (NonDet a) where
    UnderspecNonDet == UnderspecNonDet = True
    (NonDet q1) == (NonDet q2) = q1 == q2
    _ == _ = False

instance Ord a => Ord (NonDet a) where
    _ <= UnderspecNonDet = True
    UnderspecNonDet <= _ = False
    (NonDet q1) <= (NonDet q2) = q1 <= q2

instance (Ord a) => JoinSemiLattice (NonDet a) where
    (\/) (NonDet q1) (NonDet q2) = NonDet (Set.union q1 q2)
    (\/) _ _ = UnderspecNonDet -- underspecification acts as top, so is absorbing w.r.t. join

instance BooleanConfiguration NonDet where
    asExpr (NonDet qs) = sOr qs
    asExpr UnderspecNonDet = sTrue

{- |
    Create a non-deterministic concrete transition relation from an explicit list of tuples, with the destination of transitions expressed as lists of locations,
    where the empty list is mapped to either `forbidden` or `underspecified`, depending on the transition label.
    Having multiple occurrences of a transition label is interpreted as non-deterministic choice between the destinations.
-}
nonDetConcTransFromListRel :: (Completable t, Ord loc, Ord t) => [(loc, t, [loc])] -> (loc -> Map t (NonDet ((), loc)))
nonDetConcTransFromListRel = fromJust <$> transFromRelWith (\x y -> Just (x \/ y)) vacuousTrans listToNonDet
    where
    listToNonDet list@(_:_) () _ = vacuousLoc <#> NonDet (Set.fromList list)
    listToNonDet [] () t = implicitDestination t

transFromRelWith :: (Ord loc, Ord t) =>
    (m (tdest, loc) -> m (tdest, loc) -> Maybe (m (tdest, loc))) -- the way of combining the monadic transitions resulting from two list elements, or Nothing if they cannot be combined
    -> (te -> (loc, t, tdest, loc')) -- the way of creating a 4-tuple with all the transition info from a list element
    -> (loc' -> tdest -> t -> m (tdest, loc)) -- the way of creating a monadic transition result from the transition info of a list element
    -> [te] -- the transition relation in a list representation
    -> Maybe (loc -> Map t (m (tdest, loc))) -- a transition function, or Nothing if combining two monadic transitions failed
transFromRelWith c' fe' f' trans = do
    tMapMap <- foldr (addToMap c' fe' f') (Just Map.empty) trans -- map from locations to a map from transitions to Dets
    Just $ \loc -> case loc `Map.lookup` tMapMap of
        Just tMap -> tMap
        Nothing -> Map.empty
    where
    addToMap :: (Ord loc, Ord t) => (m (tdest, loc) -> m (tdest, loc) -> Maybe (m (tdest, loc))) -> (te -> (loc, t, tdest, loc')) -> (loc' -> tdest -> t -> m (tdest, loc)) -> te -> Maybe (Map loc (Map t (m (tdest, loc)))) -> Maybe (Map loc (Map t (m (tdest, loc))))
    addToMap c fe f te maybeTMapMap = do
        tMapMap <- maybeTMapMap
        let (loc, t, tdest, loc') = fe te
        case loc `Map.lookup` tMapMap of
            Just tMap -> case t `Map.lookup` tMap of
                Nothing -> Just $ Map.insert loc (Map.insert t (f loc' tdest t) tMap) tMapMap
                Just prevLoc -> do
                    combinedLoc <- c prevLoc $ f loc' tdest t
                    Just $ Map.insert loc (Map.insert t combinedLoc tMap) tMapMap
            Nothing -> Just $ Map.insert loc (Map.singleton t (f loc' tdest t)) tMapMap

vacuousTrans :: (a, b, d) -> (a, b, (), d)
vacuousTrans (a,b,c) = (a,b,(),c)

vacuousLoc :: b -> ((), b)
vacuousLoc l = ((), l)

