{- |
    An unsorted collection of utility functions.
-}

module Lattest.Util.Utils (
-- * Boolean operators
(|||),
(&&&),
(||^^),
(&&^^),
-- * Random functions
flipCoin,
takeRandom,
-- * Maybe
takeJusts,
-- * Set
takeArbitrary,
-- * List utils
removeDuplicates
)
where

import Data.Foldable(toList)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List(sort, head, group)
import System.Random(RandomGen, uniformR)
import Control.Monad.Extra((||^), (&&^))

-- | Conjunction lifted to functions.
(&&&) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(&&&) pred1 pred2 b = pred1 b && pred2 b
infixr 3 &&&

-- | Disjunction lifted to functions.
(|||) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(|||) pred1 pred2 b = pred1 b || pred2 b
infixr 2 |||

-- | Conjunction lifted to a doubly nested monad.
(&&^^) :: (Monad m1, Monad m2) => m1 (m2 Bool) -> m1 (m2 Bool) -> m1 (m2 Bool)
(&&^^) mmb1 mmb2 = do
    mb1 <- mmb1
    mb2 <- mmb2
    return $ mb1 &&^ mb2
infixr 3 &&^^

-- | Disjunction lifted to a doubly nested monad.
(||^^) :: (Monad m1, Monad m2) => m1 (m2 Bool) -> m1 (m2 Bool) -> m1 (m2 Bool)
(||^^) mmb1 mmb2 = do
    mb1 <- mmb1
    mb2 <- mmb2
    return $ mb1 ||^ mb2
infixr 3 ||^^

-- | Flip a coin for which the chance of result 'True' is p, where p is clamped to [0,1].
flipCoin :: RandomGen g => g -> Double -> (Bool, g)
flipCoin g p = let (f, g') = uniformR (0.0, 1.0) g in (f < p, g')

-- | Take a random element from the list. Gives an error for the empty list, so the user should check that first.
takeRandom :: RandomGen g => g -> [a] -> (a, g)
takeRandom g list
    | null list = error "takeRandom from empty list"
    | otherwise = let (i, g') = uniformR (0, length list - 1) g in (list !! i, g')

-- | Filter out Nothings from a Foldable of Maybes, and returns only the Justs.
takeJusts :: Foldable f => f (Maybe t) -> [t]
takeJusts maybes = takeJusts' $ toList maybes
    where
    takeJusts' [] = []
    takeJusts' (Just x : xs) = x : takeJusts' xs
    takeJusts' (Nothing : xs) = takeJusts' xs 

-- | Remove an arbitrary element from the given set, and return both that element and the remaining set, or `Nothing` if the given set was empty.
takeArbitrary :: Set a -> Maybe (a, Set a)
takeArbitrary set
    | Set.null set = Nothing
    | otherwise = Just (Set.elemAt 0 set, Set.deleteAt 0 set)

-- | Remove duplicates from a list by sorting, grouping and taking only the first element of each group. Returns ordered and filtered list.
removeDuplicates :: Ord a => [a] -> [a]
removeDuplicates = map head . group . sort

-- | Sequentially compose a number of monadic actions, passing every value of a step to the next step
--(>>*) :: (Monad m, Foldable f) => m a -> f (a -> m a) -> m a
--(>>*) = foldr =<<
--(>>*) x [] = x
--(>>*) x (f:fs) = m a >>= f >>* fs

--infixl 1  >>*