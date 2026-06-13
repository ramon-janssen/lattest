{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
    A simple implementation of 'Functor' and 'Monad' with 'Ord' constraints, to make operations on those data types more efficient.
-}

module Data.OrdMonad (
-- * Functors and Monads with Ordering
-- ** Functors with ordering
OrdFunctor,
ordMap,
(<#>),
-- ** Monads with ordering
OrdMonad,
ordBind,
(>>#),
(>#>),
ordKleisliChain,
ordReturn,
ordJoin
)
where

import qualified Data.Set as Set

{-|
    Functors with an additional 'Ord' constraint. The primary use case for the 'OrdFunctor' is to treat data structures like 'Set' as a functor, where the 'Ord'-constraint is used for performance reasons.
    Implementations of 'ordMap' should adhere to the same laws as for 'fmap' for a @'Functor' F@:

    [Identity]    @'ordMap' 'id' == 'id'@
    [Composition] @'ordMap' (f . g) == 'ordMap' f . 'ordMap' g@

    The composition law is only required if the extensionality property of type class 'Eq' holds for the domain of @f@. Effectively, this states
    that 'Eq' should behave like proper equality for @f@, or conversely, if @x '==' y@ and @f x '/=' f y@, then compositionality is not expected to hold.
-}
class OrdFunctor f where
    -- | Map a function over a functorial type, just like 'fmap', but with an additional 'Ord' constraint.
    ordMap :: (Ord b) => (a -> b) -> f a -> f b

-- | An infix synonym for 'ordMap', similar to '<$>'.
(<#>) :: (OrdFunctor f, Ord b) => (a -> b) -> f a -> f b
(<#>) = ordMap

-- | Any 'Functor' is also an 'OrdFunctor', ignoring the 'Ord' constraint..
instance {-# OVERLAPPABLE #-} Functor f => OrdFunctor f where
    ordMap = fmap

{-|
    Monads with an additional 'Ord' constraint. Analogously to how an 'OrdFunctor' specializes a regular 'Functor', 'OrdMonad' uses the 'Ord'-constraint is used for performance reasons.
    Any instance should adhere to the 'Monad' laws, assuming the extensionality property for equality 'Eq'. See 'OrdFunctor' for details.
-}
class (OrdFunctor m) => OrdMonad m where
    -- | Return operation, similar to the standard monadic 'return'. No 'Ord' constraint is present here, as comparing values is not needed for injecting a single value into a monadic type.
    ordReturn :: a -> m a
    -- | Bind operation, using an 'Ord' constraint, similar to the standard monadic bind operation '>>='.
    ordBind :: (Ord b) => m a -> (a -> m b) -> m b

-- | Any 'Monad' is also an 'OrdMonad', ignoring the 'Ord' constraint.
instance {-# OVERLAPPABLE #-} Monad m => OrdMonad m where
    ordBind = (>>=)
    ordReturn = return

-- | Operator notation for `ordBind`, analogous to `>>=`
(>>#) :: (OrdMonad m, Ord b) => m a -> (a -> m b) -> m b
(>>#) = ordBind

-- | Kleisli composion of two Kleisli maps (monadic maps)
(>#>) :: (OrdMonad m, Ord c) => (a -> m b) -> (b -> m c) -> (a -> m c)
(>#>) f g x = f x >># g

-- | Kleisli composition of a sequence of Kleisli maps (monadic maps)
ordKleisliChain :: (OrdMonad m, Ord a) => [a -> m a] -> (a -> m a)
ordKleisliChain fs = foldr (>#>) ordReturn fs


-- | Standard monadic 'join', but with an additional 'Ord' constraint.
ordJoin :: (Ord a, OrdMonad m) => m (m a) -> m a
ordJoin mma = ordBind mma id

-- | 'Set' is the the prototypical 'OrdFunctor' instance. It maps a function over the set elements, deduplicating the results.
instance OrdFunctor Set.Set where
    ordMap = Set.map

-- | 'Set' is the the prototypical 'OrdMonad' instance, where @s \`'ordBind'\` f@ is the set \( \{ x \in s' \mid s' \in f[s] \} \).
instance OrdMonad Set.Set where
    ordBind s f = Set.unions $ Set.map f s
    ordReturn s = Set.singleton s
