{- |
    An unsorted collection of utility functions for working with the IO monad.
-}
module Lattest.Util.IOUtils (
-- * Control flow
ifM_,
ifMM_,
ifM,
ifMM,
whileM,
transformWhile,
doMaybe,
-- * Encoding state in IO monads
statefulIO,
statefulIO'
)
where

import Control.Monad (void)
import GHC.Conc(newTVarIO, readTVar, writeTVar, atomically)

-- | While-loop for monads. Any state passed between loop iterations should be carried by the monad.
whileM :: (Monad m) => m Bool -> m () -> m ()
whileM mb m = ifMM_ mb (m >> whileM mb m)

-- | If-statement for monads, with a monadic condition: if the condition holds, execute the given monad and discard the result, otherwise return ().
ifMM_ :: (Monad m) => m Bool -> m a -> m ()
ifMM_ mb m = do
    b <- mb
    ifM_ b m

-- | If-statement for monads, with a pure condition: if the condition holds, execute the given monad and discard the result, otherwise return ().
ifM_ :: (Applicative m) => Bool -> m a -> m ()
ifM_ b m = if b then void m else pure ()

-- | If-statement for monads, with a monadic condition: if the condition holds, execute the given monad and return the result, otherwise return Nothing.
ifMM :: (Monad m) => m Bool -> m a -> m (Maybe a)
ifMM mb m = do
    b <- mb
    ifM b m

-- | If-statement for monads, with a pure condition: if the condition holds, execute the given monad and return the result, otherwise return Nothing.
ifM :: Applicative m => Bool -> m a -> m (Maybe a)
ifM b m = if b then Just <$> m else pure Nothing

-- | Execute the given Monad, or return () if not present.
doMaybe :: Applicative m => Maybe (m ()) -> m ()
doMaybe (Just m) = m
doMaybe Nothing = pure ()

-- | While-loop for monads with explicit state passing.
transformWhile :: (Monad m) => a -> (a -> m (a, Bool)) -> m a
transformWhile state transformAndPredicate = do
    (state', condition) <- transformAndPredicate state
    if condition
        then transformWhile state' transformAndPredicate
        else return state'

-- | Produce an IO monad that behaves like the given Mealy machine, with separate transition and output functions.
statefulIO :: (q -> i -> q) -> (q -> i -> o) -> q -> IO (i -> IO o)
statefulIO transitionFunction outputFunction initialState = statefulIO' (\q i -> (transitionFunction q i, outputFunction q i)) initialState

-- | Produce an IO monad that behaves like the given Mealy machine, with a combined transition/output function.
statefulIO' :: (q -> i -> (q, o)) -> q -> IO (i -> IO o)
statefulIO' transitionFunction initialState = do
    stateRef <- newTVarIO initialState
    return $ \i -> atomically $ do
        state <- readTVar stateRef
        let (state', output) = transitionFunction state i
        writeTVar stateRef state'
        return output
