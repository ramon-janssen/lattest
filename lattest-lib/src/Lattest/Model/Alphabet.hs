{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
    This module contains the definitions and semantics of different forms of observable actions, and inputs used in testing experiments.
-}

module Lattest.Model.Alphabet (
-- * Translating between Actions and Inputs
InputCommand,
inputChoiceToActs,
actToInputChoice,
-- * Action types
-- ** Inputs and Outputs
IOAct(..),
isInput,
isOutput,
fromInput,
fromOutput,
-- ** Observable Timeouts
{- |
    Observable actions that may be either inputs provided to a system, or outputs from that system, where the 'output' may also be an artificial
    output that represents an observed timeout. For the theoretical background on observing timeouts, see the notion of /quiescence/ in
    
    * [/Jan Tretmans/, Model based testing with labelled transition systems (Formal Methods and Testing), 2008](https://repository.ubn.ru.nl/bitstream/handle/2066/72680/72680.pdf)
-}
Timeout (..),
δ,
TimeoutIO,
asTimeout,
fromTimeout,
-- TODO decide on refusal or failure and be consistent
-- ** Input Failures
{- |
    For a 'Refusable' type of observable actions, it is possible to decide whether the action was accepted or refused by the system that exhibited
    that observed action. Refusal of an input represents the system being unable to process the given input. This concept is described as an 
    'input failure'. For a theoretical background on input failures, see 

    * [/Ramon Janssen/, Refinement and partiality for model-based testing (Doctoral dissertation), 2022, Chapter 3 and 4](https://repository.ubn.ru.nl/bitstream/handle/2066/285020/285020.pdf)
-}
Refusable,
isAccepted,
IFAct(..),
Attempt(..),
asInputAttempt,
fromInputAttempt,
-- ** Combined Input Refusals and Timeouts
TimeoutIF,
asTimeoutInputAttempt,
fromTimeoutInputAttempt,
-- * STS
SymInteract(..),
SymGuard,
SymAssign,
GateValue(..),
Value,
Gate(..),
Variable
)
where

import Grisette.Core as Grisette
import qualified Data.Map as Map (Map, fromList)

{- |
    The class of observable actions for which it is possible to derive whether the actions are accepted or refused. For types where refusal does not
    make sense, the default implementation is that all actions are accepted.
-}
class Refusable act where
    {- |
        Is the action accepted or refused?
    -}
    isAccepted :: act -> Bool
    isAccepted _ = True

{- |
    If an input type is an 'InputCommand' to a type of observable actions, this means that
    
    * given such an input, it is possible to derive the corresponding observable action, or sequence of actions, and
    * an observable action may (but also may not) correspond to an input.
-}
class Refusable act => InputCommand i act where
    {- |
        If an observable action corresponds to an input, then derive that input.
    -}
    actToInputChoice :: act -> Maybe i -- the input command that corresponds to given action (ideally, e.g. in case of a waiting time, the observed waiting time may be different than the intended waiting time)
    {- |
        Derive the sequence of observable actions that correspond to an input.
    -}
    inputChoiceToActs :: i -> [act] -- which action(s) an input command corresponds to

{- |
    Observable actions that may be either inputs provided to a system, or outputs from that system.
-}
data IOAct i o = In i | Out o deriving (Eq, Ord)

instance (Show i, Show o) => Show (IOAct i o) where
    show (In i) = "?" ++ show i
    show (Out o) = "!" ++ show o

instance {-# OVERLAPS #-} Refusable (IOAct i o)

{- |
    Relates input commands to observable inputs. Note that this instance is not very practical for testing: during testing, a test controller
    is usually asked for inputs, and with this instance, it is not possible to skip selecting an input.
-}
instance InputCommand i (IOAct i o) where
    inputChoiceToActs i = [In i]
    actToInputChoice (In i) = Just i
    actToInputChoice (Out _) = Nothing

{- |
    Is the given action an input?
-}
isInput :: IOAct i o -> Bool
isInput (In _) = True
isInput _ = False

{- |
    Is the given action an output?
-}
isOutput :: IOAct i o -> Bool
isOutput (Out _) = True
isOutput _ = False

{- |
    Partially defined function that unpacks an input.
-}
fromInput :: IOAct i o -> i
fromInput (In i) = i

{- |
    Partially defined function that unpacks an outputs.
-}
fromOutput :: IOAct i o -> o
fromOutput (Out o) = o

{- |
    Add observation of timeouts to a type of observable actions.
-}
data Timeout o = Timeout | TimeoutOut o deriving (Eq, Ord)

instance Show o => Show (Timeout o) where
    show Timeout = "δ"
    show (TimeoutOut o) = show o

{- |
    Add observation of timeouts to the observed inputs and outputs.
-}
type TimeoutIO i o = IOAct i (Timeout o)

δ :: IOAct i (Timeout o)
δ = Out Timeout

{- |
    Relates input commands to observable inputs. A 'Nothing' input command, corresponds to observation of an output, which may lead to a timeout.
-}
instance InputCommand (Maybe i) (TimeoutIO i o) where
    -- a (Maybe i) only makes sense in case of timeout outputs (quiescence), since testing would otherwise quickly deadlock
    inputChoiceToActs (Just i) = asTimeout <$> inputChoiceToActs i
    inputChoiceToActs Nothing = []
    actToInputChoice (Out Timeout) = Just Nothing
    actToInputChoice (Out (TimeoutOut o)) = Nothing
    actToInputChoice (In i) = Just $ Just i

{- |
    Convert an input or output to a type containing timeouts.
-}
asTimeout :: IOAct i o -> TimeoutIO i o
asTimeout (In i) = In i
asTimeout (Out o) = Out (TimeoutOut o)

{- |
    Partially defined function that unpacks an input or output from a type with timeouts.
-}
fromTimeout :: TimeoutIO i o -> IOAct i o
fromTimeout (In i) = In i
fromTimeout (Out (TimeoutOut o)) = Out o

-- (i, True) represents a succesful i, (i, False) represents a failed attempt at i
newtype Attempt i = Attempt (i, Bool) deriving (Eq, Ord)

instance Show i => Show (Attempt i) where
    show (Attempt (i, True)) = show i
    show (Attempt (i, False)) = showFailure (show i)
        where
        showFailure [] = []
        showFailure (c:rest) = c:'\x0305':showFailure rest -- U+0305, combine-symbol for overline

{- |
    Observable actions that may be either inputs provided to a system, or outputs from that system, where the 'inputs' may be refused.
-}
type IFAct i o = IOAct (Attempt i) o

instance {-# OVERLAPS #-} Refusable (IFAct i o) where
    isAccepted (In (Attempt (_, False))) = False
    isAccepted _ = True

{- |
    Relates input commands to observable inputs. An input command corresponds to an accepted input action, and both a refused and accepted input
    command correspond to the same input action.
-}
instance InputCommand i (IFAct i o) where
    inputChoiceToActs i = inToAttempt <$> inputChoiceToActs i
        where
        inToAttempt (In i) = In (Attempt (i, True))
        inToAttempt (Out o) = Out o 
    actToInputChoice = actToInputChoice . attemptToIn
        where
        attemptToIn (In (Attempt (i, _))) = In i
        attemptToIn (Out o) = Out o

{- |
    Convert an input or output to a type containing input failures.
-}
asInputAttempt :: IOAct i o -> IFAct i o
asInputAttempt (In i) = In (Attempt (i, True))
asInputAttempt (Out o) = Out o

{- |
    Partially defined function that unpacks an input or output from a type with input failures.
-}
fromInputAttempt :: IFAct i o -> IOAct i o
fromInputAttempt (In (Attempt (i, True))) = In i
fromInputAttempt (Out o) = Out o

-- ideally, this could just be defined by stacking IFAct and TimeoutIO to avoid all the boilerplate below, but that is a bit of a hassle
{- |
    Input failure with observed timeouts. See 'TimeoutIO' and 'IFAct' for details.
-}
type TimeoutIF i o = IOAct (Attempt i) (Timeout o)

instance InputCommand (Maybe i) (TimeoutIF i o) where
    inputChoiceToActs Nothing = [Out Timeout]
    inputChoiceToActs (Just i) = inToAttempt <$> inputChoiceToActs i
        where
        inToAttempt (In i) = In (Attempt (i, True))
        inToAttempt (Out o) = Out o 
    --actToInputChoice (Out Timeout) = Just Nothing
    actToInputChoice other = actToInputChoice $ attemptToIn other
        where
        attemptToIn (In (Attempt (i, _))) = In i
        attemptToIn (Out o) = Out o

{- |
    Convert an input or output to a type containing input failures and timeouts.
-}
asTimeoutInputAttempt :: IOAct i o -> TimeoutIF i o
asTimeoutInputAttempt (In i) = In (Attempt (i, True))
asTimeoutInputAttempt (Out o) = Out (TimeoutOut o)

{- |
    Partially defined function that unpacks an input or output from a type with input failures and timeouts.
-}
fromTimeoutInputAttempt :: TimeoutIF i o -> IOAct i o
fromTimeoutInputAttempt (In (Attempt (i, True))) = In i
fromTimeoutInputAttempt (Out (TimeoutOut o)) = Out o


-- STS data types

data Gate i o = InputGate i | OutputGate o deriving (Eq, Ord)

type Variable = Grisette.Identifier

data SymInteract i o = SymInteract (Gate i o) [Variable] deriving (Eq, Ord)

type SymGuard = Grisette.SExpr

type SymAssign  = Map.Map Variable Grisette.SExpr

type Value = Grisette.SExpr

data GateValue i o = GateValue (Gate i o) [Value] deriving (Eq, Ord)


