{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

{-|
    This module contains the definitions and semantics of different forms of observable actions, and inputs used in testing experiments.
-}

module Lattest.Model.Alphabet (
-- * Translating between Actions and Inputs
TestChoice,
choiceToActs,
actToChoice,
-- * Action types
-- ** Inputs and Outputs
IOAct(..),
isInput,
isOutput,
fromInput,
maybeFromInput,
fromOutput,
maybeFromOutput,
-- ** Observable Quiescence
{- |
    Observable actions that may be either inputs provided to a system, or outputs from that system, where the 'output' may also be an artificial
    output that represents an observed timeout, /quiescence/. For the theoretical background on observing quiescence, see
    
    * [/Jan Tretmans/, Model based testing with labelled transition systems (Formal Methods and Testing), 2008](https://repository.ubn.ru.nl/bitstream/handle/2066/72680/72680.pdf)
-}
Suspended(..),
δ,
IOSuspAct,
asSuspended,
fromSuspended,
-- TODO decide on refusal or failure and be consistent
-- ** Input Failures
{- |
    'Input failures' model the possibility to accepted or refuse an input by the system under test.
    Failure of an input represents the system being unable to process the given input. For a theoretical background on input failures, see 

    * [/Ramon Janssen/, Refinement and partiality for model-based testing (Doctoral dissertation), 2022, Chapter 3 and 4](https://repository.ubn.ru.nl/bitstream/handle/2066/285020/285020.pdf)
-}
IFAct(..),
InputAttempt(..),
asInputAttempt,
fromInputAttempt,
-- ** Combined Input Failures and Quiescences
SuspendedIF,
asSuspendedInputAttempt,
fromSuspendedInputAttempt,
-- * STS
SymInteract(..),
IOSymInteract,
SymGuard,
GateValue(..),
IOGateValue,
gateValueAsIOAct,
ioActAsGateValue,
maybeFromInputInteraction,
maybeFromOutputInteraction,
isInputGate,
isOutputGate,
isInputInteract,
isOutputInteract,
interactionGate,
valueGate,
IOSuspGateValue,
IFGateValue,
SuspendedIFGateValue,
toIOGateValue
)
where

import qualified Data.Map as Map (Map, fromList, toList, lookup, empty, insert)
import qualified Data.List as List (intercalate)
import Lattest.Model.Symbolic.Expr (Variable(..), VarModel, Valuation, Expr(..), Type(..), assign, Constant(..), constType)
import Data.Aeson(FromJSON, ToJSON)
import GHC.Generics (Generic)

{- |
    If an input type is an 'TestChoice' to a type of observable actions, this means that
    
    * given such an input, it is possible to derive the corresponding observable action, or sequence of actions, and
    * an observable action may (but also may not) correspond to an input.
-}
class TestChoice i act where
    {- |
        If an observable action corresponds to an input, then derive that input.
    -}
    actToChoice :: act -> Maybe i -- the input command that corresponds to given action (ideally, e.g. in case of a waiting time, the observed waiting time may be different than the intended waiting time)
    {- |
        Derive the sequence of observable actions that correspond to an input.
    -}
    choiceToActs :: i -> [act] -- which action(s) an input command corresponds to

{- |
    Observable actions that may be either inputs provided to a system, or outputs from that system.
-}
data IOAct i o = In i | Out o deriving (Eq, Ord)

instance (Show i, Show o) => Show (IOAct i o) where
    show (In i) = "?" ++ show i
    show (Out o) = "!" ++ show o

{- |
    Relates input commands to observable inputs. Note that this instance is not very practical for testing: during testing, a test controller
    is usually asked for inputs, and with this instance, it is not possible to skip selecting an input.
-}
instance TestChoice i (IOAct i o) where
    choiceToActs i = [In i]
    actToChoice (In i) = Just i
    actToChoice (Out _) = Nothing

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
    Unpacks an input.
-}
maybeFromInput :: IOAct i o -> Maybe i
maybeFromInput (In i) = Just i
maybeFromInput _ = Nothing

{- |
    Partially defined function that unpacks an outputs.
-}
fromOutput :: IOAct i o -> o
fromOutput (Out o) = o

{- |
    Unpacks an output.
-}
maybeFromOutput :: IOAct i o -> Maybe o
maybeFromOutput (Out o) = Just o
maybeFromOutput _ = Nothing


{- |
    Add observation of quiescence to a type of observable actions.
-}
data Suspended o = Quiescence | OutSusp o deriving (Eq, Ord)

instance Show o => Show (Suspended o) where
    show Quiescence = "δ"
    show (OutSusp o) = show o

{- |
    Add observation of quiescence to the observed inputs and outputs.
-}
type IOSuspAct i o = IOAct i (Suspended o)

δ :: IOAct i (Suspended o)
δ = Out Quiescence

{- |
    Relates input commands to observable inputs. A 'Nothing' input command, corresponds to observation of an output, which may lead to quiescence.
-}
instance TestChoice (Maybe i) (IOSuspAct i o) where
    -- a (Maybe i) only makes sense in case of quiescence, since testing would otherwise quickly deadlock
    choiceToActs (Just i) = asSuspended <$> choiceToActs i
    choiceToActs Nothing = []
    actToChoice (Out Quiescence) = Just Nothing
    actToChoice (Out (OutSusp o)) = Nothing
    actToChoice (In i) = Just $ Just i

{- |
    Convert an input or output to a type containing quiescence.
-}
asSuspended :: IOAct i o -> IOSuspAct i o
asSuspended (In i) = In i
asSuspended (Out o) = Out (OutSusp o)

{- |
    Partially defined function that unpacks an input or output from a type with quiescence.
-}
fromSuspended :: IOSuspAct i o -> IOAct i o
fromSuspended (In i) = In i
fromSuspended (Out (OutSusp o)) = Out o

-- (i, True) represents a succesful i, (i, False) represents a failed attempt at i
newtype InputAttempt i = InputAttempt (i, Bool) deriving (Eq, Ord)

instance Show i => Show (InputAttempt i) where
    show (InputAttempt (i, True)) = show i
    show (InputAttempt (i, False)) = showFailure (show i)
        where
        showFailure [] = []
        showFailure (c:rest) = c:'\x0305':showFailure rest -- U+0305, combine-symbol for overline

{- |
    Observable actions that may be either inputs provided to a system, or outputs from that system, where the 'inputs' may be refused.
-}
type IFAct i o = IOAct (InputAttempt i) o

{- |
    Relates input commands to observable inputs. An input command corresponds to an accepted input action, and both a refused and accepted input
    command correspond to the same input action.
-}
instance TestChoice i (IFAct i o) where
    choiceToActs i = inToInputAttempt <$> choiceToActs i
        where
        inToInputAttempt(In i) = In (InputAttempt(i, True))
        inToInputAttempt(Out o) = Out o 
    actToChoice = actToChoice . attemptToIn
        where
        attemptToIn (In (InputAttempt(i, _))) = In i
        attemptToIn (Out o) = Out o

{- |
    Convert an input or output to a type containing input failures.
-}
asInputAttempt :: IOAct i o -> IFAct i o
asInputAttempt(In i) = In (InputAttempt(i, True))
asInputAttempt(Out o) = Out o

{- |
    Partially defined function that unpacks an input or output from a type with input failures.
-}
fromInputAttempt :: IFAct i o -> IOAct i o
fromInputAttempt(In (InputAttempt(i, True))) = In i
fromInputAttempt(Out o) = Out o

-- ideally, this could just be defined by stacking IFAct and IOSuspAct to avoid all the boilerplate below, but that is a bit of a hassle
{- |
    Input failure with observed quiescence. See 'IOSuspAct' and 'IFAct' for details.
-}
type SuspendedIF i o = IOAct (InputAttempt i) (Suspended o)

instance TestChoice (Maybe i) (SuspendedIF i o) where
    choiceToActs Nothing = []
    choiceToActs (Just i) = inToInputAttempt <$> choiceToActs i
        where
        inToInputAttempt(In i) = In (InputAttempt(i, True))
        inToInputAttempt(Out o) = Out o 
    actToChoice other = actToChoice $ attemptToIn other
        where
        attemptToIn (In (InputAttempt(i, _))) = In i
        attemptToIn (Out o) = Out o

{- |
    Convert an input or output to a type containing input failures and quiescence.
-}
asSuspendedInputAttempt :: IOAct i o -> SuspendedIF i o
asSuspendedInputAttempt(In i) = In (InputAttempt(i, True))
asSuspendedInputAttempt(Out o) = Out (OutSusp o)

{- |
    Partially defined function that unpacks an input or output from a type with input failures and quiescence.
-}
fromSuspendedInputAttempt :: SuspendedIF i o -> IOAct i o
fromSuspendedInputAttempt(In (InputAttempt(i, True))) = In i
fromSuspendedInputAttempt(Out (OutSusp o)) = Out o


-- STS data types
data SymInteract g = SymInteract g [Variable] deriving (Eq, Ord, Functor)
type IOSymInteract i o = SymInteract (IOAct i o)

interactionGate :: SymInteract g -> g
interactionGate (SymInteract gate _) = gate

instance (Show g) => Show (SymInteract g) where
    show (SymInteract gate vars) = show gate ++ " " ++ show vars

type SymGuard = Expr Bool

data GateValue g = GateValue {gate :: g, values :: [Constant]} deriving (Eq, Ord, Functor, Generic)

instance FromJSON a => FromJSON (GateValue a)
instance ToJSON a => ToJSON (GateValue a)

type IOGateValue i o = GateValue (IOAct i o)

instance (Show g) => Show (GateValue g) where
    show (GateValue gate vals) = show gate ++ if null vals then "" else "" ++ show vals

valueGate :: GateValue g -> g
valueGate (GateValue gate _) = gate

gateValueAsIOAct :: IOGateValue i o -> IOAct (GateValue i) (GateValue o)
gateValueAsIOAct (GateValue (In i) vals) = In (GateValue i vals)
gateValueAsIOAct (GateValue (Out o) vals) = Out (GateValue o vals)

ioActAsGateValue :: IOAct (GateValue i) (GateValue o) -> IOGateValue i o
ioActAsGateValue (In (GateValue i vals)) = GateValue (In i) vals
ioActAsGateValue (Out (GateValue o vals)) = GateValue (Out o) vals

isOutputGate :: IOGateValue i o -> Bool
isOutputGate (GateValue (Out _) _) = True
isOutputGate _ = False

isInputGate :: IOGateValue i o -> Bool
isInputGate (GateValue (In _) _) = False
isInputGate _ = True

isOutputInteract :: IOSymInteract i o -> Bool
isOutputInteract (SymInteract (Out _) _) = True
isOutputInteract _ = False

isInputInteract :: IOSymInteract i o -> Bool
isInputInteract (SymInteract (In _) _) = False
isInputInteract _ = True

maybeFromInputInteraction :: IOSymInteract i o -> Maybe (SymInteract i)
maybeFromInputInteraction (SymInteract gate vars) = case maybeFromInput gate of
    Just i -> Just $ SymInteract i vars
    Nothing -> Nothing

maybeFromOutputInteraction :: IOSymInteract i o -> Maybe (SymInteract o)
maybeFromOutputInteraction (SymInteract gate vars) = case maybeFromOutput gate of
    Just o -> Just $ SymInteract o vars
    Nothing -> Nothing

type IOSuspGateValue i o = IOGateValue i (Suspended o)
type IFGateValue i o = IOGateValue (InputAttempt i) o
type SuspendedIFGateValue i o = IOGateValue (InputAttempt i) (Suspended o)

toIOGateValue :: SuspendedIF (GateValue i) (GateValue o) -> SuspendedIFGateValue i o
toIOGateValue (In (InputAttempt (GateValue i constantsi, bool))) = GateValue (In (InputAttempt (i,bool))) constantsi
toIOGateValue (Out Quiescence) = GateValue (Out Quiescence) []
toIOGateValue (Out (OutSusp (GateValue o constantso))) = GateValue (Out (OutSusp o)) constantso

instance TestChoice (GateValue i) (IOGateValue i o) where
    choiceToActs (GateValue i consts) = [GateValue (In i) consts]
    actToChoice (GateValue (In i) consts) = Just $ GateValue i consts
    actToChoice (GateValue (Out _) _) = Nothing

instance TestChoice (Maybe (GateValue i)) (IOSuspGateValue i o) where
    choiceToActs (Just i) = fmap asSuspended <$> choiceToActs i
    choiceToActs Nothing = []
    actToChoice (GateValue (Out Quiescence) _) = Just Nothing
    actToChoice (GateValue (Out (OutSusp o)) _) = Nothing
    actToChoice (GateValue (In i) values) = Just $ Just $ GateValue i values

instance TestChoice (GateValue i) (IFGateValue i o) where
    choiceToActs i = fmap inToInputAttempt <$> choiceToActs i
        where
        inToInputAttempt(In i) = In (InputAttempt(i, True))
        inToInputAttempt(Out o) = Out o 
    actToChoice = actToChoice . fmap attemptToIn
        where
        attemptToIn (In (InputAttempt(i, _))) = In i
        attemptToIn (Out o) = Out o

instance TestChoice (Maybe (GateValue i)) (SuspendedIFGateValue i o) where
    choiceToActs (Just i) = fmap inToInputAttempt <$> choiceToActs i
        where
        inToInputAttempt(In i) = In (InputAttempt(i, True))
        inToInputAttempt(Out o) = Out o 
    choiceToActs Nothing = []
    actToChoice = actToChoice . fmap attemptToIn
        where
        attemptToIn (In (InputAttempt(i, _))) = In i
        attemptToIn (Out o) = Out o

