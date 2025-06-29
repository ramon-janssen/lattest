{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

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
fromOutput,
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
    For a 'Refusable' type of observable actions, it is possible to decide whether the action was accepted or refused by the system that exhibited
    that observed action. Refusal of an input represents the system being unable to process the given input. This concept is described as an 
    'input failure'. For a theoretical background on input failures, see 

    * [/Ramon Janssen/, Refinement and partiality for model-based testing (Doctoral dissertation), 2022, Chapter 3 and 4](https://repository.ubn.ru.nl/bitstream/handle/2066/285020/285020.pdf)
-}
Refusable,
isAccepted,
IFAct(..),
InputAttempt(..),
asInputAttempt,
fromInputAttempt,
-- ** Combined Input Refusals and Quiescences
SuspendedIF,
asSuspendedInputAttempt,
fromSuspendedInputAttempt,
-- * STS
SymInteract(..),
SymGuard,
SymAssign,
GateValue(..),
Value(..),
Gate(..),
Variable(..),
addTypedVar,
Type(..),
SymExpr(..),
equalTyped,
assignedExpr,
assignment,
noAssignment
)
where

import Grisette.Core as Grisette
import Grisette.SymPrim as GSymPrim
import qualified Data.Map as Map (Map, fromList, toList, lookup, empty)
import qualified Data.List as List (intercalate)

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
    If an input type is an 'TestChoice' to a type of observable actions, this means that
    
    * given such an input, it is possible to derive the corresponding observable action, or sequence of actions, and
    * an observable action may (but also may not) correspond to an input.
-}
class Refusable act => TestChoice i act where
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

instance {-# OVERLAPS #-} Refusable (IOAct i o)

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
    Partially defined function that unpacks an outputs.
-}
fromOutput :: IOAct i o -> o
fromOutput (Out o) = o

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
newtype InputAttempt i = InputAttempt(i, Bool) deriving (Eq, Ord)

instance Show i => Show (InputAttempt i) where
    show (InputAttempt(i, True)) = show i
    show (InputAttempt(i, False)) = showFailure (show i)
        where
        showFailure [] = []
        showFailure (c:rest) = c:'\x0305':showFailure rest -- U+0305, combine-symbol for overline

{- |
    Observable actions that may be either inputs provided to a system, or outputs from that system, where the 'inputs' may be refused.
-}
type IFAct i o = IOAct (InputAttempt i) o

instance {-# OVERLAPS #-} Refusable (IFAct i o) where
    isAccepted (In (InputAttempt(_, False))) = False
    isAccepted _ = True

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
    choiceToActs Nothing = [Out Quiescence]
    choiceToActs (Just i) = inToInputAttempt <$> choiceToActs i
        where
        inToInputAttempt(In i) = In (InputAttempt(i, True))
        inToInputAttempt(Out o) = Out o 
    --actToChoice (Out Quiescence) = Just Nothing
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

data Gate i o = InputGate i | OutputGate o deriving (Eq, Ord)

instance (Show i, Show o) => Show (Gate i o) where
    show (InputGate i) = "In " ++ show i
    show (OutputGate o) = "Out " ++ show o

data Type = IntType | BoolType deriving (Eq, Ord)

instance Show Type where
    show IntType = "Int"
    show BoolType = "Bool"

addTypedVar :: Variable -> Value -> Model -> Model
addTypedVar (Variable v BoolType) (BoolVal w) m = Grisette.insertValue (GSymPrim.typedAnySymbol v :: TypedAnySymbol Bool) w m
addTypedVar (Variable v IntType) (IntVal w) m = Grisette.insertValue (GSymPrim.typedAnySymbol v :: TypedAnySymbol Integer) w m

data Variable = Variable Grisette.Symbol Type deriving (Eq, Ord)

instance Show Variable where
    show (Variable symbol stype) = show symbol ++ ":" ++ show stype

data SymInteract i o = SymInteract (Gate i o) [Variable] deriving (Eq, Ord)

instance (Show i, Show o) => Show (SymInteract i o) where
    show (SymInteract gate vars) = show gate ++ " " ++ show vars

type SymGuard = GSymPrim.SymBool

data SymExpr = BoolExpr SymBool | IntExpr SymInteger

instance Show SymExpr where
    show (BoolExpr e) = show e
    show (IntExpr e) = show e

newtype SymAssign  = SymAssign (Map.Map Variable SymExpr)

assignedExpr :: Variable -> SymAssign -> Maybe SymExpr
assignedExpr v (SymAssign map) = Map.lookup v map

assignment :: [(Variable, SymExpr)] -> SymAssign
assignment = SymAssign . Map.fromList

noAssignment :: SymAssign
noAssignment = SymAssign Map.empty

instance Show SymAssign where
    show (SymAssign map) = "{" ++ (List.intercalate ", " showList) ++ "}"
        where
        showList = showAssign <$> Map.toList map
        showAssign (v,e) = show v ++ ":=" ++ show e

data Value = IntVal Integer | BoolVal Bool deriving (Eq, Ord,Show)

data GateValue i o = GateValue (Gate i o) [Value] deriving (Eq, Ord)

equalTyped :: Variable -> Value -> Bool
equalTyped (Variable _ BoolType) (BoolVal _) = True
equalTyped (Variable _ IntType) (IntVal _) = True
equalTyped _ _ = False

