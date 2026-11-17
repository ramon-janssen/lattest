-- | Variables, valuations and assertions shared by the STS test suites.
module Test.Lattest.Util.STSTestUtils (
    pvar,
    qvar,
    xvar,
    stsExampleInitAssign,
    stsExampleInitAssignWith,
    getSTSIntrpState2,
    atLoc,
    assertAfter
    )
where

import Test.HUnit
import qualified Data.Dependent.Map as DMap
import Lattest.Model.Automaton(after, After, AutIntrpr, stateConf, IntrpState(..))
import Lattest.Model.BoundedMonad(FreeLattice, atom)
import Lattest.Model.Symbolic.Expr(Variable(..), Type(..), Valuation(..), Val(..), emptyValuation)

pvar :: Variable Integer
pvar = Variable "p" IntType
qvar :: Variable Integer
qvar = Variable "q" IntType
xvar :: Variable Integer
xvar = Variable "x" IntType

stsExampleInitAssign :: Valuation
stsExampleInitAssign = stsExampleInitAssignWith 0

-- | The valuation with the given initial value of x.
stsExampleInitAssignWith :: Integer -> Valuation
stsExampleInitAssignWith x = Valuation $ DMap.singleton xvar (Val x)

getSTSIntrpState2 :: Integer ->  Integer -> FreeLattice (IntrpState Integer)
getSTSIntrpState2 loc val = atom (IntrpState loc $ stsExampleInitAssignWith val)

-- | The state at the given location of an STS without location variables.
atLoc :: loc -> FreeLattice (IntrpState loc)
atLoc loc = atom (IntrpState loc emptyValuation)

{- |
    Takes a tuple of description, STS model, gate-parameter value pair and expected state and computes
    STS `after` interaction, asserting that the resulting state configuration matches the expected one.
-}
assertAfter :: (After m loc q t tdest act, Ord (m q), Ord q, Show (m q)) =>
    String -> AutIntrpr m loc q t tdest act -> act -> m q -> IO (AutIntrpr m loc q t tdest act)
assertAfter msg intrp act expected = do
    let intrp' = after intrp act
    assertEqual msg expected (stateConf intrp')
    return intrp'
