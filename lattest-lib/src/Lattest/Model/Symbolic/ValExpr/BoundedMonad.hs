module Lattest.Model.Symbolic.ValExpr.BoundedMonad (

)
where

{-
-- * State configurations
-- ** Deterministic
Det(..),
-- ** Non-deterministic
NonDet(..),
-- ** Distributive lattice
FreeLattice,
atom,
top,
bot,
(/\),
-- * Specifiednesss
Specifiedness(..),
BoundedConfiguration,
specifiedness,
forbidden,
underspecified,
isForbidden,
isUnderspecified,
-- ** Auxiliary Specifiedness functions
isAllowed,
isSpecified,
isIndefinite,
isConclusive,
-- ** Utility types
BoundedMonad,
BoundedApplicative,
BoundedFunctor,
-- ** General non-determinism
JoinSemiLattice,
(\/)
)
-}

import Lattest.Model.Symbolic.ValExpr.ValExprDefs(ValExprBool)
import Lattest.Model.BoundedMonad(Det(..), (NonDet(..), FreeLattice(..))

class ValExprMonad m where
    asValExpr :: m q -> ValExprBool
    asValExprInverted :: m q -> ValExprBool

instance ValExprMonad Det where
    asValExpr (Det q)

data Det q = Det q | ForbiddenDet | UnderspecDet
data NonDet q = NonDet [q] | UnderspecNonDet
newtype FreeLattice a = FreeLattice (Levitated (Free a)) deriving (Eq, Functor, Foldable, Lattice)

