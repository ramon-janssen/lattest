module Lib
    ( someFunc
    ) where


import qualified Lattest.Model.Automaton as Aut
import qualified Lattest.Model.Alphabet as Alph
import           Lattest.Model.Alphabet(IOAct(In, Out), GateValue (..))
import           Lattest.Model.Symbolic.Expr
import Lattest.SMT
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Dependent.Map as DMap
import           Lattest.Adapter.StandardAdapters
import           Lattest.Model.StandardAutomata
import           Lattest.Exec.Testing(runSMTTester)
import           Lattest.Exec.StandardTestControllers
import           Lattest.Model.BoundedMonad(Det)
import Lattest.Model.Symbolic.Internal.ExprDefs (Constant(..))

-- silly example to test some data types
-- the SUT just echos the input back as output
-- the tester computes prime numbers, and the set of prime divisors of non-prime numbers

type X = Either Integer (Integer, RCSet Integer)
xtype :: Type X
xtype = SumType IntType (TupleType IntType $ SetType IntType)

xvar :: Variable X
xvar = Variable "x" xtype

xsvar :: Variable ([X], [X])
xsvar = Variable "xs" $ TupleType (ListType xtype) (ListType xtype)

-- Used for the arguments to 'map' and 'either'
mapvar :: Variable X
mapvar = Variable "forMap" xtype
leftvar :: Variable Integer
leftvar = Variable "forEitherL" IntType
rightvar :: Variable (Integer, RCSet Integer)
rightvar = Variable "forEitherR" $ TupleType IntType $ SetType IntType

data Divisibility = Prime | Divisible deriving (Eq, Ord, Show)

primesieve :: IOSTS Det Bool Divisibility ()
primesieve =
    let x = sVar xvar
        xs = sVar xsvar
        echo = Alph.SymInteract (Out ()) [Some xvar]
        -- append the result to the 'done' list
        echoAssign = assignment [xsvar =: sPair (sCons x $ sFirst xs) (sSecond xs)]
        yes = Alph.SymInteract (In Prime) [Some xvar]
        yesguard = sEither leftvar rightvar sTrue sFalse x .&& x .== sHead (sSecond xs)
        -- xs := (fst xs, map
        --   (\a -> either
        --     (\i        -> if i `mod` fromLeft x == 0 then Right (i, {fromLeft x}) else Left i)
        --     (\(i,divs) -> if i `mod` fromLeft x == 0 then Right (i, fromLeft x `Set.insert` divs) else Right (i, divs))
        --     a)
        --   (tail (snd xs)))
        yesassign = assignment [xsvar =: sPair (sFirst xs) $
          let x' = sEither leftvar rightvar (sVar leftvar) 42 x in -- we know that x is Left, because of the guard
          sMap -- map over the tail of the todo list
            mapvar
            (sEither
              leftvar -- this number has not found a divisor yet
              rightvar
              (sIfThenElse (sVar leftvar .% x' .== 0)
                (sRight $ sPair (sVar leftvar) $ sInsert x' sEmptySet) -- found the first divisor of i
                (sLeft $ sVar leftvar)) -- still a prime candidate
              (sIfThenElse (sFirst (sVar rightvar) .% x' .== 0)
                (sRight $ sPair (sFirst $ sVar rightvar) $ sInsert x' $ sSecond $ sVar rightvar) -- found another divisor of i
                (sRight $ sVar rightvar)) -- didn't find new divisor of i
              (sVar mapvar))
            (sTail $ sSecond xs)]
        no = Alph.SymInteract (In Divisible) [Some xvar]
        noguard = sEither leftvar rightvar sFalse sTrue x .&& x .== sHead (sSecond xs)
        noassign = assignment [xsvar =: sPair (sFirst xs) (sTail (sSecond xs))]
        initConf = return False

        transition True = Map.singleton echo $ pure (Aut.stsTLoc sTrue echoAssign, False)
        transition False = Map.fromList
          [ (yes, pure (Aut.stsTLoc yesguard yesassign, True))
          , (no,  pure (Aut.stsTLoc noguard  noassign, True))]
    in automaton initConf (Set.fromList [echo,yes,no]) transition

primesieveInitAssign :: Valuation
primesieveInitAssign = Valuation $ DMap.singleton xsvar $ Val ([], map Left [2..10])

model :: STSIntrp Det Bool (IOAct Divisibility ())
model = interpretSTS primesieve primesieveInitAssign

someFunc :: IO ()
someFunc = do
    -- putStrLn $ Aut.prettyPrintIntrp $ Aut.after model $ GateValue (In Prime) [Some $ CSum (Left 2) IntType $ TupleType IntType $ SetType IntType]

    -- simple adapter that flops between A and B and echos its input
    adap <- pureMealyAdapter
      (\() -> const ())
      (\_ (GateValue m d) -> [GateValue (In m) d, GateValue (Out ()) d])
      ()

    let nrSteps = 18
        randomSeed = 456
        testSelector = randomDataTestSelectorFromSeed randomSeed `untilCondition` stopAfterSteps nrSteps
                        `observingOnly` traceObserver `andObserving` stateObserver `andObserving` inconclusiveStateObserver
    (verdict, (observed, maybeMq)) <- runSMTTester model testSelector adap

    putStrLn $ "verdict: " ++ show verdict
    putStrLn $ "observed: " ++ show observed
    putStrLn $ "final state: " ++ show maybeMq
