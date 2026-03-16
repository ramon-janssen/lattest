{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Test.Lattest.Model.BoundedMonad (
prop_latticeIsCNF,
LatticeOp
)
where

import Test.QuickCheck
import qualified Lattest.Model.BoundedMonad as BM
import qualified Lattest.Util.Utils as Utils
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as CM
import qualified Debug.Trace as Trace

-- operations for constructing free lattices. The Map of the Bind operation contains keys for exactly all free  variables in the bound lattice
data LatticeOp a = Var a | Top | Bot | Join (LatticeOp a) (LatticeOp a) | Meet (LatticeOp a) (LatticeOp a) | Bind (LatticeOp a) (Map.Map a (LatticeOp a)) deriving (Eq, Ord, Show)

-- the free variables after performing the operations (in case of bind, only the free variables after substitution)
freeVars :: Ord a => LatticeOp a -> Set.Set a
freeVars (Var a) = Set.singleton a
freeVars (Join x y) = freeVars x `Set.union` freeVars y
freeVars (Meet x y) = freeVars x `Set.union` freeVars y
freeVars (Bind _ subs) = Set.unions $ freeVars <$> Map.elems subs
freeVars _ = Set.empty

instance (Arbitrary a, Ord a) => Arbitrary (LatticeOp a) where
    arbitrary = sized arbitrary'
        where
        arbitrary' 0 = oneof [
            Var <$> arbitrary,
            return Top,
            return Bot
            ]
        arbitrary' n = oneof [
            Var <$> arbitrary,
            return Top,
            return Bot,
            CM.liftM2 Join sub sub,
            CM.liftM2 Meet sub sub,
            sub >>= wrapInBind (n - 1)
            ]
            where
                sub = arbitrary' (n - 1)
                wrapInBind n a = Bind a <$> (arbitraryMapping n $ Set.toList $ freeVars a)
                arbitraryMapping n vars = Map.fromList <$> sequence (arbitraryIdPlusLatticeOp n <$> vars)
                arbitraryIdPlusLatticeOp n a = do
                    l <- arbitrary' n
                    return (a, l)
    shrink Top = []
    shrink Bot = []
    shrink (Var _) = [Top, Bot]
    shrink (Join x y) = [Join x' y' | (x', y') <- shrink (x, y)] ++ shrink x ++ shrink y
    shrink (Meet x y) = [Meet x' y' | (x', y') <- shrink (x, y)] ++ shrink x ++ shrink y
    shrink _ = []
    shrink (Bind l subs) = [let subs' = Map.restrictKeys subs (freeVars l') in if Map.null subs then l' else (Bind l' subs') | l' <- shrink l]
                            ++ [Bind l subs' | subs' <- simplifiedSubs]
        where
        simplifiedSubs = [ Map.insert var sub subs | (var,sub) <- Map.toList subs, sub' <- shrink sub ]

constructLattice :: (BM.BoundedConfiguration l, BM.JoinSemiLattice (l a), BM.MeetSemiLattice (l a), BM.OrdMonad l, Ord a) => LatticeOp a -> l a
constructLattice Top = BM.underspecified
constructLattice Bot = BM.forbidden
constructLattice (Var a) = BM.ordReturn a
constructLattice (Join x y) = (constructLattice x) BM.\/ (constructLattice y)
constructLattice (Meet x y) = (constructLattice x) BM./\ (constructLattice y)
constructLattice (Bind l subs) =
    let subs' = Map.map constructLattice subs 
    in (constructLattice l) `BM.ordBind` (subs' Map.!) 

prop_latticeIsCNF :: (Ord a, Show a) => LatticeOp a -> Bool
prop_latticeIsCNF l = 
    let cnf = constructLattice l
        standard = constructLattice l
        outcome = (cnfToLattice $ cnf) == standard
        message = "CNF:\n" ++ show cnf ++ "\n\nstandard:\n" ++ show standard ++ "\n\n"
    in if outcome then True else Trace.trace message False
    where
    cnfToLattice :: BM.FreeLatticeCNF a -> BM.FreeLattice a
    cnfToLattice (BM.FreeLatticeCNF l) = cnfToLattice' l
    cnfToLattice' = Set.foldr mergeConjunct BM.underspecified
    mergeConjunct :: Set.Set a -> BM.FreeLattice a -> BM.FreeLattice a
    mergeConjunct conjunct l = conjunctToLattice conjunct BM./\ l
    conjunctToLattice = Set.foldr mergeDisjunct BM.forbidden
    mergeDisjunct :: a -> BM.FreeLattice a -> BM.FreeLattice a
    mergeDisjunct a l = return a BM.\/ l
















