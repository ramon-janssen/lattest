{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
module Lattest.SMT (
  SMT,
  SMTQ,
  SolvableProblem(..),
  addAssertions,
  addAssertionsQ,
  addDeclarations,
  getSolution,
  getSolvable,
  pop,
  push,
  query,
  runSMT,
  Some(..),
  RCSet(..),
  sortOfEqual
) where

import Data.SBV(constrain, SBV, SymVal (..), RCSet(..), Kind (..), Symbolic)
import Data.SBV.Control( CheckSatResult, checkSat, Query)
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBV
import qualified Data.SBV.List as SBV
import qualified Data.SBV.Internals as SBVI -- 'unsafe' internals

import Lattest.Model.Symbolic.Expr(ExprView(..), Variable (..), Valuation (..), Expr, Type (..), Constant (..), (.&&), (.<), sConst, Val (..), withExprConstraints)
import Lattest.Model.Symbolic.Internal.FreeMonoidX
import Lattest.Model.Symbolic.Internal.Sum(SumTerm(..))

import Control.Monad((<=<))
import Control.Monad.State (StateT (..), evalStateT, lift, modify, gets, MonadState (..), runState, State, evalState)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Lattest.Model.Symbolic.Internal.Product (ProductTerm(..))
import Data.Some (Some (..))
import qualified Data.Dependent.Map as DMap
import Data.Constraint.Extras (Has(..))
import Lattest.Model.Symbolic.Internal.ExprDefs (ExprType (..), ExprConstraints, freeVars', Expr (..), withExprConstraints, withExprNumConstraint)
import qualified Data.SBV.Tuple as SBV
import qualified Data.SBV.Either as SBV
import qualified Data.SBV.Set as SBV
import Unsafe.Coerce (unsafeCoerce)


--------------------
-- exported types and functions
-- these define the interface to
-- the SMT backend
--------------------
type  Solution v       =  Map.Map v (Some Constant)
data  SolvableProblem  = Sat
                       | Unsat
                       | Unknown
     deriving (Eq,Ord,Read,Show)
data  SolveProblem v  = Solved (Solution v)
                      | Unsolvable
                      | UnableToSolve
     deriving (Eq,Ord,Read,Show)

type SMTQ = StateT (Map String (Some SBV)) Query
type SMT = StateT (Map String (Some SBV)) Symbolic
type SMT' = State (Map String (Some SBV))

smt'tosmt :: SMT' a -> SMT a
smt'tosmt smt = StateT $ (\f x -> pure $ f x) $ runState smt

smt'tosmtq :: SMT' a -> SMTQ a
smt'tosmtq smt = StateT $ (\f x -> pure $ f x) $ runState smt

runSMT :: SMT a -> IO a
runSMT = SBV.runSMT . flip evalStateT Map.empty

query :: SMTQ a -> SMT a
query = StateT . (\f m -> SBV.query (f m)) . runStateT

getSolution :: [Some Variable] -> SMTQ Valuation
getSolution vs =
  Valuation . foldr DMap.union mempty
  <$> mapM getVarValue vs
  where
    getVarValue :: Some Variable -> SMTQ (DMap.DMap Variable Val)
    getVarValue (Some v@(Variable nm tp)) = do
        sval <- gets (\m -> case m Map.!? nm of
            Nothing -> error $ show nm <> "is not in the map"
            Just (Some (SBVI.SBV x)) -> x)
        (Constant _ c) <- lift $ svalToConstant tp sval
        return $ DMap.singleton v (withExprConstraints tp $ Val c)

svalToConstant :: Type a -> SBVI.SVal -> Query (Constant a)
svalToConstant t s = withExprConstraints t $ Constant t <$> SBV.getValue (SBVI.SBV s)

addAssertions :: [Expr Bool] -> SMT ()
addAssertions = mapM_ (lift . constrain <=< smt'tosmt . exprToSymbolic . view)

addAssertionsQ :: [Expr Bool] -> SMTQ ()
addAssertionsQ = mapM_ (lift . constrain <=< smt'tosmtq . exprToSymbolic . view)

-- This is the reason we have the StateT wrapper in SMT:
-- SBV wants us to keep track of the symbolic variables
-- we get on each declaration, and use them to reference
-- the variable.
addDeclarations :: [Some Variable] -> SMT ()
addDeclarations = mapM_ (\(Some v) -> addDeclaration v)

addDeclaration :: Variable t -> SMT ()
addDeclaration (Variable nm ty) = do
  v <- has @SymVal ty $ lift $ mkvar ty nm
  modify $ Map.insert nm $ Some v
  where
    mkvar :: Type t -> String -> Symbolic (SBV t)
    mkvar = \case
      IntType -> SBV.sInteger
      FloatType -> SBV.sDouble
      RationalType -> SBV.sRational
      BoolType -> SBV.sBool
      UnitType -> SBV.sTuple
      CharType -> SBV.sChar
      ListType t -> withExprConstraints t SBV.sList
      SetType t -> withExprConstraints t SBV.sSet
      TupleType a b -> withExprConstraints a $ withExprConstraints b $ \name -> curry SBV.tuple <$> mkvar a ("fst"<>name) <*> mkvar b ("snd"<>name)
      SumType a b -> withExprConstraints a $ withExprConstraints b SBV.sEither

getSolvable :: SMTQ SolvableProblem
getSolvable = checkSatToSolveProblem <$> lift checkSat

pop, push :: SMTQ ()
pop  = lift $ SBV.pop  1
push = lift $ SBV.push 1

---------------
-- Non-exported functions
---------------

-- The main translation between our Exprs and SBV's Symbolic
exprToSymbolic :: ExprConstraints a => ExprView a -> SMT' (SBV a)
exprToSymbolic v = case v of
  Var (Variable nm _tp) -> gets (\m -> case m Map.!? nm of
      Nothing -> error $ "exprToSymbolic: variable " <> show nm <> " is not declared (declared: " <> show (Map.keys m) <> ")"
      Just (Some (SBVI.SBV x)) -> SBVI.SBV x)
  Const c -> pure $ literal c
  Ite i t e -> SBV.ite <$> go i <*> go t <*> go e
  Equal _ l r -> case sortOfEqual 0.0001 l r of
    -- if there are no doubles, use actual equality
    Equal t l' r' -> withExprConstraints t $ (SBV..==) <$> go l' <*> go r'
    exprview -> go exprview
  Divide      x y -> SBV.sDiv  <$> go x <*> go y
  DivideFloat x y -> case typeOf' x of -- need to split because of overlapping instances in SBV
    RationalType -> (/) <$> go x <*> go y
    FloatType    -> (/) <$> go x <*> go y
    _ -> error "impossible type"
  Modulo x y -> SBV.sMod  <$> go x <*> go y
  Sum t s -> withExprNumConstraint t $ foldOccur (\(SumTerm x) i symY -> (\sX sY -> sX * literal (fromInteger i) + sY) <$> go x <*> symY) (pure $ literal 0) s
  Product t p -> withExprNumConstraint t $ foldOccur (\(ProductTerm x) i symY -> (\x' y -> x' ^ i * y) <$> go x <*> symY) (pure $ literal 1) p
  Length t x -> withExprConstraints t $ SBV.length <$> go x
  Gez i -> withExprConstraints i $ (SBV..>= literal 0) <$> go i
  Not b -> SBV.sNot <$> go b
  And xs -> foldr (\b bs -> (SBV..&&) <$> go b <*> bs) (pure $ literal True) (Set.toList xs)
   -- The below version errors because SBV doesn't properly declare some variable
   -- My best guess is that it's a bug if you use 'and' inside a Query, but I haven't
   -- looked deep enough nor done enough testing to report as a bug.
   -- SBV.and <$> foldr (\b bs -> (SBV..:) <$> go b <*> bs) (pure SBV.nil) (Set.toList xs)
  Concat xs -> SBV.concat <$> go xs
  Cons x xs -> case typeOf' xs of
    ListType t -> withExprConstraints t $ (SBV..:) <$> go x <*> go xs
  Append xs ys -> case typeOf' xs of
    ListType t -> withExprConstraints t $ (SBV.++) <$> go xs <*> go ys
  LElem t x xs -> withExprConstraints t $ SBV.elem <$> go x <*> go xs
  Take i xs -> case typeOf' xs of
    ListType t -> withExprConstraints t $ SBV.take <$> go i <*> go xs
  Drop i xs -> case typeOf' xs of
    ListType t -> withExprConstraints t $ SBV.drop <$> go i <*> go xs
  First t x -> withExprConstraints t $ SBV.fst <$> go x
  Second t x -> withExprConstraints t $ SBV.snd <$> go x
  Pair x y -> case typeOf' (Pair x y) of
    TupleType t1 t2 -> withExprConstraints t1 $ withExprConstraints t2 $
      curry SBV.tuple <$> go x <*> go y
  Head xs -> withExprConstraints (typeOf' xs) $ SBV.head <$> go xs
  Tail xs -> withExprConstraints (typeOf' xs) $ SBV.tail <$> go xs
  ELeft xs -> withExprConstraints (typeOf' xs) $ SBV.sLeft <$> go xs
  ERight xs -> withExprConstraints (typeOf' xs) $ SBV.sRight <$> go xs
  SElem t x xs -> withExprConstraints t $ withExprConstraints (SetType t) $ SBV.member <$> go x <*> go xs
  SInsert x xs -> SBV.insert <$> go x <*> go xs
  Zip a b xs ys -> withExprConstraints a $ withExprConstraints b $ SBV.zip <$> go xs <*> go ys

  -- do-notation makes it easier to massage the functions into the forms that SBV expects
  -- we locally modify the environment to map our placeholder variables to the smtvar we get
  -- SBV requires the functions passed to map/filter/fold to be closed, so the free variables of
  -- the function body are passed explicitly
  Map v@(Variable nm ta) f x -> withExprConstraints ta $ withExprConstraints f $ do
    xs <- go x
    m <- get
    let f' env smtvar = evalState (go f) $ Map.insert nm (Some smtvar) env
    pure $ case closureEnvFor m $ filter (/= Some v) (freeVars' f) of
      Nothing -> SBV.map (f' m) xs
      Just (ClosureEnv env inject) -> SBV.map (SBV.Closure env $ \e -> f' (inject e m)) xs
  Filter v@(Variable nm ta) f x -> withExprConstraints ta $ withExprConstraints f $ do
    xs <- go x
    m <- get
    let f' env smtvar = evalState (go f) $ Map.insert nm (Some smtvar) env
    pure $ case closureEnvFor m $ filter (/= Some v) (freeVars' f) of
      Nothing -> SBV.filter (f' m) xs
      Just (ClosureEnv env inject) -> SBV.filter (SBV.Closure env $ \e -> f' (inject e m)) xs
  -- SBV's own closure instances for foldr/foldl still capture the environment in the generated
  -- function body, so for folds the environment is paired with every list element instead
  Foldr va@(Variable na (ta :: Type a)) vb@(Variable nb (_ :: Type b)) f i x -> withExprConstraints ta $ withExprConstraints f $ do
    xs <- go x
    i' <- go i
    m <- get
    let f' :: Map String (Some SBV) -> SBV a -> SBV b -> SBV b
        f' env smtvara smtvarb = evalState (go f) $ Map.insert na (Some smtvara) $ Map.insert nb (Some smtvarb) env
    pure $ case closureEnvFor m $ filter (`notElem` [Some va, Some vb]) (freeVars' f) of
      Nothing -> SBV.foldr (f' m) i' xs
      Just (ClosureEnv (env :: SBV env) inject) ->
        let f'' :: SBV (env, a) -> SBV b -> SBV b
            f'' ea = let (e, a) = SBV.untuple ea in f' (inject e m) a
        in SBV.foldr f'' i' $ withClosureEnv env xs
  Foldl vb@(Variable nb (_ :: Type b)) va@(Variable na (ta :: Type a)) f i x -> withExprConstraints ta $ withExprConstraints f $ do
    xs <- go x
    i' <- go i
    m <- get
    let f' :: Map String (Some SBV) -> SBV b -> SBV a -> SBV b
        f' env smtvarb smtvara = evalState (go f) $ Map.insert na (Some smtvara) $ Map.insert nb (Some smtvarb) env
    pure $ case closureEnvFor m $ filter (`notElem` [Some va, Some vb]) (freeVars' f) of
      Nothing -> SBV.foldl (f' m) i' xs
      Just (ClosureEnv (env :: SBV env) inject) ->
        let f'' :: SBV b -> SBV (env, a) -> SBV b
            f'' b ea = let (e, a) = SBV.untuple ea in f' (inject e m) b a
        in SBV.foldl f'' i' $ withClosureEnv env xs
  Either (Variable nml tl) (Variable nmr tr) l r e -> withExprConstraints tl $ withExprConstraints tr $ withExprConstraints e $ do
    ei <- go e
    m <- get
    let fl smtvar = flip evalState m $ do
          modify $ Map.insert nml $ Some smtvar
          go l
    let fr smtvar = flip evalState m $ do
          modify $ Map.insert nmr $ Some smtvar
          go r
    pure $ SBV.either fl fr ei
  where
    go :: ExprConstraints a => ExprView a -> SMT' (SBV a)
    go = exprToSymbolic

-- We can't == doubles, and using symbolic equality (===) instead is also not ideal.
-- We should add more decimal types (fixed point? reals?), rename FloatType,
-- and add a note that equality on doubles is not exact.
sortOfEqual :: (Fractional a => a) -> ExprView a -> ExprView a -> ExprView Bool
sortOfEqual range l r = withExprConstraints (Expr l) $ case typeOf' l of
  FloatType -> view $ Expr l - Expr r .< sConst range .&& Expr r - Expr l .< sConst range
  RationalType -> view $ Expr l - Expr r .< sConst range .&& Expr r - Expr l .< sConst range
  TupleType a b -> withExprConstraints a $ withExprConstraints b $ view $
                  Expr (Equal a (First b l) (First b r)) .&& Expr (Equal b (Second a l) (Second a r))
  SumType a b -> withExprConstraints a $ withExprConstraints b $
                  let v1 = Variable "eitherEqualityVarL" a
                      v2 = Variable "eitherEqualityVarL" b
                      v3 = Variable "eitherEqualityVarR" a
                      v4 = Variable "eitherEqualityVarR" b
                  in Either v1 v2
                      (Either v3 v4 (Equal a (Var v1) (Var v3)) (Const False) r)
                      (Either v3 v4 (Const False) (Equal b (Var v2) (Var v4)) r)
                      l
  ListType tp -> withExprConstraints tp $
    let v1 = Variable "mapEqualityVar" (TupleType tp tp)
        v2 = Variable "foldEqualityVar" BoolType
    in Foldr v1 v2 (Equal tp (First tp $ Var v1) (Second tp $ Var v1)) (Const True) $ Zip tp tp l r
  -- the version of sets that SBV supports probably just isn't very useful for Lattest,
  -- so we might just remove them. I'll try to implement this if we decide that we do want to keep RCSets.
  SetType _ -> error "TODO"
  -- For int, bool, char, and unit; just use equality
  _ -> Equal (typeOf' l) l r

-- The free variables of a function body, packed into a single symbolic value, together with 
-- a function that unpacks such a value back into the variable environment.
data ClosureEnv where
  ClosureEnv :: SymVal env => SBV env -> (SBV env -> Map String (Some SBV) -> Map String (Some SBV)) -> ClosureEnv

-- Return Nothing if there are no free variables, in which case the function is already closed.
-- The variables are sorted, so that the same function body always gets the same environment layout.
closureEnvFor :: Map String (Some SBV) -> [Some Variable] -> Maybe ClosureEnv
closureEnvFor m = pack . Set.toAscList . Set.fromList
  where
    pack :: [Some Variable] -> Maybe ClosureEnv
    pack [] = Nothing
    pack [Some v@(Variable nm ty)] = withExprConstraints ty $
      Just $ ClosureEnv (lookupVar v) (\e -> Map.insert nm (Some e))
    pack (Some v@(Variable nm (ty :: Type t)) : vs) = case pack vs of
      Nothing -> pack [Some v]
      Just (ClosureEnv (rest :: SBV r) inject) -> withExprConstraints ty $
        Just $ ClosureEnv (SBV.tuple (lookupVar v, rest)) $ \e ->
          let (x, r) = SBV.untuple e :: (SBV t, SBV r)
          in Map.insert nm (Some x) . inject r
    lookupVar :: Variable t -> SBV t
    lookupVar (Variable nm _) = case m Map.!? nm of
      Nothing -> error $ "closureEnvFor: variable " <> show nm <> " is not declared (declared: " <> show (Map.keys m) <> ")"
      Just (Some (SBVI.SBV x)) -> SBVI.SBV x

-- pair every element of a list with the closure environment
withClosureEnv :: forall env a. (SymVal env, SymVal a) => SBV env -> SBV [a] -> SBV [(env, a)]
withClosureEnv env = SBV.map $ SBV.Closure env (\e (x :: SBV a) -> SBV.tuple (e, x))

checkSatToSolveProblem :: CheckSatResult -> SolvableProblem
checkSatToSolveProblem = \case
  SBV.Sat -> Sat
  SBV.Unsat -> Unsat
  SBV.Unk -> Unknown
  SBV.DSat _ -> Unknown

sbvModelToValuation :: SBVI.SMTModel -> Valuation
sbvModelToValuation = Valuation . foldr f DMap.empty . SBVI.modelAssocs
  where
    f (varname, cv) = go cv $
        \tp x -> DMap.insert (Variable varname tp) $ withExprConstraints tp $ Val x

    go :: SBVI.CV -> (forall t. Type t -> t -> r) -> r
    go cv k = case cv of
      SBVI.CV KBool _ -> k BoolType (SBVI.cvToBool cv)
      SBVI.CV KUnbounded (SBVI.CInteger i) -> k IntType i
      SBVI.CV KDouble (SBVI.CDouble d) -> k FloatType d
      SBVI.CV KChar (SBVI.CChar c) -> k CharType c
      SBVI.CV KString (SBVI.CString s) -> k (ListType CharType) s
      SBVI.CV (KList t) (SBVI.CList xs) -> kindToType t $ \tp -> k (ListType tp) $
        foldr (\x ys -> go (SBVI.CV t x) $ \_ y -> unsafeCoerce y:ys) [] xs
      SBVI.CV (KSet t) (SBVI.CSet s) -> case s of
        RegularSet    xs -> go (SBVI.CV (KList t) (SBVI.CList $ Set.toList xs)) $ \cases
          (ListType tp) ys -> withExprConstraints tp $ k (SetType tp) (RegularSet    $ Set.fromList ys)
          _ _ -> error "impossible"
        ComplementSet xs -> go (SBVI.CV (KList t) (SBVI.CList $ Set.toList xs)) $ \cases
          (ListType tp) ys -> withExprConstraints tp $ k (SetType tp) (ComplementSet $ Set.fromList ys)
          _ _ -> error "impossible"
      SBVI.CV (KTuple [k1, k2]) (SBVI.CTuple [x,y]) -> go (SBVI.CV k1 x) $ \t1 x' -> go (SBVI.CV k2 y) $ \t2 y' -> k (TupleType t1 t2) (x', y')
      SBVI.CV (KTuple []) _ -> k UnitType ()
      SBVI.CV (KADT "Either" _ [("Left", _), ("Right", [rk])]) (SBVI.CADT ("Left", [(k', x)])) -> kindToType rk $ \rty ->
        go (SBVI.CV k' x) $ \tp y -> k (SumType tp rty) (Left y)
      SBVI.CV (KADT "Either" _ [("Left", [lk]), ("Right", _)]) (SBVI.CADT ("Right", [(k', x)])) -> kindToType lk $ \lty ->
        go (SBVI.CV k' x) $ \tp y -> k (SumType lty tp) (Right y)
      SBVI.CV k' _ -> error $ "Couldn't convert " <> show cv <> ", with kind " <> show k'

    -- needed to correctly type empty lists and sets
    kindToType :: Kind -> (forall t. Type t -> r) -> r
    kindToType kind k = case kind of
      KBool -> k BoolType
      KUnbounded -> k IntType
      KDouble -> k FloatType
      KChar -> k CharType
      KString -> k $ ListType CharType
      KList t -> kindToType t $ k . ListType
      KSet t -> kindToType t $ k . SetType
      KTuple [k1, k2] -> kindToType k1 $ \t1 -> kindToType k2 $ \t2 -> k $ TupleType t1 t2
      KTuple [] -> k UnitType
      _ -> error $ "couldn't convert kind " <> show kind


