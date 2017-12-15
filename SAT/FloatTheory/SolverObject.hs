module SAT.FloatTheory.SolverObject (
    newFloatSolver
  , FloatSolver(..)
  , FloatSolverParams(..)
  , newFloat
  , constraint
  , assertConstraint
  , conditionalConstraint

  -- Solver object options
  , setIntervalPropagationIterations
  , setIntervalPropagationRelativeTolerance
  , setLocalSearchObjectiveRelativeTolerance
  , setLocalSearchObjectiveAbsoluteTolerance
  , setLocalSearchParameterRelativeTolerance
  , setLocalSearchParameterAbsoluteTolerance

  , modelValue

  ) where

import SAT.FloatTheory.Constraints
import SAT.FloatTheory.Model
import qualified SAT
import Data.IORef
import qualified Data.Vector.Storable as V

data FloatSolverParams = FloatSolverParams {
  hcIter :: Maybe Int,
  hcRelTol  :: Double,
  searchObjRelTol :: Double,
  searchObjAbsTol :: Double,
  searchParRelTol :: Double,
  searchParAbsTol :: Double
}

data FloatSolver = FloatSolver {
  solverPtr :: SAT.Solver,
  varCounter :: IORef VarId,
  constraints :: IORef [(SAT.Lit, FloatConstraint)],
  backgroundConstraints  :: IORef [FloatConstraint],
  fmodel :: IORef (Maybe FloatModel),
  solverParams :: IORef FloatSolverParams
}

newFloatSolver :: SAT.Solver -> IO FloatSolver
newFloatSolver s = do
  counter <- newIORef 0
  constr <- newIORef []
  bgConstr <- newIORef []
  m <- newIORef Nothing
  params <- newIORef $ FloatSolverParams (Just 10) 1e-5 1e-8 1e-8 1e-8 1e-8
  return (FloatSolver s counter constr bgConstr m params)

newFloat :: FloatSolver -> Double -> Double -> IO FloatExpr
newFloat fs low high = do
  v <- readIORef (varCounter fs)
  modifyIORef (varCounter fs) (+1)
  let r = (TVar v)
  assertConstraint fs (r .>=. (number low))
  assertConstraint fs (r .<=. (number high))
  return r

constraint :: FloatSolver -> FloatConstraint -> IO SAT.Lit
constraint fs c = do
  l <- SAT.newLit (solverPtr fs)
  conditionalConstraint fs l c
  return l

assertConstraint :: FloatSolver -> FloatConstraint -> IO ()
assertConstraint fs c = modifyIORef (backgroundConstraints fs) (c:)

conditionalConstraint :: FloatSolver -> SAT.Lit -> FloatConstraint -> IO ()
conditionalConstraint fs l c = modifyIORef (constraints fs) ((l,c):)
  
setIntervalPropagationIterations :: FloatSolver -> Maybe Int -> IO ()
setIntervalPropagationIterations fs x = modifyIORef (solverParams fs)
  (\(FloatSolverParams a b c d e f) -> FloatSolverParams x b c d e f)
setIntervalPropagationRelativeTolerance :: FloatSolver -> Double -> IO ()
setIntervalPropagationRelativeTolerance fs x = modifyIORef (solverParams fs)
  (\(FloatSolverParams a b c d e f) -> FloatSolverParams a x c d e f)
setLocalSearchObjectiveRelativeTolerance :: FloatSolver -> Double -> IO ()
setLocalSearchObjectiveRelativeTolerance fs x = modifyIORef (solverParams fs)
  (\(FloatSolverParams a b c d e f) -> FloatSolverParams a b x d e f)
setLocalSearchObjectiveAbsoluteTolerance :: FloatSolver -> Double -> IO ()
setLocalSearchObjectiveAbsoluteTolerance fs x = modifyIORef (solverParams fs)
  (\(FloatSolverParams a b c d e f) -> FloatSolverParams a b c x e f)
setLocalSearchParameterRelativeTolerance :: FloatSolver -> Double -> IO ()
setLocalSearchParameterRelativeTolerance fs x = modifyIORef (solverParams fs)
  (\(FloatSolverParams a b c d e f) -> FloatSolverParams a b c d x f)
setLocalSearchParameterAbsoluteTolerance :: FloatSolver -> Double -> IO ()
setLocalSearchParameterAbsoluteTolerance fs x = modifyIORef (solverParams fs)
  (\(FloatSolverParams a b c d e f) -> FloatSolverParams a b c d e x)

modelValue :: FloatSolver -> FloatExpr -> IO Double
modelValue fs t = do
  model <- readIORef (fmodel fs)
  case model of
    Just model -> return (evalFloatExpr model t)
    Nothing -> error "FloatSolver: model has not been found"

