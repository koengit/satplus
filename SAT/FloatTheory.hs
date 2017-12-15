module SAT.FloatTheory (
  -- Solver object
    newFloatSolver
  , FloatSolver
  , constraint
  , assertConstraint
  -- Solver object options
  , setIntervalPropagationIterations
  , setIntervalPropagationRelativeTolerance
  , setLocalSearchObjectiveRelativeTolerance
  , setLocalSearchObjectiveAbsoluteTolerance
  , setLocalSearchParameterRelativeTolerance
  , setLocalSearchParameterAbsoluteTolerance

  -- Theory terms
  , FloatExpr(..)
  , newFloat
  , number
  , (.+.), (.-.), (.*.)
  , (.==.), (.<=.), (.>=.)
  , square

  -- Call this instead of SAT.solve
  , solveMinimizeFloat
  -- Evaluate expressions when model has been found
  , modelValue
  ) where

import SAT.FloatTheory.Constraints
import SAT.FloatTheory.SolverObject
import SAT.FloatTheory.Solver
