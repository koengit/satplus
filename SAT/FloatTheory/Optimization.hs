
module SAT.FloatTheory.Optimization (
  nloptSat
  ) where

import qualified SAT.FloatTheory.NLOPTBindings as Opt
import qualified Data.Vector.Storable as V
import qualified Data.Vector as OV
import qualified System.Exit as E
import qualified Data.Vector.Storable.Mutable as MV
import qualified Data.Map as Map
import Control.Monad (when, forM, forM_)


import qualified SAT
import qualified SAT.FloatTheory.Interval as I
import SAT.FloatTheory.Constraints
import SAT.FloatTheory.Model
import SAT.FloatTheory.HullConsistency

alg = Opt.LD_SLSQP
type DVec = V.Vector Double

checkReturn :: Opt.Result -> IO ()
checkReturn c = when (not $ Opt.isSuccess c) $ do
  putStrLn $ "NLOPT error '" ++ show c ++ "'!"
  E.exitFailure

optF :: (DVec -> Double) -> (DVec -> DVec) -> Opt.ScalarFunction ()
optF xf gf x grad () = do
  case grad of
    Just grad -> V.copy grad (gf x)
    Nothing -> return ()
  return (xf x)

c_ineq :: Opt.Opt -> (DVec -> Double) -> (DVec -> DVec) -> IO ()
c_ineq opt f g = do
  let ineq1 = optF f g
  (=<<) checkReturn $ Opt.add_inequality_constraint opt ineq1 () ctol
  return ()

c_eq :: Opt.Opt -> (DVec -> Double) -> (DVec -> DVec) -> IO ()
c_eq opt f g = do
  let eq1 = optF f g
  (=<<) checkReturn $ Opt.add_equality_constraint opt eq1 () ctol
  return ()

ctol = 1e-8
xtol = 1e-8

nloptSat :: Box -> FloatExpr -> [FloatConstraint] -> IO FloatModel
nloptSat x0box objective constraints = do

  let numVars     = OV.length x0box
  let lowerBounds = V.fromList $ map I.lowerBound $ OV.toList x0box
  let upperBounds = V.fromList $ map I.upperBound $ OV.toList x0box
  let x0          = V.fromList $ map I.finiteSample $ OV.toList x0box

  Just opt <- Opt.create alg (fromIntegral numVars)
  Opt.set_lower_bounds opt lowerBounds >>= checkReturn
  Opt.set_upper_bounds opt upperBounds >>= checkReturn

  let objectiveF = optF (\x -> evalFloatExpr x objective)
                        (\x -> evalFloatExprGradient x objective)
  Opt.set_min_objective opt objectiveF () >>= checkReturn

  forM_ constraints $ \c -> do
    let (c_f,t) = case c of
                        CEqz t -> (c_eq, t)
                        CLez t -> (c_ineq, t)
    c_f opt (\x -> evalFloatExpr         x t) 
            (\x -> evalFloatExprGradient x t)

  Opt.set_xtol_rel opt xtol >>= checkReturn
  Opt.set_xtol_abs1 opt xtol >>= checkReturn
  Opt.set_ftol_rel opt xtol >>= checkReturn
  Opt.set_ftol_abs opt xtol >>= checkReturn
  Opt.Output result cost params <- Opt.optimize opt x0

  if not (Opt.isSuccess result) then do
    putStrLn $ "NLOpt warning: " ++ (show result)
  else do
    putStrLn $ "NLOpt OK: " ++ (show result)
  return params
