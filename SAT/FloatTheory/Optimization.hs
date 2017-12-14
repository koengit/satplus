
module SAT.FloatTheory.Optimization (
  nloptSat
  ) where

import SAT.FloatTheory.Constraints

import qualified SAT.FloatTheory.NLOPTBindings as Opt
import qualified Data.Vector.Storable as V
import qualified System.Exit as E
import qualified Data.Vector.Storable.Mutable as MV
import qualified Data.Map as Map
import Control.Monad (when, forM, forM_)

import qualified SAT.FloatTheory.Interval as I
import Debug.Trace

data Diff = Diff Double Double deriving (Eq, Show)
constDiff x = Diff x 0
idDiff    x = Diff x 1

diffAdd (Diff x x') (Diff y y') = Diff (x+y) (x'+y')
diffSub (Diff x x') (Diff y y') = Diff (x+(-y)) (x'+(-y'))
diffMul (Diff x x') (Diff y y') = Diff (x*y) (y'*x + x'*y)

alg = Opt.LD_SLSQP


checkReturn :: Opt.Result -> IO ()
checkReturn c = when (not $ Opt.isSuccess c) $ do
  putStrLn $ "NLOPT error '" ++ show c ++ "'!"
  E.exitFailure

optF :: ([Double] -> Double) -> ([Double] -> [Double]) -> Opt.ScalarFunction ()
optF xf gf x grad () = do
  case grad of
    Just grad -> V.copy grad (V.fromList (gf (V.toList x)))
    Nothing -> return ()
  return (xf (V.toList x))

c_ineq :: Opt.Opt -> ([Double] -> Double) -> ([Double] -> [Double]) -> IO ()
c_ineq opt f g = do
  let ineq1 = optF f g
  (=<<) checkReturn $ Opt.add_inequality_constraint opt ineq1 () ctol
  return ()

c_eq :: Opt.Opt -> ([Double] -> Double) -> ([Double] -> [Double]) -> IO ()
c_eq opt f g = do
  let eq1 = optF f g
  (=<<) checkReturn $ Opt.add_equality_constraint opt eq1 () ctol
  return ()

ctol = 1e-8
xtol = 1e-8


nloptSat :: (Show id, Ord id, Show v, Ord v) => Box v -> FExpr v -> [(id, FConstraint v)] -> IO (FloatSatResult v id)
nloptSat x0box objective constraints = do
  let m = Map.toList x0box
  let (vars, bounds) = (map fst m, map snd m) 
  let model x = (Map.fromList (zip vars x))
  Just opt <- Opt.create alg $ fromInteger $ toInteger (length vars)
  putStrLn $ "opt " ++ (show (length vars))
  putStrLn (show $ vars )
  (=<<) checkReturn $ Opt.set_lower_bounds opt $ V.fromList (map I.lowerBound bounds)
  putStrLn $ "lower "  ++ (show ( V.fromList (map I.lowerBound bounds)))
  (=<<) checkReturn $ Opt.set_upper_bounds opt $ V.fromList (map I.upperBound bounds)
  putStrLn $ "upper "  ++ (show ( V.fromList (map I.upperBound bounds)))

  let objectiveF = optF (\x -> traceShowId (evalFExpr (model x) objective))
                        (\x -> traceShowId (evalFExprGradient vars (model x) objective))

  (=<<) checkReturn $ Opt.set_min_objective opt objectiveF ()

  
  putStrLn "obj"

  forM_ constraints $ \(_,c) -> do
    let (c_f,t) = case c of
                        CEqz t -> (c_eq, t)
                        CLez t -> (c_ineq, t)
    c_f opt (\x -> evalFExpr         (model x) t) 
            (\x -> evalFExprGradient vars (model x) t)
    putStrLn "constraint"

  -- Solution tolerance
  (=<<) checkReturn $ Opt.set_xtol_rel opt xtol
  let x0 = [ I.finiteSample (x0box Map.! v) | v <- vars ]
  putStrLn $ "x0: " ++ (show x0)
  Opt.Output result cost params <- Opt.optimize opt (V.fromList x0)
  checkReturn result
  putStrLn $ "Found minimum at f" ++ show params ++ " = " ++ show cost
  putStrLn $ show result

  if (Opt.isSuccess result) then do
    putStrLn "nlopt success"
    return $ Sat $ Map.fromList [(v,val) | (v,val) <- zip vars (V.toList params)]
  else do
    error "nlopt failed"
