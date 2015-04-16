{-|
Module      : SAT.Optimize
Description : Finding the optimal solution, according to a specified objective
-}
module SAT.Optimize where

import SAT as S
import SAT.Unary as U
import Data.Maybe( fromJust )
import System.IO( hFlush, stdout )

------------------------------------------------------------------------------
-- * Simple optimization

-- | Like 'solve', but finds the minimum solution, where the objective is a
-- specified unary number. This function does not /commit/ to a
-- solution. If committing is the desired behavior, the user should manually
-- add a clause with @obj .<= k@ afterwards.
solveMinimize :: Solver -> [Lit] -> Unary -> IO Bool
solveMinimize s ass obj =
  fromJust `fmap` solveOptimize s ass obj (\_ -> return True)

-- | Like 'solve', but finds the maximum solution, where the objective is a
-- specified unary number. This function does not /commit/ to a
-- solution. If committing is the desired behavior, the user should manually
-- add a clause with @obj .>= k@ afterwards.
solveMaximize :: Solver -> [Lit] -> Unary -> IO Bool
solveMaximize s ass obj =
  fromJust `fmap` solveOptimize s ass (invert obj) (\_ -> return True)

------------------------------------------------------------------------------
-- * Verbose optimization

-- | A type to specify what to print during optimization
data Verbosity
  = None    -- ^ Print nothing
  | Compact -- ^ Print a compact state, erase afterwards
  | Line    -- ^ Print every output on a separate line
 deriving ( Eq, Ord, Show, Read )

-- | Like 'solveMinimum', but also prints information during optimization.
solveMinimizeVerbose :: Solver -> [Lit] -> Unary -> Verbosity -> IO Bool
solveMinimizeVerbose s ass obj v =
  fromJust `fmap` solveOptimize s ass obj (printOpti v)

-- | Like 'solveMaximum', but also prints information during optimization.
solveMaximizeVerbose :: Solver -> [Lit] -> Unary -> Verbosity -> IO Bool
solveMaximizeVerbose s ass obj v =
  fromJust `fmap` solveOptimize s ass (invert obj) (printOpti' v)
 where
  m = maxValue obj
  printOpti' v (x,y) = printOpti v (m-y,m-x)

printOpti :: Verbosity -> (Int,Int) -> IO Bool
printOpti v (x,y) =
  do case v of
       None    -> do return ()
       Line    -> do putStrLn s
       Compact -> do putStr (s ++ back)
                     hFlush stdout
                     putStr (wipe ++ back)
     return True
 where
  s    = "(" ++ show x ++ "-" ++ show y ++ ")"
  n    = length s
  back = replicate n '\b'
  wipe = replicate n ' '

------------------------------------------------------------------------------
-- * General optimization

-- | The most general optimization function. It supports a callback that at
-- each optimization step can decide whether or not to continue. If the
-- callback says not to continue (by returning False),
-- the result of 'solveOptimize' will be Nothing. It is still possible to
-- read off the best solution found using functions such as 'modelValue'.
--
-- The optimization performs a binary search. The callback function gets the
-- current optimization interval @(minTry,minReached)@ as argument;
-- which are the values of the best value still considered possible
-- (@minTry@) and the best value found so far (@minReached@), respectively.
--
-- This function minimizes. For maximization, use the function 'invert' on
-- the objective first.
solveOptimize :: Solver -> [Lit] {- ^ assumptions -}
                        -> Unary {- ^ objective (for minimization) -}
                        -> ((Int,Int) -> IO Bool) {- ^ callback -}
                        -> IO (Maybe Bool)
solveOptimize s ass obj callback =
  do b <- solve s ass
     if b then
       -- there is a solution; let's optimize!
       let opti minTry minReached | minReached > minTry =
             do cont <- callback (minTry,minReached)
                if cont then
                  do b <- solve s ([ obj .<= i | i <- [minReached-1,minReached-2..k] ] ++ ass)
                     if b then
                       do n <- U.modelValue s obj
                          opti minTry n
                      else
                       do ass' <- conflict s
                          opti (maximum ([i+1 | i <- [k..minReached-1], neg (obj .<= i) `elem` ass'] ++ [k+1])) minReached
                 else
                  -- callback says: give up
                  do return Nothing
            where
             k = (minTry+minReached) `div` 2

           opti _ _ =
             -- optimum reached
             do return (Just True)

        in do n <- U.modelValue s obj
              opti 0 n

      else
       -- no solution
       do return (Just False)

