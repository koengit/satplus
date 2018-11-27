{-|
Module      : SAT
Description : Basic SAT operations

This module provides basic functions for working with Solver objects. A simple
example of typical use is:

@
main :: IO ()
main = do s <- newSolver
          x <- newLit s
          y <- newLit s
          addClause s [neg x, neg y]
          addClause s [x, y]
          b <- solve s []
          if b then
            do putStrLn \"Found model!\"
               a <- modelValue s x
               b <- modelValue s y
               putStrLn (\"x=\" ++ show a ++ \", y=\" ++ show b)
           else
            do putStrLn \"No model found.\"
          deleteSolver s
@
-}
module SAT(
  -- * The Solver object
    Solver
  , newSolver
  , deleteSolver
  , withNewSolver
  , numAssigns
  , numClauses
  , numLearnts
  , numVars
  , numFreeVars
  , numConflicts

  -- * Literals
  , Lit
  , newLit
  , false, true
  , bool
  , neg
  , pos

  -- * Clauses
  , addClause

  -- * Solving
  , solve
  , modelValue
  , modelValueMaybe
  , conflict

  -- * Implied constants
  , valueMaybe
  )
 where

import qualified MiniSat as M
import Data.IORef
import Data.Maybe( fromMaybe )

------------------------------------------------------------------------------
-- The Solver object

-- | The type of a Solver object
data Solver = Solver M.Solver (IORef (Maybe Lit))

-- | Create a Solver object.
newSolver :: IO Solver
newSolver =
  do s <- M.newSolver
     ref <- newIORef Nothing
     return (Solver s ref)

-- | Delete a Solver object. Use only once!
deleteSolver :: Solver -> IO ()
deleteSolver (Solver s _) =
  do M.deleteSolver s

-- | Create a Solver object, and delete when done.
withNewSolver :: (Solver -> IO a) -> IO a
withNewSolver h =
  M.withNewSolver $ \s ->
    do ref <- newIORef Nothing
       h (Solver s ref)

-- | The current number of assigned literals.
numAssigns :: Solver -> IO Int
numAssigns (Solver m _) = M.minisat_num_assigns m

-- | The current number of original clauses.
numClauses :: Solver -> IO Int
numClauses (Solver m _) = M.minisat_num_clauses m

-- | The current number of learnt clauses.
numLearnts :: Solver -> IO Int
numLearnts (Solver m _) = M.minisat_num_learnts m

-- | The current number of variables.
numVars :: Solver -> IO Int
numVars (Solver m _) = M.minisat_num_vars m

numFreeVars :: Solver -> IO Int
numFreeVars (Solver m _) = M.minisat_num_freeVars m

numConflicts :: Solver -> IO Int
numConflicts (Solver m _) = M.minisat_num_conflicts m

------------------------------------------------------------------------------
-- Literals

-- | The type of a literal
data Lit = Bool Bool | Lit M.Lit
 deriving ( Eq, Ord )

instance Show Lit where
  show (Bool b) = show b
  show (Lit x)  = show x

-- | Create a fresh literal in a given Solver.
newLit :: Solver -> IO Lit
newLit (Solver s _) = Lit `fmap` M.newLit s

-- | Constant literal.
true, false :: Lit
true  = Bool True
false = Bool False

-- | Create a constant literal based on a Bool.
bool :: Bool -> Lit
bool = Bool

-- | Negate a literal.
neg :: Lit -> Lit
neg (Bool b) = Bool (not b)
neg (Lit x)  = Lit (M.neg x)

-- | Return the sign of a literal. The sign flips when a literal is negated.
pos :: Lit -> Bool
pos x = x < neg x

------------------------------------------------------------------------------
-- Clauses

-- | Add a clause in a given Solver. (The argument list is thus /disjunctive/.)
addClause :: Solver -> [Lit] -> IO ()
addClause (Solver s _) xs
  | true `elem` xs = do return ()
  | otherwise      = do M.addClause s [ x | Lit x <- xs ]; return ()

------------------------------------------------------------------------------
-- Solving

-- | Try to find a model of all clauses in the given Solver, under the
-- assumptions of the given arguments. (The argument list is thus /conjunctive/.)
-- Returns True if a model was found, False if no model was found.
solve :: Solver -> [Lit] -> IO Bool
solve (Solver s ref) xs
  | false `elem` xs =
    do writeIORef ref (Just true)
       return False

  | otherwise =
    do writeIORef ref Nothing
       M.solve s [ x | Lit x <- xs ]

-- | If the last call to 'solve' returned False: Return the conflict clause
-- that was the reason for the fact that no model was found under the
-- specified assumptions. The conflict clause only contains literals that
-- are negations of the assumptions given to 'solve'. The conflict
-- clause is always logically implied by the current set of clauses.
--
-- For example, if the returned clause is empty, there is a contradiction even
-- without any assumptions.
--
-- This function can be used to implement so-called \'unsatisfiable cores\'.
--
-- There are no guarantees about minimality of the returned clause.
-- (/Only use when 'solve' has previously returned False!/)
conflict :: Solver -> IO [Lit]
conflict (Solver s ref) =
  do mx <- readIORef ref
     case mx of
       Nothing -> do xs <- M.conflict s
                     return (map Lit xs)
       Just x  -> do return [x]

------------------------------------------------------------------------------

-- | If the last call to 'solve' returned True, return the value of
-- the specified literal in the found model.
-- (/Only use when 'solve' has previously returned True!/)
modelValue :: Solver -> Lit -> IO Bool
modelValue s x =
  do mb <- modelValueMaybe s x
     return (fromMaybe (not (pos x)) mb)

-- | If the last call to 'solve' returned True, return the value of
-- the specified literal in the found model, or Nothing if there is a model
-- regardless of the value of this literal.
-- There are no guarantees about when Nothing is returned.
-- (/Only use when 'solve' has previously returned True!/)
modelValueMaybe :: Solver -> Lit -> IO (Maybe Bool)
modelValueMaybe _ (Bool b) =
  do return (Just b)

modelValueMaybe (Solver s _) (Lit x) =
  do M.modelValue s x

------------------------------------------------------------------------------
-- Implied constants

-- | Check whether or not a given literal has received a top-level value
-- in the given Solver. This can happen when the literal is implied to be
-- False or True by the current set of clauses. There are no guarantees about
-- when this actually happens.
valueMaybe :: Solver -> Lit -> IO (Maybe Bool)
valueMaybe _            (Bool b) = return (Just b)
valueMaybe (Solver s _) (Lit x)  = M.value s x

------------------------------------------------------------------------------
