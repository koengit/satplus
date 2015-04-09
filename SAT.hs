module SAT
  ( Solver
  , Lit
  , neg
  , pos
  , false, true
  , bool
  , newSolver
  , deleteSolver
  , withNewSolver
  , newLit
  , addClause
  , solve
  , modelValue
  , conflict
  , valueMaybe
  , modelValueMaybe
  )
 where

import qualified MiniSat as M
import Data.IORef
import Data.Maybe( fromMaybe )

------------------------------------------------------------------------

data Lit = Bool Bool | Lit M.Lit
 deriving ( Eq, Ord )

instance Show Lit where
  show (Bool b) = show b
  show (Lit x)  = show x

neg :: Lit -> Lit
neg (Bool b) = Bool (not b)
neg (Lit x)  = Lit (M.neg x)

true, false :: Lit
true  = Bool True
false = Bool False

bool :: Bool -> Lit
bool = Bool

newLit :: Solver -> IO Lit
newLit (Solver s _) = Lit `fmap` M.newLit s

pos :: Lit -> Bool
pos x = x < neg x

------------------------------------------------------------------------

data Solver = Solver M.Solver (IORef (Maybe Lit))

newSolver :: IO Solver
newSolver =
  do s <- M.newSolver
     ref <- newIORef Nothing
     return (Solver s ref)

deleteSolver :: Solver -> IO ()
deleteSolver (Solver s _) =
  do M.deleteSolver s

withNewSolver :: (Solver -> IO a) -> IO a
withNewSolver h = M.withNewSolver (\s -> do ref <- newIORef Nothing; h (Solver s ref))

------------------------------------------------------------------------

addClause :: Solver -> [Lit] -> IO ()
addClause (Solver s _) xs
  | true `elem` xs = do return ()
  | otherwise      = do M.addClause s [ x | Lit x <- xs ]; return ()

solve :: Solver -> [Lit] -> IO Bool
solve (Solver s ref) xs
  | false `elem` xs =
    do writeIORef ref (Just false)
       return False
  
  | otherwise =
    do writeIORef ref Nothing
       M.solve s [ x | Lit x <- xs ]

conflict :: Solver -> IO [Lit]
conflict (Solver s ref) =
  do mx <- readIORef ref
     case mx of
       Nothing -> do xs <- M.conflict s
                     return (map Lit xs)
       Just x  -> do return [x]

------------------------------------------------------------------------

modelValue :: Solver -> Lit -> IO Bool
modelValue s x =
  do mb <- modelValueMaybe s x
     return (fromMaybe (not (pos x)) mb)

modelValueMaybe :: Solver -> Lit -> IO (Maybe Bool)
modelValueMaybe _ (Bool b) =
  do return (Just b)

modelValueMaybe (Solver s _) (Lit x) =
  do M.modelValue s x

------------------------------------------------------------------------

valueMaybe :: Solver -> Lit -> IO (Maybe Bool)
valueMaybe _            (Bool b) = return (Just b)
valueMaybe (Solver s _) (Lit x)  = M.value s x

------------------------------------------------------------------------
