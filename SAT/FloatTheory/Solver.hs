module SAT.FloatTheory.Solver (
  FloatSatResult(..),
  floatConjSat
  ) where

-- Partial decision of satisfiability of conjunctions of 
-- floating point constraints, with a numerical tolerance.
--
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map (Map)
import Control.Monad (forM, forM_)

import SAT.FloatTheory.Constraints
import SAT.FloatTheory.HullConsistency
import SAT.FloatTheory.Interval (Interval, interval)
import qualified SAT.FloatTheory.Interval as I

data FloatSatResult v id = Sat (FModel v) | Unsat [id] | Unknown (Box v)
  deriving (Show)

nub :: Ord v => [v] -> [v]
nub = Set.toList . Set.fromList

floatConjSat :: (Show id, Ord id, Show v, Ord v) => [FConstraint v] -> [(id, FConstraint v)] -> IO (FloatSatResult v id)
floatConjSat base cs = do
  putStrLn $ " --- "
  putStrLn $ " FloatConjSat with:"
  forM_ base $ \b -> do
     putStrLn $ " b*> " ++ (show b)
  forM_ cs $ \c -> do
    putStrLn $ " c*> " ++ (show c)
  box <- hullConsistency (base ++ (map snd cs))
  -- putStrLn $ "HULL CONSISTENCY: got box " ++ (show box)
  -- error "ok"
  case box of
    Just b -> do
       model <- sample b
       let ok = testModel (map snd cs) model
       case ok of 
         True -> return $ Sat model
         False -> return $ Unknown b
       -- putStrLn $ "floatConjSat: sat, testing model"
       -- result <- resultBox (base ++ (map snd cs)) b
       -- case result of
       --   Just model -> return $ Sat model
       --   Nothing -> return $ Unknown model
    Nothing -> do
       putStrLn $ "floatConjSat: unsat, finding core"
       core <- blackboxUnsatCore hullConsistency splitMid base cs
       -- putStrLn $ "RETURNING CORE " ++ (show core)
       -- forM_ cs $ \c -> do
       --   putStrLn $ " c*> " ++ (show c)
       putStrLn $ "  Core num constraints " ++ (show (length core)) ++ "/" ++ (show (length cs))
       return (Unsat core)

blackboxUnsatCore :: (Show id, Ord id, Show p, Ord p) => ([p] -> IO (Maybe m)) ->
                     ([(id,p)] -> ([(id,p)],[(id,p)])) ->
                     [p] -> [(id,p)] -> IO [id]
blackboxUnsatCore satF split base ps = caseSplit base ps
  where
    -- Assumption: satF (base ++ ps) == Nothing
    -- caseSplit :: [p] -> [(id,p)] -> IO [p]
    caseSplit base ps = do
      -- putStrLn $ "ENTERED caseSplit with base=" ++ (show base) ++ ", ps=" ++ (show ps)
      let (a,b) = split ps
      -- putStrLn $ "split into " ++ (show (a,b))
      if length b == 0 then return (map fst a)
      else do
        -- Try sat base + a
        satA <- satF (base ++ (map snd a))
        case satA of
          Nothing -> caseSplit base a -- base + a is unsat
          Just modelA -> do  -- base + a is SAT with model
            -- Try sat base + b
            satB <- satF (base ++ (map snd b))
            case satB of
              Nothing -> caseSplit base b -- base + b is unsat
              Just modelB -> do
                -- Both a and b are SAT (under base), so minimize each under the other
                coreA <- caseSplit (base ++ (map snd b)) a
                coreB <- caseSplit (base ++ (map snd a)) b
                return $ nub (coreA ++ coreB)

-- TODO get rid of this 
splitMid :: [a] -> ([a],[a])
splitMid l = splitAt (((length l) + 1) `div` 2) l

sample :: (Show v, Ord v) => Box v -> IO (FModel v)
sample m = do
  n <- sequence [do putStrLn $ "sampling " ++ (show v)
                    x <- sampleI v
                    putStrLn $ "  -> " ++ (show (not (isInfinite (I.lowerBound v))))
                    return (k,x)
                 | (k,v) <- Map.toList m ]
  return (Map.fromList n)
  where
    sampleI :: Interval -> IO Double
    sampleI i
-- TODO: remove these cases now that we have finiteSample
      | not (isNaN (I.finiteSample i)) && not (isInfinite (I.finiteSample i)) = return $ I.finiteSample i
      | not (isInfinite (I.lowerBound i)) = return $ I.lowerBound i
      | not (isInfinite (I.upperBound i)) = return $ I.upperBound i
      | I.member 0.0 i = return 0.0
      | otherwise = error "could not sample interval"


-- resultBox :: (Show v, Ord v) => [FConstraint v] -> Box v -> IO (Maybe (FModel v))
-- resultBox cs box = do
--   model <- sample box
--   let test = testModel cs model
--   let g
--         | test      = return $ Just model
--         | otherwise = return $ Nothing
--   g

