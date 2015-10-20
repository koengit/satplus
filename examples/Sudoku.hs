module Sudoku where



import Data.List

import SAT
import SAT.Equal
import SAT.Val hiding (modelValue)
import qualified SAT.Val as Val



--------------------------------------------------------------------------------
-- Representation

data Sudoku = Sudoku { rows :: [[Maybe Int]] }
 deriving (Show, Eq)

example :: Sudoku
example = Sudoku
    [ [Just 3, Just 6, Nothing,Nothing,Just 7, Just 1, Just 2, Nothing,Nothing]
    , [Nothing,Just 5, Nothing,Nothing,Nothing,Nothing,Just 1, Just 8, Nothing]
    , [Nothing,Nothing,Just 9, Just 2, Nothing,Just 4, Just 7, Nothing,Nothing]
    , [Nothing,Nothing,Nothing,Nothing,Just 1, Just 3, Nothing,Just 2, Just 8]
    , [Just 4, Nothing,Nothing,Just 5, Nothing,Just 2, Nothing,Nothing,Just 9]
    , [Just 2, Just 7, Nothing,Just 4, Just 6, Nothing,Nothing,Nothing,Nothing]
    , [Nothing,Nothing,Just 5, Just 3, Nothing,Just 8, Just 9, Nothing,Nothing]
    , [Nothing,Just 8, Just 3, Nothing,Nothing,Nothing,Nothing,Just 6, Nothing]
    , [Nothing,Nothing,Just 7, Just 6, Just 9, Nothing,Nothing,Just 4, Just 3]
    ]

exampleFalse :: Sudoku
exampleFalse = Sudoku
    [ [Just 1, Just 2, Just 3,Just 7,Just 5, Just 6, Just 4, Just 8,Nothing]
    , [Nothing,Just 5, Nothing,Nothing,Nothing,Nothing,Just 1, Nothing, Nothing]
    , [Nothing,Nothing,Just 9, Just 2, Nothing,Just 4, Just 7, Nothing,Nothing]
    , [Nothing,Nothing,Nothing,Nothing,Just 1, Just 3, Nothing,Just 2, Just 8]
    , [Just 4, Nothing,Nothing,Just 5, Nothing,Just 2, Nothing,Nothing,Just 9]
    , [Just 2, Just 7, Nothing,Just 4, Just 6, Nothing,Nothing,Nothing,Nothing]
    , [Nothing,Nothing,Just 5, Just 3, Nothing,Just 8, Just 9, Nothing,Nothing]
    , [Nothing,Just 8, Just 3, Nothing,Nothing,Nothing,Nothing,Just 6, Nothing]
    , [Nothing,Nothing,Just 7, Just 6, Just 9, Nothing,Nothing,Just 4, Just 3]
    ]

printSudoku :: Sudoku -> IO ()
printSudoku s = putStrLn $ unlines $ map (map cell2char) $ rows s
  where
    cell2char (Just c) = head (show c)
    cell2char Nothing  = '.'



--------------------------------------------------------------------------------
-- Conversion

type Sudoku' = [[Val Int]]

fromSudoku :: Solver -> Sudoku -> IO Sudoku'
fromSudoku sol = mapM (mapM fromCell) . rows
  where
    fromCell Nothing  = newVal sol [1..9]
    fromCell (Just c) = return (val c)

toSudoku :: Solver -> Sudoku' -> IO Sudoku
toSudoku sol rs = do
    rs' <- mapM (mapM (fmap Just . Val.modelValue sol)) rs
    return (Sudoku rs')



--------------------------------------------------------------------------------
-- Validity (what is an OK solution?)

type Block = [Val Int]

blocks :: Sudoku' -> [Block]
blocks sud = sud ++ transpose sud ++ squares sud

split3 :: [a] -> [[a]]
split3 [] = []
split3 as = take 3 as : split3 (drop 3 as)

squares :: Sudoku' -> [Block]
squares sud =
    [concat rs' | rs <- split3 sud, rs' <- split3 (transpose rs)]

isOkayBlock :: Solver -> Block -> IO ()
isOkayBlock sol cs =
    sequence_ [notEqual sol c1 c2  | c1 <- cs, c2 <- cs, c1/=c2]

isOkay :: Solver -> Sudoku' -> IO ()
isOkay sol = mapM_ (isOkayBlock sol) . blocks



--------------------------------------------------------------------------------
-- Running

solveSud :: Sudoku -> IO ()
solveSud sud = do
    sol  <- newSolver
    sud' <- fromSudoku sol sud
    isOkay sol sud'
    ok <- solve sol []
    if ok
      then toSudoku sol sud' >>= printSudoku
      else putStrLn "no solution"

test1 = solveSud example
test2 = solveSud exampleFalse

