{-|
Module      : SAT.Unary
Description : Functions for working with natural numbers represented as
              unary numbers.
-}
module SAT.Unary(
  -- * The Unary type
    Unary
  , newUnary
  , zero
  , number
  , digit
  , maxValue

  -- * Comparison against constants
  , (.<=), (.<), (.>), (.>=)

  -- * Counting
  , count
  , add
  , addList

  -- * Operations
  , invert
  , succ
  , pred
  , (//)
  , modulo

  -- * Models
  , modelValue
  )
 where

import SAT hiding ( modelValue )
import qualified SAT
import SAT.Bool
import SAT.Equal
import SAT.Order
import Data.List( sort, insert, transpose )

import Prelude hiding ( Enum(succ,pred) )

------------------------------------------------------------------------------

-- | The type Unary, for natural numbers represented in unary
data Unary = Unary Int [Lit] -- sorted 11..1100..00
 deriving ( Eq, Ord )

instance Show Unary where
  show (Unary _ xs) = show xs

-- | Creates a fresh unary number, with the specified maximum value.
newUnary :: Solver -> Int -> IO Unary
newUnary s n =
  do xs <- sequence [ newLit s | i <- [1..n] ]
     sequence_ [ addClause s [neg y, x] | (x,y) <- xs `zip` tail xs ]
     return (Unary n xs)

-- | Creates 0 as a unary number.
zero :: Unary
zero = Unary 0 []

-- | Creates n as a unary number.
number :: Int -> Unary
number n = Unary n (replicate n true)

-- | Successor.
succ :: Unary -> Unary
succ (Unary n xs) = Unary (n+1) (true : xs)

-- | Predecessor (but 0 goes to 0).
pred :: Unary -> Unary
pred (Unary _ [])     = Unary 0 []
pred (Unary n (_:xs)) = Unary (n-1) xs

-- | Creates a 1-digit unary number, specified by the given literal.
digit :: Lit -> Unary
digit x = Unary 1 [x]

-- | Inverts a unary number; computes /maxValue n - n/. Can be used to maximize
-- instead of minimize.
invert :: Unary -> Unary
invert (Unary n xs) = Unary n (reverse (map neg xs))

-- | Compares a unary number with a constant.
(.<=), (.<), (.>=), (.>) :: Unary -> Int -> Lit
--u .>  k = u .>= (k+1)
u .<  k = neg (u .>= k)
u .<= k = u .< (k+1)
u .>= k = u .> (k-1)

Unary n xs .> k
--  | length xs /= n = error ("unary: length " ++ show xs ++ " /= " ++ show n)
  | k < 0     = true
  | k >= n    = false
  | otherwise = xs !! k

-- | Integer division by a (strictly positive) constant.
(//) :: Unary -> Int -> Unary
Unary n xs // k =
  -- Idea: take every k-th literal.
  Unary (n `div` k)
        [ x | (x,True) <- xs `zip` cycle (replicate (k-1) False ++ [True]) ]

-- | Integer modulo a (strictly positive) constant.
modulo :: Solver -> Unary -> Int -> IO Unary
modulo s (Unary n xs) k =
  -- Idea: We start with a unary number, say
  --   1 1 1 1 1 1 1 0 0 0 0 0 0
  -- and we take modulo, say 3. First, we divide in groups of 3:
  --   [1 1 1] [1 1 1] [1 0 0] [0 0 0] [0]
  -- and pad:
  --   [1 1 1] [1 1 1] [1 0 0] [0 0 0] [0 0 0]
  -- We know there will only be at most one group that contains
  -- both 1's and 0's. That group is the answer (minus the last element
  -- because we know it will be 0).
  -- (If there is no such group, the answer is simply [0 0].)
  -- First, we "neutralize" every group [1 1 1], by taking away the
  -- last literal in each group, negating it, and and-ing it with the rest:
  --   [0 0]   [0 0]   [1 0]   [0 0]   [0 0]
  -- Then, we transpose:
  --   [0 0 1 0 0]
  --   [0 0 0 0 0]
  -- and we take the or of each row:
  --   [1 0]
  -- which is the right answer.
  do xss1 <- sequence [ sequence [ andl s [neg a, x] | x <- init as ]
                      | as <- xss
                      , let a = last as
                      ]
     ys <- sequence [ orl s bs | bs <- transpose xss1 ]
     return (Unary (if null ys then 0 else k-1) ys)
 where
  xss = map pad . takeWhile (not . null) . map (take k) . iterate (drop k) $ xs
  pad = take k . (++ repeat false)

-- | Returns a unary number that represents the number of True literals in
-- the given list.
count :: Solver -> [Lit] -> IO Unary
count s xs = addList s (map digit xs)

-- | Adds up two unary numbers.
add :: Solver -> Unary -> Unary -> IO Unary
add s (Unary n xs) (Unary m ys) =
  do zs <- merge s xs ys
     return (Unary (n+m) zs)

merge :: Solver -> [Lit] -> [Lit] -> IO [Lit]
merge s []  ys  = return ys
merge s xs  []  = return xs
merge s [x] [y] =
  do a <- andl s [x,y]
     b <- orl s [x,y]
     return [b,a]

merge s xs  ys  =
  do zs0 <- merge s xs0 ys0
     zs1 <- merge s xs1 ys1
     let zs = zs0 `ilv` zs1
     zss <- sequence [ merge s [v] [w] | (v,w) <- pairs (tail zs) ]
     return (take (a+b) ([head zs] ++ concat zss ++ [last zs]))
 where
  a   = length xs
  b   = length ys
  n'  = a `max` b
  n   = if even n' then n' else n'+1 -- apparently not needed?
  xs' = xs ++ replicate (n-a) false
  ys' = ys ++ replicate (n-b) false
  xs0 = evens xs'
  xs1 = odds  xs'
  ys0 = evens ys'
  ys1 = odds  ys'

  evens (x:xs) = x : odds xs
  evens []     = []

  odds (x:xs) = evens xs
  odds []     = []

  pairs (x:y:xs) = (x,y) : pairs xs
  pairs _        = []

  (x:xs) `ilv` ys = x : (ys `ilv` xs)
  []     `ilv` ys = ys

-- | Returns the maximum value a given unary number can have.
maxValue :: Unary -> Int
maxValue (Unary n _) = n

-- | Adds up a list of unary numbers. When adding more than 2 numbers, this
-- function is preferred over linearly folding the function 'add' over a list,
-- because a balanced tree (based on the sizes of the numbers involved) is
-- constructed by this function, which creates a lot less clauses than doing
-- it the naive way.
addList :: Solver -> [Unary] -> IO Unary
addList s us = go (sort us)
 where
  go [] =
    do return zero

  go [u] =
    do return u

  go (u1:u2:us) =
    do u <- add s u1 u2
       go (insert u us)

-- | Return the numeric value of a unary number in the current model.
-- (/Use only when 'solve' has returned True!/)
modelValue :: Solver -> Unary -> IO Int
modelValue s (Unary _ xs) = go xs
 where
  go []     = do return 0
  go (x:xs) = do b <- SAT.modelValue s x
                 if b then
                   (+1) `fmap` go xs
                  else
                   return 0

------------------------------------------------------------------------------

instance Equal Unary where
  equalOr s pre u1 u2 =
    -- this generates precisely all bi-implications
    do lessThanEqualOr s pre u1 u2
       lessThanEqualOr s pre u2 u1

  notEqualOr s pre u1 u2 =
    -- this only needs one helper variable
    do q <- newLit s
       lessThanOr s (q    :pre) u1 u2
       lessThanOr s (neg q:pre) u2 u1

instance Order Unary where
  lessOr s pre False u v =
    do lessOr s pre True (succ u) v

  lessOr s pre True (Unary _ xs) (Unary _ ys) = leq xs ys
   where
    leq [] _ =
      do return ()

    leq (x:xs) [] =
      do addClause s (neg x : pre)
         -- do not need to recurse here

    leq (x:xs) (y:ys) =
      do addClause s (neg x : y : pre)
         leq xs ys

------------------------------------------------------------------------------
