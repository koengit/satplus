module SAT.Unary(
  -- * The Unary type
    Unary
  , newUnary
  , zero
  , digit
  , invert
  , maxValue
  
  -- * Comparison against constants
  , (.<=), (.<), (.>), (.>=)

  -- * Counting
  , count
  , add
  , addList

  -- * Models
  , modelValue
  )
 where

import SAT hiding ( modelValue )
import qualified SAT
import SAT.Bool
import SAT.Equal
import Data.List( sort, insert )

------------------------------------------------------------------------

-- | The type Unary, for unary numbers
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

-- | Creates a 1-digit unary number, specified by the given literal.
digit :: Lit -> Unary
digit x = Unary 1 [x]

-- | Inverts a unary number; computes /maxValue n - n/. Used to maximize instead of minimize.
invert :: Unary -> Unary
invert (Unary n xs) = Unary n (reverse (map neg xs))

-- | Compares a unary number with a constant.
(.<=), (.<), (.>=), (.>) :: Unary -> Int -> Lit
u .>  k = u .>= (k+1)
u .<  k = neg (u .>= k)
u .<= k = u .< (k+1)

Unary n xs .>= k
  | k <= 0    = true
  | k >  n    = false
  | otherwise = xs !! (k-1)

-- | Returns a unary number that represents the number of True literals in the given list.
count :: Solver -> [Lit] -> IO Unary
count s xs = addList s (map digit xs)

-- | Adds up two unary numbers.
add :: Solver -> Unary -> Unary -> IO Unary
add s (Unary n xs) (Unary m ys) =
  do zs <- merge xs ys
     return (Unary (n+m) zs)
 where
  merge []  ys  = return ys
  merge xs  []  = return xs
  merge [x] [y] = merge2 x y
  merge xs  ys  =
    do zs0 <- merge xs0 ys0
       zs1 <- merge xs1 ys1
       let zs = zs0 `ilv` zs1
       zss <- sequence [ merge2 v w | (v,w) <- pairs (tail zs) ]
       return (take (a+b) ([head zs] ++ concat zss ++ [last zs]))
   where
    a   = length xs
    b   = length ys
    n'  = a `max` b
    n   = if even n' then n' else n'+1
    xs' = xs ++ replicate (n-a) false
    ys' = ys ++ replicate (n-b) false
    xs0 = evens xs'
    xs1 = odds  xs'
    ys0 = evens ys'
    ys1 = odds  ys'

  merge2 x y =
    do a <- andl s [x,y]
       b <- orl s [x,y]
       return [b,a]

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
