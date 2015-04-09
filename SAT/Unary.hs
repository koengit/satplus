module SAT.Unary where

import SAT
import SAT.Bool
import SAT.Equal
import Data.List( sort, insert )

------------------------------------------------------------------------

data Unary = Unary Int [Lit] -- sorted 11..1100..00
 deriving ( Eq, Ord )

instance Show Unary where
  show (Unary _ xs) = show xs

newUnary :: Solver -> Int -> IO Unary
newUnary s n =
  do xs <- sequence [ newLit s | i <- [1..n] ]
     sequence_ [ addClause s [neg y, x] | (x,y) <- xs `zip` tail xs ]
     return (Unary n xs)

zero :: Unary
zero = Unary 0 []

one :: Lit -> Unary
one x = Unary 1 [x]

(.<=), (.<), (.>=), (.>) :: Unary -> Int -> Lit
u .>  k = u .>= (k+1)
u .<  k = neg (u .>= k)
u .<= k = u .< (k+1)

Unary n xs .>= k
  | k <= 0    = true
  | k >  n    = false
  | otherwise = xs !! (k-1)

count :: Solver -> [Lit] -> IO Unary
count s xs = addList s (map one xs)

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

maxValue :: Unary -> Int
maxValue (Unary n _) = n

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
