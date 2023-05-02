{-|
Module      : SAT.Binary
Description : Functions for working with natural numbers represented as
              binary numbers.
              
              WARNING: completely untested so far.
-}
module SAT.Binary(
  -- * The Binary type
    Binary
  , newBinary
  , zero
  , number
  , digit
  , maxValue

  -- * Counting
  , count
  , add
  , addList
  , addBits
  , mul1
  , mul

  -- * Operations
  , invert

  -- * Conversion
  , fromList
  , toList

  -- * Models
  , modelValue
  )
 where

------------------------------------------------------------------------------

import SAT hiding ( modelValue )
import qualified SAT
import SAT.Bool
import SAT.Equal
import SAT.Order
import SAT.Value
import Data.List( insert, sort )

------------------------------------------------------------------------------

-- | The type Binary, for natural numbers represented in binary
newtype Binary = Binary [Lit] -- least significant bit first
 deriving ( Eq, Ord )

instance Show Binary where
  show (Binary xs) = show xs

-- | Creates a binary number from a list of digits (least significant bit first).
fromList :: [Lit] -> Binary
fromList xs = Binary xs

-- | Returns the list of digits (least significant bit first).
toList :: Binary -> [Lit]
toList (Binary xs) = xs

-- | Creates a fresh binary number, with the specified number of bits.
newBinary :: Solver -> Int -> IO Binary
newBinary s k =
  do xs <- sequence [ newLit s | i <- [1..k] ]
     return (Binary xs)

-- | Creates 0 as a binary number.
zero :: Binary
zero = Binary []

-- | Creates n>=0 as a binary number.
number :: Int -> Binary
number n = Binary (bin n)
 where
  bin 0 = []
  bin n = (if odd n then true else false) : bin (n `div` 2)

-- | Creates a 1-digit binary number, specified by the given literal.
digit :: Lit -> Binary
digit x = fromList [x]

-- | Inverts a binary number; computes /maxValue n - n/. Can be used to maximize
-- instead of minimize.
invert :: Binary -> Binary
invert (Binary xs) = Binary (map neg xs)

-- | Returns a binary number that represents the number of true literals in
-- the given list.
count :: Solver -> [Lit] -> IO Binary
count s xs = addList s (map digit xs)

-- | Adds up two binary numbers.
add :: Solver -> Binary -> Binary -> IO Binary
add s a b = addList s [a,b]

-- | Adds up a list of binary numbers. When adding more than 2 numbers, this
-- function is preferred over linearly folding the function 'add' over a list,
-- because a balanced tree (based on the sizes of the numbers involved) is
-- constructed by this function, which creates a lot less clauses than doing
-- it the naive way.
addList :: Solver -> [Binary] -> IO Binary
addList s bs = addBits s [ (k,x) | Binary xs <- bs, (k,x) <- [0..] `zip` xs ]

-- | Adds up a list of digits, annotated with their weight, which is the
-- placement of the binary digit. This function is used in the functions @addList@
-- and @mul@, but may be useful to users in its own right.
addBits :: Solver -> [(Int,Lit)] -> IO Binary
addBits s ixs = Binary `fmap` go 0 (sort ixs)
 where
  go _ [] =
    do return []

  go i xs@((i0,x):_) | i < i0 =
    do ys <- go (i+1) xs
       return (false : ys)

  go _ ((i0,x):(i1,y):(i2,z):xs) | i0 == i1 && i0 == i2 =
    do (v,c) <- full x y z
       go i0 ((i0,v):insert (i0+1,c) xs)

  go _ ((i0,x):(i1,y):xs) | i0 == i1 =
    do (v,c) <- full x y false
       ys <- go (i0+1) ((i0+1,c):xs)
       return (v:ys)

  go _ ((i0,x):xs) =
    do ys <- go (i0+1) xs
       return (x:ys)

  full x y z =
    do v <- xorl s [x,y,z]
       c <- atLeast2 x y z
       return (v,c)
  
  -- desparately tries to avoid creating extra literals
  atLeast2 x y z
    | x == true = orl s [y,z] 
    | y == true = orl s [x,z] 
    | z == true = orl s [x,y] 

    | x == false = andl s [y,z] 
    | y == false = andl s [x,z] 
    | z == false = andl s [x,y] 

    | x == y = return x 
    | y == z = return y 
    | x == z = return z
    
    | x == neg y = return z 
    | y == neg z = return x 
    | x == neg z = return y
    
    | otherwise =
      do v <- newLit s
         addClause s [neg x, neg y, v]
         addClause s [neg x, neg z, v]
         addClause s [neg y, neg z, v]
         addClause s [x, y, neg v]
         addClause s [x, z, neg v]
         addClause s [y, z, neg v]
         return v

-- | Returns the maximum value a given binary number can have.
maxValue :: Num a => Binary -> a
maxValue (Binary xs) = (2^length xs) - 1

-- | Multiplies a digit and a binary number.
mul1 :: Solver -> Lit -> Binary -> IO Binary
mul1 s x (Binary ys) =
  do ys' <- sequence [ andl s [x,y] | y <- ys ]
     return (Binary ys')

-- | Multiplies two binary numbers.
mul :: Solver -> Binary -> Binary -> IO Binary
mul s (Binary xs) (Binary ys) =
  do izs <- sequence
            [ do z <- andl s [x,y]
                 return (i+j,z)
            | (i,x) <- [0..] `zip` xs
            , (j,y) <- [0..] `zip` ys
            ]
     addBits s izs

-- | Return the numeric value of a binary number in the current model.
-- (/Use only when 'solve' has returned True!/)
modelValue :: Num a => Solver -> Binary -> IO a
modelValue s (Binary xs) = go xs
 where
  go []     = do return 0
  go (x:xs) = do b <- SAT.modelValue s x
                 n <- go xs
                 return (2*n + if b then 1 else 0)

------------------------------------------------------------------------------

instance Value Binary where
  type Type Binary = Integer
  getValue = modelValue

instance Equal Binary where
  equalOr s pre (Binary xs) (Binary ys) =
    equalOr s pre (pad xs ys) (pad ys xs)

  notEqualOr s pre (Binary xs) (Binary ys) =
    notEqualOr s pre (pad xs ys) (pad ys xs)

instance Order Binary where
  lessOr s pre b (Binary xsLSBF) (Binary ysLSBF) =
    do lessOr s pre b xs ys
    where xs = reverse (pad xsLSBF ysLSBF)
          ys = reverse (pad ysLSBF xsLSBF)


pad xs ys = xs ++ replicate (length ys - length xs) false

------------------------------------------------------------------------------

