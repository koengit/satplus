{-|
Module      : SAT.Order
Description : Comparison functions on things that live in the SAT-solver

This module provides a type class with functions for asserting the ordering
of two objects, as well as functions that compute whether or
not an object compares to another object.
-}
module SAT.Order(
  -- * Functions
    isGreaterThan
  , isLessThan
  , isGreaterThanEqual
  , isLessThanEqual

  -- * Constraints
  , greaterThan
  , lessThan
  , greaterThanEqual
  , lessThanEqual

  , greaterThanOr
  , lessThanOr
  , greaterThanEqualOr
  , lessThanEqualOr

  -- * Type class
  , Order(..)
  )
 where

import SAT
import SAT.Equal
import SAT.Util

import Prelude
import Control.Monad ( when )

------------------------------------------------------------------------------

-- | Type class for things that can be compared.
--
-- New instances only need to define the 'lessTupleOr' function. However, if
-- there is no natural way to implement lexicographic ordering with the
-- instance type, it is possible to only define 'lessOr', in which case
-- the default definition of 'lessTupleOr' is less efficient.
--
-- For types where it is easy to see statically if the answer is going to
-- be True or False, a special definition of 'newLessLit' can be made. For
-- most types, the default definition should be enough.
class Order a where
  -- | Add constraints to the Solver that state that the first argument is
  -- less than the second, under the presence of a /disjunctive prefix/.
  -- The extra argument specifies if the comparison should be strict (False)
  -- or inclusive (True).
  -- (See 'SAT.Util.unconditionally' for what /prefix/ means.)
  lessOr :: Solver -> [Lit] -> Bool -> a -> a -> IO ()
  lessOr s pre incl x y = lessTupleOr s pre incl (x,()) (y,())

  -- | Create a literal that implies the specified relationship between
  -- the arguments.
  newLessLit :: Solver -> Bool -> a -> a -> IO Lit
  newLessLit s incl x y =
    do q <- newLit s
       lessOr s [neg q] incl x y
       return q

  -- | Add constraints to the Solver that state that the first argument is
  -- less than the second, under the presence of a /disjunctive prefix/.
  -- The extra argument specifies if the comparison should be strict (False)
  -- or inclusive (True).
  -- (See 'SAT.Util.unconditionally' for what /prefix/ means.) This function
  -- is typically not going to be used directly by a user of this library;
  -- use 'compareOr' instead.
  lessTupleOr :: Order b => Solver -> [Lit] -> Bool -> (a,b) -> (a,b) -> IO ()
  lessTupleOr s pre incl (x,p) (y,q) =
    do w <- newLessLit s incl p q
       if w == false || w == true then
         do lessOr s pre (w == true) x y
        else
         do lessOr s pre     True  x y  -- x <= y
            lessOr s (w:pre) False x y  -- x < y | p <~ q

------------------------------------------------------------------------------

-- | Add constraints to the Solver that state that the arguments have the
-- specified relationship.
greaterThan, greaterThanEqual, lessThan, lessThanEqual ::
  Order a => Solver -> a -> a -> IO ()
greaterThan      = unconditionally greaterThanOr
greaterThanEqual = unconditionally greaterThanEqualOr
lessThan         = unconditionally lessThanOr
lessThanEqual    = unconditionally lessThanEqualOr

-- | Add constraints to the Solver that state that the arguments have the
-- specified relationship, under the presence of a /disjunctive prefix/.
-- (See 'SAT.Util.unconditionally' for what /prefix/ means.)
greaterThanOr, greaterThanEqualOr, lessThanOr, lessThanEqualOr ::
  Order a => Solver -> [Lit] -> a -> a -> IO ()
greaterThanOr      s pre x y = lessThanOr      s pre y x
greaterThanEqualOr s pre x y = lessThanEqualOr s pre y x
lessThanOr         s pre x y = lessOr s pre False x y
lessThanEqualOr    s pre x y = lessOr s pre True  x y

-- | Return a literal that indicates whether or not the arguments have
-- the specified relationship.
isGreaterThan, isGreaterThanEqual, isLessThan, isLessThanEqual ::
  Order a => Solver -> a -> a -> IO Lit
isGreaterThan      s x y = isLessThan      s y x
isGreaterThanEqual s x y = isLessThanEqual s y x
isLessThan         s x y = neg `fmap` isGreaterThanEqual s x y
isLessThanEqual    s x y =
  do q <- newLessLit s True x y
     when (q /= false && q /= true) $
       greaterThanOr s [q] x y
     return q

------------------------------------------------------------------------------

instance Order () where
  lessOr s pre True  _ _ = return ()
  lessOr s pre False _ _ = addClause s pre

  newLessLit s True  _ _ = return true
  newLessLit s False _ _ = return false

  lessTupleOr s pre incl (_,p) (_,q) =
    lessOr s pre incl p q

instance Order Bool where
  lessTupleOr s pre incl (x,p) (y,q) =
    case x `compare` y of
      LT -> return ()
      EQ -> lessOr s pre incl p q
      GT -> addClause s pre

  newLessLit s incl x y =
    case x `compare` y of
      LT -> return true
      EQ -> return (bool incl)
      GT -> return false

instance Order Lit where
  lessTupleOr s pre incl (x,p) (y,q)
    | x == y    = lessOr s pre incl p q
    | otherwise =
      do w <- newLessLit s incl p q
         addClause s ([y, w] ++ pre)
         addClause s ([neg x, w] ++ pre)
         addClause s ([neg x, y] ++ pre)

  newLessLit s incl x y
    | x == y     = return (bool incl)
    | x == neg y = return y
    | x == false = return (if incl then true  else y)
    | x == true  = return (if incl then y     else false)
    | y == false = return (if incl then neg x else false)
    | y == true  = return (if incl then true  else neg x)
    | otherwise  = do q <- newLit s
                      lessOr s [neg q] incl x y
                      return q

instance (Order a, Order b) => Order (a,b) where
  lessOr s pre incl t1 t2 =
    lessTupleOr s pre incl t1 t2

  lessTupleOr s pre incl t1 t2 =
    lessTupleOr s pre incl (encTuple t1) (encTuple t2)

encTuple ((x,y),r) = (x,(y,r))

instance (Order a, Order b) => Order (Either a b) where
  lessTupleOr s pre incl (Left x1,z1) (Left x2,z2) =
    lessTupleOr s pre incl (x1,z1) (x2,z2)

  lessTupleOr s pre incl (Right y1,z1) (Right y2,z2) =
    lessTupleOr s pre incl (y1,z1) (y2,z2)

  lessTupleOr s pre incl (Left _,z1) (Right _,z2) =
    return ()

  lessTupleOr s pre incl (Right _,z1) (Left _,z2) =
    addClause s pre

------------------------------------------------------------------------------

instance (Order a, Order b, Order c) => Order (a,b,c) where
  lessTupleOr s pre incl t1 t2 =
    lessTupleOr s pre incl (encTriple t1) (encTriple t2)

encTriple ((x,y,z),r) = (x,(y,(z,r)))

instance Order a => Order (Maybe a) where
  lessTupleOr s pre incl m1 m2 =
    lessTupleOr s pre incl (encMaybe m1) (encMaybe m2)

encMaybe (Nothing, r) = (Left (), r)
encMaybe (Just x,  r) = (Right x, r)

instance Order a => Order [a] where
  lessTupleOr s pre incl l1 l2 =
    lessTupleOr s pre incl (encList l1) (encList l2)

encList ([],     r) = (Left (),      r)
encList ((x:xs), r) = (Right (x,xs), r)
