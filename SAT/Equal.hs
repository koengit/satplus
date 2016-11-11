{-|
Module      : SAT.Equal
Description : Equality functions on things that live in the SAT-solver

This module provides a type class with functions for asserting the equality
or inequality of two objects, as well as functions that compute whether or
not two objects are equal or not.
-}
module SAT.Equal(
  -- * Constraints
    equal
  , notEqual

  -- * Type class Equal
  , Equal(..)
  )
 where

import SAT
import SAT.Bool
import SAT.Util( unconditionally )

------------------------------------------------------------------------------

-- | Type class for SAT-things that can be equal or not.
class Equal a where
  -- | Add constraints to the Solver that state that the arguments are equal,
  -- under the presence of a /disjunctive prefix/.
  -- (See 'SAT.Util.unconditionally' for what /prefix/ means. This function
  -- without prefix is called 'equal'.)
  equalOr :: Solver -> [Lit] {- ^ prefix -} -> a -> a -> IO ()

  -- | Add constraints to the Solver that state that the arguments are not
  -- equal, under the presence of a /disjunctive prefix/.
  -- (See 'SAT.Util.unconditionally' for what /prefix/ means.
  -- This function without prefix is called 'notEqual'.)
  notEqualOr :: Solver -> [Lit] {- ^ prefix -} -> a -> a -> IO ()

  -- | Return a literal that represents the arguments being equal or not.
  isEqual :: Solver -> a -> a -> IO Lit
  isEqual s x y =
    do q <- newLit s
       equalOr s [neg q] x y
       notEqualOr s [q] x y
       return q

------------------------------------------------------------------------------

-- | Add constraints to the Solver that state that the arguments are equal.
-- See also 'equalOr'.
equal :: Equal a => Solver -> a -> a -> IO ()
equal = unconditionally equalOr

-- | Add constraints to the Solver that state that the arguments are not equal.
-- See also 'notEqualOr'.
notEqual :: Equal a => Solver -> a -> a -> IO ()
notEqual = unconditionally notEqualOr

------------------------------------------------------------------------------

instance Equal () where
  equalOr    s pre _ _ = return ()
  notEqualOr s pre _ _ = addClause s pre
  isEqual    _     _ _ = return true

instance Equal Bool where
  equalOr    s pre x y = if x == y then return () else addClause s pre
  notEqualOr s pre x y = if x /= y then return () else addClause s pre
  isEqual    _     x y = return (bool (x==y))

instance Equal Lit where
  equalOr s pre x y =
    do addClause s (pre ++ [neg x, y])
       addClause s (pre ++ [x, neg y])

  notEqualOr s pre x y =
    do equalOr s pre x (neg y)

  isEqual s x y = xorl s [x, neg y]

instance (Equal a, Equal b) => Equal (a,b) where
  equalOr s pre (x1,x2) (y1,y2) =
    do equalOr s pre x1 y1
       equalOr s pre x2 y2

  notEqualOr s pre (x1,x2) (y1,y2) =
    do q <- newLit s
       notEqualOr s (q:pre) x1 y1
       notEqualOr s [neg q] x2 y2

instance (Equal a, Equal b) => Equal (Either a b) where
  equalOr s pre (Left x)  (Left y)  = equalOr s pre x y
  equalOr s pre (Right x) (Right y) = equalOr s pre x y
  equalOr s pre _         _         = addClause s pre

  notEqualOr s pre (Left x)  (Left y)  = notEqualOr s pre x y
  notEqualOr s pre (Right x) (Right y) = notEqualOr s pre x y
  notEqualOr s pre _         _         = return ()

------------------------------------------------------------------------------

instance (Equal a, Equal b, Equal c) => Equal (a,b,c) where
  equalOr    s pre x y = equalOr    s pre (encTriple x) (encTriple y)
  notEqualOr s pre x y = notEqualOr s pre (encTriple x) (encTriple y)

encTriple (x,y,z) = ((x,y),z)

instance Equal a => Equal (Maybe a) where
  equalOr    s pre mx my = equalOr    s pre (encMaybe mx) (encMaybe my)
  notEqualOr s pre mx my = notEqualOr s pre (encMaybe mx) (encMaybe my)

encMaybe Nothing  = Left ()
encMaybe (Just x) = Right x

instance Equal a => Equal [a] where
  equalOr    s pre xs ys = equalOr    s pre (encList xs) (encList ys)
  notEqualOr s pre xs ys = notEqualOr s pre (encList xs) (encList ys)

encList []     = Nothing
encList (x:xs) = Just (x,xs)

------------------------------------------------------------------------------
