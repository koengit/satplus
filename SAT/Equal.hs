module SAT.Equal where

import SAT
import SAT.Bool
import SAT.Util( here )

------------------------------------------------------------------------

class Equal a where
  equalOr    :: Solver -> [Lit] -> a -> a -> IO ()
  notEqualOr :: Solver -> [Lit] -> a -> a -> IO ()

  isEqual :: Equal a => Solver -> a -> a -> IO Lit
  isEqual s x y =
    do q <- newLit s
       equalOr s [neg q] x y
       notEqualOr s [q] x y
       return q

------------------------------------------------------------------------

equal :: Equal a => Solver -> a -> a -> IO ()
equal = here equalOr

notEqual :: Equal a => Solver -> a -> a -> IO ()
notEqual = here notEqualOr

------------------------------------------------------------------------

instance Equal () where
  equalOr    s pre _ _ = return ()
  notEqualOr s pre _ _ = addClause s pre
  isEqual    _     _ _ = return true

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

------------------------------------------------------------------------

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

------------------------------------------------------------------------
