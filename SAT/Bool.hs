module SAT.Bool where

import SAT
import SAT.Util
import Data.List( partition, sort )

------------------------------------------------------------------------

andl, orl, xorl :: Solver -> [Lit] -> IO Lit
andl s xs
  | false `elem` xs = return false
  | xAndNegX        = return false
  | otherwise       = case filter (/= true) xs' of
                        []   -> do return true
                        [x]  -> do return x
                        xs'' -> do y <- newLit s
                                   sequence_ [ addClause s [neg y, x] | x <- xs'' ]
                                   addClause s (y : map neg xs'')
                                   return y
 where
  xs'       = usort xs
  (xs0,xs1) = partition pos xs'
  xAndNegX  = xs0 `overlap` sort (map neg xs1)
  
  []     `overlap` _      = False
  _      `overlap` []     = False
  (x:xs) `overlap` (y:ys) =
    case x `compare` y of
	  LT -> xs `overlap` (y:ys)
	  EQ -> True
	  GT -> (x:xs) `overlap` ys

orl s = fmap neg . andl s . map neg

xorl s xs =
  case xs'' of
    []  -> do return (bool p)
    [x] -> do return (if p then x else neg x)
    _   -> do y <- newLit s
              parity s (neg y : xs'') p
              return y
 where
  xs'       = filter (/= false) (sort xs)
  (xs0,xs1) = partition pos (filter (/= true) xs')
  (p,xs'')  = go (even (length (filter (== true) xs'))) [] xs0 (sort (map neg xs1))
  
  go p ys []        xs1       = (p, map neg xs1 ++ ys)
  go p ys xs0       []        = (p, xs0 ++ ys)
  go p ys (x:y:xs0) xs1       | x == y = go p ys xs0 xs1
  go p ys xs0       (x:y:xs1) | x == y = go p ys xs0 xs1
  go p ys (x0:xs0)  (x1:xs1)  =
    case x0 `compare` x1 of
      LT -> go p (x0:ys) xs0 (x1:xs1)
      EQ -> go (not p) ys xs0 xs1
      GT -> go p (neg x1:ys) (x0:xs0) xs1

------------------------------------------------------------------------

atMostOneOr :: Solver -> [Lit] -> [Lit] -> IO ()
atMostOneOr s pre xs = go (length xs) xs
 where
  go n xs | n <= 5 =
    do sequence_ [ addClause s (pre ++ [neg x, neg y]) | (x,y) <- pairs xs ]
   where
    pairs (x:xs) = [ (x,y) | y <- xs ] ++ pairs xs
    pairs []     = []

  go n xs =
    do x <- newLit s
       go (k+1)   (x     : take k xs)
       go (n-k+1) (neg x : drop k xs)
   where
    k = n `div` 2

atMostOne :: Solver -> [Lit] -> IO ()
atMostOne = here atMostOneOr

------------------------------------------------------------------------

parityOr :: Solver -> [Lit] -> [Lit] -> Bool -> IO ()
parityOr s pre xs p = go pre (length xs) xs p
 where
  go pre _ [] False =
    do return ()

  go pre _ [] True =
    do addClause s pre

  go pre n (x:xs) p | n <= 5 =
    do go (neg x : pre) (n-1) xs (not p)
       go (x     : pre) (n-1) xs p
  
  go pre n xs p =
    do x <- newLit s
       go pre (k+1)   (x : take k xs) p
       go pre (n-k+1) (x : drop k xs) p
   where
    k = n `div` 2

parity :: Solver -> [Lit] -> Bool -> IO ()
parity = here parityOr

------------------------------------------------------------------------
