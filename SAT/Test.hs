{-|
Module      : SAT.Test
Description : QuickCheck properties for many of the functions in this library
-}
{-# LANGUAGE TemplateHaskell #-}
module SAT.Test where

import SAT
import SAT.Bool
import qualified SAT.Unary as U
import qualified SAT.Val   as V
import SAT.Optimize
import SAT.Equal
import SAT.Order
import qualified SAT.Term as T

import Test.QuickCheck
import Test.QuickCheck.Modifiers
import Test.QuickCheck.Monadic
import Test.QuickCheck.Poly
import Test.QuickCheck.All

------------------------------------------------------------------------------

prop_conflict c1 c2 c3 xs =
  monadicIO $
    do s  <- run $ newSolver
       ps <- run $ sequence [ newLit s | i <- [1..100] ]
       let lit (LIT x) = if x > 0 then p else neg p
            where
             p = (true : ps) !! (abs x - 1)

       run $ addClause s (map lit c1)
       run $ addClause s (map lit c2)
       run $ addClause s (map lit c3)
       b <- run $ solve s (map lit xs)
       monitor (not b ==>)
       ys <- run $ conflict s
       monitor (whenFail (putStrLn ("ys=" ++ show ys)))
       assert (all (`elem` map lit xs) (map neg ys))

------------------------------------------------------------------------------

prop_andl xs =
  satfun $ \s lit bol ->
    do y <- run $ andl s (map lit xs)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s y
       assert (a == and (map bol xs))

prop_orl xs =
  satfun $ \s lit bol ->
    do y <- run $ orl s (map lit xs)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s y
       assert (a == or (map bol xs))

prop_xorl xs =
  satfun $ \s lit bol ->
    do y <- run $ xorl s (map lit xs)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s y
       monitor (whenFail (putStrLn ("xorl " ++ show (map bol xs) ++ " = " ++ show a)))
       assert (a == odd (length (filter id (map bol xs))))

prop_implies x y =
  satfun $ \s lit bol ->
    do z <- run $ implies s (lit x) (lit y)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s z
       assert (a == (bol x <= bol y))

prop_equiv x y =
  satfun $ \s lit bol ->
    do z <- run $ equiv s (lit x) (lit y)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s z
       assert (a == (bol x == bol y))

------------------------------------------------------------------------------

prop_atMostOneOr pre xs =
  satfun $ \s lit bol ->
    do run $ atMostOneOr s (map lit pre) (map lit xs)
       b <- run $ solve s []
       monitor (whenFail (putStrLn ("atMostOneOr " ++ show (map bol pre) ++ " " ++ show (map bol xs) ++ " -> " ++ show b)))
       assert (or (map bol pre) || b == (length (filter id (map bol xs)) <= 1))

prop_parityOr pre xs p =
  satfun $ \s lit bol ->
    do run $ parityOr s (map lit pre) (map lit xs) p
       b <- run $ solve s []
       monitor (whenFail (putStrLn ("parityOr " ++ show (map bol pre) ++ " " ++ show (map bol xs) ++ " " ++ show p ++ " -> " ++ show b)))
       assert (or (map bol pre) || b == (p == odd (length (filter id (map bol xs)))))

------------------------------------------------------------------------------

prop_unaryLeq (NonNegative m) (NonNegative k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       b <- run $ solve s []
       assert b
       n <- run $ U.modelValue s u
       a <- run $ modelValue s (u U..<= k)
       assert (a == (n <= k))

prop_unaryLt (NonNegative m) (NonNegative k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       b <- run $ solve s []
       assert b
       n <- run $ U.modelValue s u
       a <- run $ modelValue s (u U..< k)
       assert (a == (n < k))

prop_unaryGeq (NonNegative m) (NonNegative k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       b <- run $ solve s []
       assert b
       n <- run $ U.modelValue s u
       a <- run $ modelValue s (u U..>= k)
       assert (a == (n >= k))

prop_unaryGt (NonNegative m) (NonNegative k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       b <- run $ solve s []
       assert b
       n <- run $ U.modelValue s u
       a <- run $ modelValue s (u U..> k)
       assert (a == (n > k))

prop_unary_add (NonNegative m1) (NonNegative m2) =
  satfun $ \s lit bol ->
    do u1 <- run $ U.newUnary s m1
       u2 <- run $ U.newUnary s m2
       k1 <- pick (choose (0,m1))
       k2 <- pick (choose (0,m2))
       u3 <- run $ U.add s u1 u2
       b <- run $ solve s [u1 U..>= k1, u2 U..>= k2]
       assert b
       n1 <- run $ U.modelValue s u1
       n2 <- run $ U.modelValue s u2
       n3 <- run $ U.modelValue s u3
       assert (n3 == n1+n2)

prop_unary_count xs =
  satfun $ \s lit bol ->
    do u <- run $ U.count s (map lit xs)
       b <- run $ solve s []
       assert b
       n  <- run $ U.modelValue s u
       bs <- run $ sequence [ modelValue s (lit x) | x <- xs ]
       assert (length (filter id bs) == n)

prop_unary_div (NonNegative m) (Positive k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       i <- pick (choose (0,m))
       b <- run $ solve s [u U..>= i]
       assert b
       n  <- run $ U.modelValue s u
       nk <- run $ U.modelValue s (u U.// k)
       assert (nk == (n `div` k))

prop_unary_mod (NonNegative m) (Positive k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       i <- pick (choose (0,m))
       uk <- run $ U.modulo s u k
       b <- run $ solve s [u U..>= i]
       assert b
       n  <- run $ U.modelValue s u
       nk <- run $ U.modelValue s uk
       assert (nk == (n `mod` k))

------------------------------------------------------------------------------

prop_minimize (NonNegative m) as =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       i <- pick (choose (0,m))
       run $ addClause s [u U..>= i]
       b <- run $ solveMinimize s (map lit as) u
       assert (b == (False `notElem` map bol as))
       if b then
         do n <- run $ U.modelValue s u
            monitor (whenFail $ putStrLn ("n=" ++ show n ++ ", i=" ++ show i))
            assert (n == i)
        else
         do monitor (whenFail $ putStrLn ("b=" ++ show b ++ ", as=" ++ show (map bol as)))

prop_maximize (NonNegative m) as =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       i <- pick (choose (0,m))
       run $ addClause s [u U..<= i]
       b <- run $ solveMaximize s (map lit as) u
       assert (b == (False `notElem` map bol as))
       if b then
         do n <- run $ U.modelValue s u
            monitor (whenFail $ putStrLn ("n=" ++ show n ++ ", i=" ++ show i))
            assert (n == i)
        else
         do monitor (whenFail $ putStrLn ("b=" ++ show b ++ ", as=" ++ show (map bol as)))

------------------------------------------------------------------------------

prop_equalLit pre x y =
  satfun $ \s lit bol ->
    do run $ equalOr s (map lit pre) (lit x) (lit y)
       b <- run $ solve s []
       assert (b == (or (map bol pre) || bol x == bol y))

prop_notEqualLit pre x y =
  satfun $ \s lit bol ->
    do run $ notEqualOr s (map lit pre) (lit x) (lit y)
       b <- run $ solve s []
       assert (b == (or (map bol pre) || bol x /= bol y))

prop_equalPair pre x1 x2 y1 y2 =
  satfun $ \s lit bol ->
    do run $ equalOr s (map lit pre) (lit x1, lit x2) (lit y1, lit y2)
       b <- run $ solve s []
       assert (b == (or (map bol pre) || (bol x1, bol x2) == (bol y1, bol y2)))

prop_notEqualPair pre x1 x2 y1 y2 =
  satfun $ \s lit bol ->
    do run $ notEqualOr s (map lit pre) (lit x1, lit x2) (lit y1, lit y2)
       b <- run $ solve s []
       assert (b == (or (map bol pre) || (bol x1, bol x2) /= (bol y1, bol y2)))

prop_isEqualPair x1 x2 y1 y2 =
  satfun $ \s lit bol ->
    do q <- run $ isEqual s (lit x1, lit x2) (lit y1, lit y2)
       b <- run $ solve s []
       assert b
       p <- run $ modelValue s q
       assert (p == ((bol x1, bol x2) == (bol y1, bol y2)))

------------------------------------------------------------------------------

prop_isLessThanEqual x y =
  satfun $ \s lit bol ->
    do z <- run $ isLessThanEqual s (lit x) (lit y)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s (lit x)
       b <- run $ modelValue s (lit y)
       c <- run $ modelValue s z
       assert (c == (a <= b))

prop_isLessThanEqualPair x1 x2 y1 y2 =
  satfun $ \s lit bol ->
    do z <- run $ isLessThanEqual s (lit x1, lit x2) (lit y1, lit y2)
       b <- run $ solve s []
       assert b
       a1 <- run $ modelValue s (lit x1)
       a2 <- run $ modelValue s (lit x2)
       b1 <- run $ modelValue s (lit y1)
       b2 <- run $ modelValue s (lit y2)
       c <- run $ modelValue s z
       assert (c == ((a1,a2) <= (b1,b2)))

prop_compareLit pre cmp x y =
  satfun $ \s lit bol ->
    do run $ lessOr s (map lit pre) cmp (lit x) (lit y)
       b <- run $ solve s []
       assert (b == (or (map bol pre) || bol x `comp` bol y))
   where
    comp = head [ op | (cmp',op) <- cmps, cmp' == cmp ]
    cmps = [(False,(<)),(True,(<=))]

prop_compareBool pre cmp x y =
  satfun $ \s lit bol ->
    do run $ lessOr s (map lit pre) cmp (bool x) (bool y)
       b <- run $ solve s []
       assert (b == (or (map bol pre) || x `comp` y))
   where
    comp = head [ op | (cmp',op) <- cmps, cmp' == cmp ]
    cmps = [(False,(<)),(True,(<=))]

prop_comparePair pre cmp x1 x2 y1 y2 =
  satfun $ \s lit bol ->
    do run $ lessOr s (map lit pre) cmp (lit x1, lit x2) (lit y1, lit y2)
       b <- run $ solve s []
       assert (b == (or (map bol pre) || (bol x1, bol x2) `comp` (bol y1, bol y2)))
   where
    comp = head [ op | (cmp',op) <- cmps, cmp' == cmp ]
    cmps = [(False,(<)),(True,(<=))]

prop_compareList pre cmp xs ys =
  satfun $ \s lit bol ->
    do run $ lessOr s (map lit pre) cmp (map lit xs) (map lit ys)
       b <- run $ solve s []
       assert (b == (or (map bol pre) || map bol xs `comp` map bol ys))
   where
    comp = head [ op | (cmp',op) <- cmps, cmp' == cmp ]
    cmps = [(False,(<)),(True,(<=))]

------------------------------------------------------------------------------

prop_equalUnary pre (NonNegative m) (NonNegative n) =
  satfun $ \s lit bol ->
    do u1 <- run $ U.newUnary s m
       u2 <- run $ U.newUnary s n
       run $ equalOr s (map lit pre) u1 u2
       i1 <- pick (choose (0,m))
       i2 <- pick (choose (0,n))
       b <- run $ solve s [u1 U..>= i1, u2 U..<= i2]
       assert (b == (or (map bol pre) || i1 <= i2))
       if b then
         do a1 <- run $ U.modelValue s u1
            a2 <- run $ U.modelValue s u2
            assert (or (map bol pre) || a1 == a2)
        else
         do return ()

prop_notEqualUnary pre (NonNegative m) (NonNegative n) =
  satfun $ \s lit bol ->
    do u1 <- run $ U.newUnary s m
       u2 <- run $ U.newUnary s n
       run $ notEqualOr s (map lit pre) u1 u2
       i1 <- pick (choose (0,m))
       i2 <- pick (choose (0,n))
       b <- run $ solve s [u1 U..>= i1, u2 U..<= i2]
       monitor (whenFail (putStrLn ("solve=" ++ show b)))
       assert (b == (or (map bol pre) || (i1 /= i2 || i1 /= m || i2 /= 0)))
       if b then
         do a1 <- run $ U.modelValue s u1
            a2 <- run $ U.modelValue s u2
            assert (or (map bol pre) || a1 /= a2)
        else
         do return ()

prop_compareUnary pre incl (NonNegative m) (NonNegative n) =
  satfun $ \s lit bol ->
    do u1 <- run $ U.newUnary s m
       u2 <- run $ U.newUnary s n
       run $ lessOr s (map lit pre) incl u1 u2
       i1 <- pick (choose (0,m))
       i2 <- pick (choose (0,n))
       b <- run $ solve s [u1 U..>= i1, u2 U..<= i2]
       assert (b == (or (map bol pre) || (if incl then i1 <= i2 else i1 < i2)))
       if b then
         do a1 <- run $ U.modelValue s u1
            a2 <- run $ U.modelValue s u2
            assert (or (map bol pre) || (if incl then a1 <= a2 else a1 < a2))
        else
         do return ()

prop_compareUnaryPair pre incl (NonNegative m) x (NonNegative n) y =
  satfun $ \s lit bol ->
    do u1 <- run $ U.newUnary s m
       u2 <- run $ U.newUnary s n
       run $ lessOr s (map lit pre) incl (u1,lit x) (u2, lit y)
       i1 <- pick (choose (0,m))
       i2 <- pick (choose (0,n))
       b <- run $ solve s [u1 U..>= i1, u2 U..<= i2]
       monitor (whenFail (putStrLn ("solve=" ++ show b)))
       monitor (whenFail (putStrLn (show (i1,bol x) ++ " <= " ++ show (i2,bol y))))
       assert (b == (or (map bol pre) || (if incl then (i1,bol x) <= (i2, bol y) else (i1, bol x) < (i2, bol y))))
       if b then
         do a1 <- run $ U.modelValue s u1
            a2 <- run $ U.modelValue s u2
            monitor (whenFail (print (a1,a2)))
            assert (or (map bol pre) || (if incl then (a1,bol x) <= (a2, bol y) else (a1, bol x) < (a2, bol y)))
        else
         do return ()

------------------------------------------------------------------------------

prop_equalVal pre (NonEmpty xs) (NonEmpty ys) =
  satfun $ \s lit bol ->
    do v1 <- run $ V.newVal s (xs :: [OrdA])
       v2 <- run $ V.newVal s ys
       run $ equalOr s (map lit pre) v1 v2
       x <- pick (elements xs)
       y <- pick (elements ys)
       b <- run $ solve s [v1 V..= x, v2 V..= y]
       monitor (whenFail (putStrLn ("solve=" ++ show b)))
       assert (b == (or (map bol pre) || x == y))

prop_notEqualVal pre (NonEmpty xs) (NonEmpty ys) =
  satfun $ \s lit bol ->
    do v1 <- run $ V.newVal s (xs :: [OrdA])
       v2 <- run $ V.newVal s ys
       run $ notEqualOr s (map lit pre) v1 v2
       x <- pick (elements xs)
       y <- pick (elements ys)
       b <- run $ solve s [v1 V..= x, v2 V..= y]
       monitor (whenFail (putStrLn ("solve=" ++ show b)))
       assert (b == (or (map bol pre) || x /= y))

prop_compareVal pre incl (NonEmpty xs) (NonEmpty ys) =
  satfun $ \s lit bol ->
    do v1 <- run $ V.newVal s (xs :: [OrdA])
       v2 <- run $ V.newVal s ys
       run $ lessOr s (map lit pre) incl v1 v2
       x <- pick (elements xs)
       y <- pick (elements ys)
       b <- run $ solve s [v1 V..= x, v2 V..= y]
       monitor (whenFail (putStrLn ("solve=" ++ show b)))
       assert (b == (or (map bol pre) || (if incl then x <= y else x < y)))

------------------------------------------------------------------------------

prop_constraint pre axs k =
  satfun $ \s lit bol ->
    do run $ lessThanEqualOr s (map lit pre) (T.fromList [ (a,lit x) | (a, x) <- axs ]) (T.number k)
       b <- run $ solve s []
       monitor (whenFail (putStrLn ("solve=" ++ show b)))
       assert (b == (or (map bol pre) || (sum [ a | (a, x) <- axs, bol x] <= k)))

prop_newTerm (NonNegative k) (NonNegative n) =
  satfun $ \s lit bol ->
    do monitor ((k <= n) ==>)
       t <- run $ T.newTerm s n
       run $ greaterThanEqual s t (T.number k)
       b <- run $ solve s []
       assert b

------------------------------------------------------------------------------

testAll = $(quickCheckAll)

------------------------------------------------------------------------------

satfun h =
  monadicIO $
    do s  <- run $ newSolver
       ps <- run $ sequence [ newLit s | i <- [1..100] ]
       Blind bs <- pick $ Blind `fmap` sequence [ arbitrary | p <- ps ]
       run $ sequence_ [ addClause s [ if b then p else neg p ]
                       | (p,b) <- ps `zip` bs
                       ]

       let lit (LIT x) = if x > 0 then p else neg p
            where
             p = (true : ps) ?? ("lit",abs x - 1)

           bol (LIT x) = if x > 0 then p else not p
            where
             p = (True : bs) ?? ("bol",abs x - 1)

       h s lit bol

xs ?? (s,i) | i >= 0 && i < length xs = xs !! i
            | otherwise               = error ("index: " ++ s ++ " = " ++ show i)

data LIT = LIT Int
 deriving ( Eq, Ord )

instance Show LIT where
  show (LIT 1)    = "TRUE"
  show (LIT (-1)) = "FALSE"
  show (LIT x)    = show x

instance Arbitrary LIT where
  arbitrary =
    LIT `fmap`
      sized (\s -> let n = 1+(s`div` 8) in
              choose (-n, n) `suchThat` (/=0))

  shrink (LIT x) =
    [ LIT (-1) | x /= (-1) ] ++
    [ LIT 1    | abs x /= 1 ]
