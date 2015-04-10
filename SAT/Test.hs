{-# LANGUAGE TemplateHaskell #-}
module SAT.Test where

import SAT
import SAT.Bool

import Test.QuickCheck
import Test.QuickCheck.Modifiers
import Test.QuickCheck.Monadic
import Test.QuickCheck.All

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
             p = (true : ps) !! (abs x - 1)
       
           bol (LIT x) = if x > 0 then p else not p
            where
             p = (True : bs) !! (abs x - 1)
       
       h s lit bol

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
