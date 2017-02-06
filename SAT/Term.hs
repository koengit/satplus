{-|
Module      : SAT.Term
Description : Representing sums of products of literals

This module can be used to implement so-called pseudo-boolean constraints.
These are constraints of the form:

@
a1 * x1 + ... + ak * xk <= c
@

where @a1@..@an@ and @c@ are integer constants, and @x1@..@xk@ are SAT literals.

To add such a constraint, simply create two terms:

@
lhs = fromList [(a1,x1),..,(ak,xk)]
rhs = number c
@

and use any of the comparison constraints in the 'Order' type class, for
example:

@
lessThanEqual s lhs rhs
@

When adding a constraint, terms are normalized as much as possible (so the
user does not have to worry about this). When creating terms, almost no
normalization happens.
-}
module SAT.Term(
  -- * Terms
    Term
  , SAT.Term.number
  , newTerm
  , fromList
  , toList
  , (.+.)
  , (.-.)
  , (.*)
  , minus
  , minValue
  , SAT.Term.maxValue
  , SAT.Term.modelValue
  )
 where

import SAT as S
import SAT.Equal
import SAT.Order

import Data.List( sort, group, sortBy, groupBy, minimumBy )
import Data.Ord( comparing )

------------------------------------------------------------------------------

-- | A type to represent sums of products of literals.
data Term = Term{ toList :: [(Integer,Lit)] {- ^ Look inside a term. -} }
 deriving ( Eq, Ord )

instance Show Term where
  show (Term axs) =
    combine [ if x == true then show a else
                (if a == 1 then ""
               else if a == -1 then "-"
               else show a ++ "*")
                 ++ show x
            | (a,x) <- axs
            , a /= 0
            ]
   where
    combine []       = "0"
    combine [x]      = x
    combine (x:y:xs)
      | take 1 y == "-" = x ++ combine (y:xs)
      | otherwise       = x ++ "+" ++ combine (y:xs)

-- | Create a fresh term, between 0 and n.
newTerm :: Solver -> Integer -> IO Term
newTerm s n = go [] 1 n
 where
  go axs _ 0 =
    do return (Term axs)

  go axs k n | k <= n =
    do x <- newLit s
       go ((k,x):axs) (2*k) (n-k)

  go axs k n =
    do x <- newLit s
       sequence_ [ addClause s (neg x : c) | c <- atLeast (k-n) (sum (map fst axs)) axs ]
       return (Term ((n,x):axs))
   where
    atLeast b s _ | b <= 0 =
      []

    atLeast b s _ | s < b =
      [ [] ]

    atLeast b s ((a,x):axs) =
      [     xs | xs <- atLeast (b-a) (s-a) axs ] ++
      [ x : xs | xs <- atLeast b     (s-a) axs ]

-- | Create a constant term.
number :: Integer -> Term
number n = Term [(n,true)]

-- | Create a term from a list of products.
fromList :: [(Integer,Lit)] -> Term
fromList axs = Term axs

-- | Add two terms.
(.+.) :: Term -> Term -> Term
Term axs .+. Term bys = Term (axs ++ bys)

-- | Subtract two terms.
(.-.) :: Term -> Term -> Term
t1 .-. t2 = t1 .+. minus t2

-- | Multiply a term by a constant.
(.*) :: Integer -> Term -> Term
c .* Term axs = Term [ (c*a,x) | c /= 0, (a,x) <- axs, a /= 0 ]

-- | Negate a term.
minus :: Term -> Term
minus t = (-1) .* t

-- | Compute the minimum value of a term.
minValue :: Term -> Integer
minValue (Term axs) = sum [ a | (a,x) <- axs, x == true || (a < 0 && x /= false) ]

-- | Compute the maximum value of a term.
maxValue :: Term -> Integer
maxValue (Term axs) = sum [ a | (a,x) <- axs, x == true || (a > 0 && x /= false) ]

-- | Look at the value of a term.
modelValue :: Solver -> Term -> IO Integer
modelValue s (Term axs) =
  do ns <- sequence [ val a `fmap` S.modelValue s x | (a,x) <- axs ]
     return (sum ns)
 where
  val a False = 0
  val a True  = a

------------------------------------------------------------------------------

instance Equal Term where
  equalOr s pre t1 t2 =
    do lessThanEqualOr s pre t1 t2
       lessThanEqualOr s pre t2 t1

  notEqualOr s pre t1 t2 =
    do q <- newLit s
       lessThanOr s (q    :pre) t1 t2
       lessThanOr s (neg q:pre) t2 t1

instance Order Term where
  lessOr s pre incl t1 t2 =
    addNormedConstrOr s pre (norm ((t1 .-. t2) :<=: (if incl then 0 else (-1))))

------------------------------------------------------------------------------

data Constr = Term :<=: Integer

-- | Normalizes an LEQ-constraint.
-- After normalization:
-- 1. Constant literals do not occur
-- 2. Every literal only occurs at most once; either positively or negatively
-- 3. All factors are strictly positive
-- 4. We have divided by appropriate constants as much as we can
--    (..still an open problem for now..)
norm :: Constr -> Constr
norm = normFactorize
     . normPositive
     . normLiterals

normLiterals :: Constr -> Constr
normLiterals (Term axs :<=: k) =
  Term [ ax | ax@(a,x) <- axs1, a /= 0, x /= true ]
    :<=:
      (k - sum [ a | (a,x) <- axs1, x == true ])
 where
  keep x | x == true  = True
         | x == false = False
         | otherwise  = pos x

  axs0 = [ ax | ax@(_,x) <- axs
              , keep x
              ]
      ++ [ by | (a,x) <- axs
              , not (keep x)
              , by <- [ (-a, neg x), (a, true) ]
              ]

  axs1 = map (\(axs@((_,x):_)) -> (sum (map fst axs), x))
       $ groupBy eqLit
       $ sortBy cmpLit axs0

  (_,x) `eqLit`  (_,y) = x == y
  (_,x) `cmpLit` (_,y) = x `compare` y

normPositive :: Constr -> Constr
normPositive (Term axs :<=: k) =
  Term [ if a > 0 then (a, x) else (-a, neg x) | (a,x) <- axs, a /= 0 ]
    :<=:
      (k + sum [ -a | (a,x) <- axs, a < 0 ])

normFactorize :: Constr -> Constr
normFactorize constr@(Term axs :<=: k) =
  Term [ (a `div` n, x) | (a,x) <- axs ] :<=: (k `div` n)
 where
  n | null axs  = 1
    | otherwise = foldr1 gcd [ a | (a,_) <- axs ]

------------------------------------------------------------------------------

-- | Adds a normalized LEQ-constraint.
addNormedConstrOr :: Solver -> [Lit] -> Constr -> IO ()
addNormedConstrOr s pre (Term axs :<=: k) =
  do --putStrLn (show axs ++ " <= " ++ show k)
     go pre (reverse (sort axs)) k
 where
  -- all 1
  --go pre axs k | all (==1) (map fst axs) =
  --  do putStrLn (show pre ++ " | ALL 1: " ++ show (Term axs) ++ " <= " ++ show k)

  -- expand whenever possible
  go pre axs k | k <= 0 || n <= 8 || cs `lengthLeq` 64 =
    do --if not (null cs)
       --  then putStrLn (show pre ++ " | " ++ show axs ++ " <= " ++ show k)
       --  else return ()
       sequence_ [ do addClause s (pre ++ c) {- ; print (pre ++ c) -} | c <- cs ]
   where
    n  = length axs
    cs = expand axs (sum [ a | (a,_) <- axs ]) k
  
    expand _  m k | k < 0  = [[]]
    expand _  m k | m <= k = []
    expand ((a,x):axs) m k =
      [ neg x : c | c <- expand axs m' (k-a) ] ++
      expand axs m' k
     where
      m' = m-a

    (_:_)  `lengthLeq` 0 = False
    []     `lengthLeq` _ = True
    (_:xs) `lengthLeq` n = xs `lengthLeq` (n-1)

  -- case split on largest coefficient whenever possible
  go pre ((a,x):axs) k | a >= k || a >= sum [ a | (a,_) <- axs ] =
    do go (neg x : pre) axs (k-a)
       go pre axs k

  -- split according to p*A + B <= k --> A <= t & p*t + B <= k
  go pre axs@((a,_):_) k =
    do i <- newTerm s (maxI-minI)
       let t = number minI .+. i
       --putStrLn ("t = " ++ show t)
       --putStrLn (show minI ++ " <= t <= " ++ show maxI)
       --putStrLn (show (Term axs') ++ " <= t")
       --putStrLn (show p ++ " * t + " ++ show (Term bxs) ++ " <= " ++ show k)
       if p > 1 && myc <= c then error "cost!" else return ()
       lessThanEqualOr s pre (Term axs') t
       lessThanEqualOr s pre (p .* t .+. Term bxs) (number k)
   where
    n  = length axs
    n2 = n `div` 2

    (p, axs', bxs, minI, maxI) =
      minimumOn cost possibilities

    myc = cost (1, axs, [], 0, 0)
    c   = cost (p, axs', bxs, minI, maxI)

    cost (p, axs', bxs, minI, maxI) =
      if p == 1
        then (ca,va) `max` (cb,vb)
        else (cb, vb)
     where
      r  = maxI - minI
      v  = log2 r
      va = length axs' + v
      vb = length bxs + v
      ca = sum [ a     | (a,_) <- axs' ] + r
      cb = sum [ abs b | (b,_) <- bxs ] + p*r

      log2 0 = 0
      log2 n = 1 + log2 (n `div` 2)

    addRange (p, axs', bxs) = (p, axs', bxs, minI, maxI)
     where
      minL = 0 -- = minValue (Term axs')
      maxL = maxValue (Term axs')
      minR = (k - maxValue (Term bxs)) `div` p
      maxR = (k - minValue (Term bxs)) `div` p
      minI = minL `max` minR
      maxI = maxL `min` maxR

    possibilities =
      map addRange $
      [ (1, axs', take n2 axs)
      | let axs' = reverse (drop n2 axs)
      -- , tight 1 axs'
      ] ++
      [ (p, axs', bxs)
      | p <- ps
      , let dmxs = [ (a `aDivMod` p,x) | (a,x) <- axs ]
            axs' = [ (d,x) | ((d,_),x) <- dmxs, d /= 0 ]
            bxs  = [ (m,x) | ((_,m),x) <- dmxs, m /= 0 ]
      ]

    tight s []          = True
    tight s ((a,_):axs) = a <= s && tight (s+a) axs

    a `aDivMod` p
      | abs m2 < m1 = (d2,m2)
      | otherwise   = (d1,m1)
     where
      (d1,m1) = (a `div` p, a `mod` p)
      (d2,m2) = (d1+1,m1-p)

    ps = map head . group . sort $
      takeWhile (<=a) [2,3,5,7] ++
      as ++ gcds as
     where
      as = [ a | (a,_) <- axs, a /= 1 ]

    gcds []  = []
    gcds [_] = []
    gcds xs  = zipWith gcd xs (tail xs ++ [head xs])

minimumOn :: Ord b => (a -> b) -> [a] -> a
minimumOn f xs = snd . minimumBy (comparing fst) $ [ (f x, x) | x <- xs ]

------------------------------------------------------------------------------
