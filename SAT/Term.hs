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
  , fromList
  , toList
  , (.+.)
  , (.-.)
  , (.*)
  , minus
  , SAT.Term.modelValue
  )
 where

import SAT as S
import SAT.Unary as U
import SAT.Equal
import SAT.Order

import Data.List( sortBy, groupBy )

------------------------------------------------------------------------------

-- | A type to represent sums of products of literals.
data Term = Term{ toList :: [(Integer,Lit)] {- ^ Look inside a term. -} }
 deriving ( Eq, Ord, Show )

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
addNormedConstrOr s pre (Term axs :<=: k)
  | k < 0                         = addClause s pre
  | sum [ a | (a,_) <- axs ] <= k = return ()
  | otherwise                     = go zero axs k
 where
  go u axs 0 =
    do addClause s (u .<= 0 : pre)
       sequence_ [ addClause s (neg x : pre) | (_,x) <- axs ]

  go u axs k =
    do u' <- addList s (u : [ digit x | (a,x) <- axs, odd a ])
       go ((if even k then U.succ u' else u') // 2) axs2 (k `div` 2)
   where
    axs2 = [ (a `div` 2, x) | (a,x) <- axs, a > 1 ]

------------------------------------------------------------------------------
