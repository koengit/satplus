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
  )
 where

import SAT as S
import SAT.Unary as U
import SAT.Equal
import SAT.Order

import Data.List( sortBy, groupBy )

------------------------------------------------------------------------------

-- | A type to represent sums of products of literals.
data Term = Term{ toList :: [(Integer,Lit)] }

-- | Create a constant term.
number :: Integer -> Term
number n = Term [(n,true)]

-- | Add two terms.
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
-- 4. We have divided the constraint by factors as much as we can
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
normFactorize = id

------------------------------------------------------------------------------

-- | Adds a normalized LEQ-constraint.
addNormedConstrOr :: Solver -> [Lit] -> Constr -> IO ()
addNormedConstrOr s pre (Term axs :<=: k)
  | sum [ a | (a,_) <- axs ] <= k = return ()
  | otherwise                     = go zero axs k
 where
  go u axs k | k < 0 =
    do addClause s pre

  go u axs 0 =
    do addClause s (u .<= 0 : pre)
       sequence_ [ addClause s (neg x : pre) | (_,x) <- axs ]

  go u axs k =
    do u' <- addList s (u : [ digit x | (a,x) <- axs, odd a ])
       if even k then
         do x <- modulo s u' 2
            go (u' // 2) ((1,x .>= 1):axs2) (k `div` 2)
        else
         do go (u' // 2) axs2 (k `div` 2)
   where
    axs2 = [ (a `div` 2, x) | (a,x) <- axs, a > 1 ]

------------------------------------------------------------------------------
