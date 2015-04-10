module SAT.Util where

import SAT
import Data.List( sort, group )

------------------------------------------------------------------------

-- | Turn a Solver-function with prefix into a Solver-function without prefix.
--
-- All constraint-generating functions in this library have two versions: One
-- that unconditionally adds the constraint, and one that makes use of a
-- /disjunctive prefix/.
-- When the prefix is used, the actual constraint that is added is the
-- disjunction between the prefix and the constraint the function generates.
--
-- The naming scheme works as follows. If the unconditional function is:
--
-- @someConstraint :: Solver -> ... -> IO ()@
--
-- then the prefixed version is:
--
-- @someConstraintOr :: Solver -> [Lit] -> ... -> IO ()@
--
-- It is always the case that:
--
-- @someConstraint = unconditionally someConstraintOr@
--
-- The disjunctive prefix is typically used to conditionally add the
-- constraint. For example, if we say:
--
-- @someConstraintOr s [neg x] ...@
-- 
-- (i.e. the prefix is @[neg x]@), then the someConstraint is only asserted
-- when @x@ is True.
--
-- If the prefix is empty, it degenerates to the function without prefix.
unconditionally :: (Solver -> [Lit] -> abc) -> (Solver -> abc)
unconditionally f = \s -> f s []

------------------------------------------------------------------------

-- | Sort and remove duplicates.
usort :: Ord a => [a] -> [a]
usort = map head . group . sort

------------------------------------------------------------------------
