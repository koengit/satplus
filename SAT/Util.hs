module SAT.Util where

import SAT
import Data.List( sort, group )

------------------------------------------------------------------------

here :: (Solver -> [Lit] -> abc) -> (Solver -> abc)
here f = \s -> f s []

------------------------------------------------------------------------

usort :: Ord a => [a] -> [a]
usort = map head . group . sort

------------------------------------------------------------------------
