module SAT.Term where

import SAT as S
import SAT.Unary as U

------------------------------------------------------------------------------

data Term = Term [(Integer,Lit)] Integer

