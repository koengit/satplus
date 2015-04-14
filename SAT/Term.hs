module SAT.Term where

import SAT as S
import SAT.Unary as U
import SAT.Binary as B

------------------------------------------------------------------------------

data Term = Term [(Integer,Lit)] Integer


