module SAT.FloatTheory.Constraints (
  FloatExpr(..),
  FloatConstraint(..),
  VarId,
  vars, cvars, 
  number,
  (.+.), (.-.), (.*.), square,
  (.==.), (.<=.), (.>=.)
  ) where

type VarId = Int

data FloatConstraint = 
    CLez FloatExpr
  | CEqz FloatExpr
  deriving (Ord, Eq)

instance Show FloatConstraint where
  show (CLez e) = (show e) ++ " <= 0"
  show (CEqz e) = (show e) ++ " == 0"

cvars :: FloatConstraint -> [VarId]
cvars (CLez a) = vars a
cvars (CEqz a) = vars a

data FloatExpr = 
    TConst Double
  | TVar VarId
  | TAdd FloatExpr FloatExpr
  | TSub FloatExpr FloatExpr
  | TMul FloatExpr FloatExpr
  | TSqr FloatExpr
  deriving (Ord, Eq)

instance Show FloatExpr where
  show (TConst d) = show d
  show (TVar v) = "x" ++ (show v)
  show (TAdd a b) = "(" ++ (show a) ++ " + " ++ (show b) ++ ")"
  show (TSub a b) = "(" ++ (show a) ++ " - " ++ (show b) ++ ")"
  show (TMul a b) = "(" ++ (show a) ++ " * " ++ (show b) ++ ")"
  show (TSqr a) = "(" ++ (show a) ++ "^2)"

vars :: FloatExpr -> [VarId]
vars (TConst _) = []
vars (TVar v) = [v]
vars (TSqr a) = (vars a) 
vars (TAdd a b) = (vars a) ++ (vars b)
vars (TSub a b) = (vars a) ++ (vars b)
vars (TMul a b) = (vars a) ++ (vars b)

(.+.) a (TConst 0) = a
(.+.) (TConst 0) b = b
(.+.) a b = TAdd a b

(.-.) a (TConst 0) = a
(.-.) a b = TSub a b

(.*.) a (TConst 0) = TConst 0
(.*.) (TConst 0) b = TConst 0
(.*.) a (TConst 1) = a
(.*.) (TConst 1) b = b
(.*.) a b = TMul a b

square (TConst 0) = TConst 0
square (TConst 1) = TConst 1
square x = TSqr x

(.==.) a b = CEqz (a .-. b)
(.<=.) a b = CLez (a .-. b)
(.>=.) a b = b .<=. a

number = TConst
