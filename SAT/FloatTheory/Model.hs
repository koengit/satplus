module SAT.FloatTheory.Model (
    FloatModel
  , evalFloatExpr
  , evalFloatExprGradient
  , testModel
  ) where

import SAT.FloatTheory.Constraints
import qualified Data.Vector.Storable as V
import Debug.Trace
type Vec a = V.Vector a
type FloatModel = Vec Double

testModel :: [FloatConstraint] -> FloatModel -> Bool
testModel cs m = foldl (&&) True (map (testConstraint (1e-2) m) (trace "testModel" (traceShowId cs)))

testConstraint :: Double -> FloatModel -> FloatConstraint -> Bool
testConstraint tol m (CEqz t) = abs (evalFloatExpr m t) < tol
testConstraint tol m (CLez t) = (evalFloatExpr m t) < tol

evalFloatExpr :: FloatModel -> FloatExpr -> Double
evalFloatExpr m = evalT
  where
    evalT (TConst c) = c
    evalT (TVar v) = (V.!) m v
    evalT (TAdd a b) = (+) (evalT a) (evalT b)
    evalT (TSub a b) = (-) (evalT a) (evalT b)
    evalT (TMul a b) = (*) (evalT a) (evalT b)
    evalT (TSqr a) = (^2) (evalT a)

evalFloatExprGradient :: FloatModel -> FloatExpr -> Vec Double
evalFloatExprGradient model = V.fromList . snd . evalT
  where
    evalT :: FloatExpr -> (Double,[Double])
    evalT (TConst c) = (c, [ 0 | _ <- V.toList model ])
    evalT (TVar v)   = ((V.!) model v, 
        [ if i == v then 1 else 0  | (i,_) <- zip [0..] (V.toList model) ])
    evalT (TAdd a b) = (xa + xb, [da + db | (da,db) <- zip vda vdb] )
      where ((xa,vda),(xb,vdb)) = (evalT a, evalT b)
    evalT (TSub a b) = (xa - xb, [da - db | (da,db) <- zip vda vdb] )
      where ((xa,vda),(xb,vdb)) = (evalT a, evalT b)
    evalT (TMul a b) = (xa * xb, [db*xa + da*xb | (da,db) <- zip vda vdb] )
      where ((xa,vda),(xb,vdb)) = (evalT a, evalT b)
    evalT (TSqr a) = (xa*xa, [2*da*xa |da <- vda])
      where (xa,vda) = (evalT a)

