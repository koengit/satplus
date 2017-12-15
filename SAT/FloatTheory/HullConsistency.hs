module SAT.FloatTheory.HullConsistency (
  hullConsistency, Box
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (catMaybes, fromJust, maybe, isJust)
import Control.Monad.State
import Data.Tree
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

import SAT.FloatTheory.Interval (Interval, interval)
import qualified SAT.FloatTheory.Interval as I
import SAT.FloatTheory.Constraints

type Box = V.Vector Interval

data IConstraint =
    ICLez Interval ITerm
  | ICEqz Interval ITerm

instance Show IConstraint where
  show = drawTree . icToTree

icToTree :: IConstraint -> Tree String
icToTree (ICLez i t) = Node ("(<0) [" ++ (show i) ++ "]") [itermToTree t]
icToTree (ICEqz i t) = Node ("(=0) [" ++ (show i) ++ "]") [itermToTree t]

data ITerm =
    ITConst Interval
  | ITVar Interval VarId
  | ITSqr Interval ITerm
  | ITAdd Interval ITerm ITerm
  | ITSub Interval ITerm ITerm
  | ITMul Interval ITerm ITerm

instance Show ITerm where
  show = drawTree . itermToTree

itermToTree :: ITerm -> Tree String
itermToTree (ITConst i)   = Node ("Const [" ++ (show i) ++ "]") []
itermToTree (ITVar i v)   = Node ("Var x" ++ (show v) ++ 
                                    " [" ++ (show i) ++ "]") []
itermToTree (ITSqr i a)   = Node ("(^2) [" ++ (show i) ++ "]") 
                               [itermToTree a]
itermToTree (ITAdd i a b) = Node ("(+) [" ++ (show i) ++ "]")
                               [itermToTree a, itermToTree b]
itermToTree (ITSub i a b) = Node ("(-) [" ++ (show i) ++ "]") 
                               [itermToTree a, itermToTree b]
itermToTree (ITMul i a b) = Node ("(*) [" ++ (show i) ++ "]") 
                               [itermToTree a, itermToTree b]

initIntervalTree :: Box -> FloatConstraint -> IConstraint
initIntervalTree b = sc
  where
    sc (CLez t) = ICLez I.negative (st t)
    sc (CEqz t) = ICEqz (I.singleton 0) (st t)
    st (TConst c) = ITConst (I.singleton c)
    st (TVar v) = ITVar ((V.!) b v) v
    st (TSqr a) = ITSqr I.whole (st a)
    st (TAdd a b) = ITAdd I.whole (st a) (st b)
    st (TSub a b) = ITSub I.whole (st a) (st b)
    st (TMul a b) = ITMul I.whole (st a) (st b)


(.&) = I.intersection
itermI :: ITerm -> Interval
itermI (ITConst i) = i
itermI (ITVar i _) = i
itermI (ITSqr i _) = i
itermI (ITAdd i _ _) = i
itermI (ITSub i _ _) = i
itermI (ITMul i _ _) = i

hullConsistency :: Int -> Double -> Maybe Int -> [FloatConstraint] -> Maybe Box
hullConsistency numVars relTol maxIters cs = hc4 constraintSet whole
  where
    cmap  = Map.fromListWith (\a b -> Set.union a b) 
              [ (v, Set.singleton c) | c <- cs, v <- cvars c ]
    whole = V.fromList [ I.whole | _ <- [0..(numVars-1)] ]
    constraintSet = Set.fromList cs

    hc4 :: Set FloatConstraint -> Box -> Maybe Box
    hc4 items box
      | Set.null items = Just box
      | maybe False (any (> relTol)) (fmap relativeChange newBox) = 
          hc4 (Set.union propagateSet rest) (fromJust newBox)
      | isJust newBox = hc4 rest (fromJust newBox)
      | otherwise = Nothing
      where 
        (item, rest) = (Set.elemAt 0 items, Set.deleteAt 0 items)
        newBox = hc4revise item box

        relativeChange b = [ maximum (0:[abs (1.0 - (bound ia)/(bound ib))
                                       | bound <- [I.lowerBound, I.upperBound]
                                       , bound ib /= 0.0])
                           | (ia,ib) <- zip (V.toList b) (V.toList box)]

        changedVars b = [ i | (i,d) <- zip [0..] (relativeChange b), d > relTol]

        propagateSet = Set.unions ((Set.singleton item):(catMaybes propagateTo))
        propagateTo = map (\v -> Map.lookup v cmap) (changedVars $ fromJust newBox) 

    hc4revise :: FloatConstraint -> Box -> Maybe Box
    hc4revise c b = backwardProp b (forwardEval (initIntervalTree b c))

    forwardEval :: IConstraint -> IConstraint
    forwardEval = sc
      where
        sc (ICLez i t) = ICLez (i .& (iv (st t))) (st t)
        sc (ICEqz i t) = ICEqz (i .& (iv (st t))) (st t)
    
        st :: ITerm -> ITerm
        st (ITAdd i a b) = comb I.add ITAdd a b
        st (ITSub i a b) = comb I.sub ITSub a b
        st (ITMul i a b) = comb I.mul ITMul a b
        st (ITSqr i a) = comb1 I.square ITSqr a
        st t = t
    
        iv = itermI
        comb op cstr a b = cstr (op (iv ta) (iv tb)) ta tb
          where ta = st a
                tb = st b
        comb1 op cstr a = cstr (op (iv ta)) ta
          where ta = st a

    backwardProp :: Box -> IConstraint -> Maybe Box
    backwardProp b c = execState (sc c) (Just b)
    
      where
        sc :: IConstraint -> State (Maybe Box) ()
        sc (ICLez i t) = update i t
        sc (ICEqz i t) = update i t
        iv = itermI
    
        update :: Interval -> ITerm -> State (Maybe Box) ()
        update ri = st
          where
            st :: ITerm -> State (Maybe Box) ()
            st (ITVar i v)
              | ri .& i == I.empty = put Nothing -- Fail
              | otherwise = modify (fmap (V.modify (\a -> MV.write a v (ri .& i))))
            st (ITConst i)
              | ri .& i == I.empty = put Nothing -- Fail
              | otherwise = return ()
    
            st (ITAdd i a b) = do update ((i .& ri) `I.sub` (iv b)) a
                                  update ((i .& ri) `I.sub` (iv a)) b
            st (ITSub i a b) = do update ((i .& ri) `I.add` (iv b)) a
                                  update ((iv a) `I.sub` (i .& ri)) b
            st (ITMul i a b) = do update ((i .& ri) `I.invmul` (iv b)) a
                                  update ((i .& ri) `I.invmul` (iv a)) b
            st (ITSqr i a) = update (I.symmetric (I.sqrt (i .& ri))) a 
    
