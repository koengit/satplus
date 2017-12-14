-- 
-- Interval arithmetic for Double
-- (Not generic like the intervals package on hackage, because
--  of the need to check NaN and have 0*Inf=0 in some places)

module SAT.FloatTheory.Interval (
  Interval,
  interval,
  empty,
  singleton,
  whole,
  positive,
  negative,
  lowerBound,
  upperBound,
  member,
  finiteSample,
  intersection,
  symmetric,
  add, sub, mul, invmul, pow, sqrt
  ) where

import Prelude hiding (sqrt)
import qualified Prelude (sqrt)

infty = (read "Infinity") :: Double
nan = (read "NaN") :: Double

data Interval = Interval Double Double | Empty
  deriving (Show, Eq, Ord)

isFinite x = (not (isInfinite x)) && (not (isNaN x))

interval :: Double -> Double -> Interval
interval a b
  | (not $ isNaN a) && (not $ isNaN b) && a <= b = Interval a b
  | otherwise = Empty

singleton :: Double -> Interval
singleton x
  | isNaN x = Empty
  | otherwise = Interval x x

empty :: Interval
empty = Empty

whole :: Interval
whole = Interval (-infty) infty

positive :: Interval
positive = Interval 0 infty

negative :: Interval
negative = Interval (-infty) 0

lowerBound :: Interval -> Double
lowerBound (Interval a b) = a
lowerBound Empty = nan

upperBound :: Interval -> Double
upperBound (Interval a b) = b
upperBound Empty = nan

member :: Double -> Interval -> Bool
member x (Interval a b) = a <= x && x <= b
member _ Empty = False

symmetric :: Interval -> Interval
symmetric (Interval a b) = Interval (-m) m
  where m = max (abs a) (abs b)
symmetric Empty = Empty

finiteSample :: Interval -> Double
finiteSample i@(Interval a b)
  | isFinite a && isFinite b = (a+b)/2.0
  | isFinite a = a
  | isFinite b = b
  | member 0.0 i = 0.0
  | otherwise = (a+b)/2.0
finiteSample Empty = nan

intersection :: Interval -> Interval -> Interval
intersection a@(Interval a1 a2) b@(Interval b1 b2)
  | noOverlap a b = Empty
  | otherwise = Interval (max a1 b1) (min a2 b2)
intersection _ _ = Empty

noOverlap :: Interval -> Interval -> Bool
noOverlap (Interval a1 a2) (Interval b1 b2) = a2 < b1 || b2 < a1
noOverlap _ _ = True

mapIncreasing :: (Double -> Double) -> Interval -> Interval
mapIncreasing f (Interval a b) = Interval (f a) (f b)
mapIncreasing _ Empty = Empty

mapDecreasing :: (Double -> Double) -> Interval -> Interval
mapDecreasing f (Interval a b) = Interval (f b) (f a)
mapDecreasing _ Empty = Empty

add :: Interval -> Interval -> Interval
add (Interval a1 a2) (Interval b1 b2) = Interval (a1+b1) (a2+b2)
add _ _ = Empty

sub :: Interval -> Interval -> Interval
sub (Interval a1 a2) (Interval b1 b2) = Interval (a1-b2) (a2-b1)
sub _ _ = Empty

-- float multiplication, but with 0*Inf = 0 (infinity as a limit)
dmul :: Double -> Double -> Double
dmul a b
 | isInfinite a && b == 0.0 = 0.0
 | isInfinite b && a == 0.0 = 0.0
 | otherwise = a*b

mul :: Interval -> Interval -> Interval
mul (Interval a1 a2) (Interval b1 b2) = Interval (minimum combs) (maximum combs)
  where combs = [dmul a1 b1, dmul a1 b2, dmul a2 b1, dmul a2 b2]
mul _ _ = Empty

invmul :: Interval -> Interval -> Interval
invmul a@(Interval a1 a2) b@(Interval b1 b2) 
  -- Expect bugs
  | not (member 0.0 b) = Interval (minimum combs) (maximum combs)
  | b == singleton 0.0 = if (member 0.0 a) then whole else empty
  | b1 == 0.0 && a == singleton 0.0 = a
  | b1 == 0.0 && a2 < 0.0 = Interval (-infty) (a2/b2)
  | b1 == 0.0 && a1 < 0.0 = whole 
  | b1 == 0.0 && a1 == 0.0 = Interval 0 infty
  | b1 == 0.0 = Interval (a1/b2) (infty)
  | b2 == 0.0 && a == singleton 0.0 = a
  | b2 == 0.0 && a2 < 0.0 = Interval (a2/b1) (infty)
  | b2 == 0.0 && a1 < 0.0 = whole
  | b2 == 0.0 = Interval (a1/b1) (infty)
  | a == singleton 0.0 = a
  | otherwise = whole
  where 
    ddiv = (/)
    combs = [ddiv a1 b1, ddiv a1 b2, ddiv a2 b1, ddiv a2 b2]
invmul _ _ = Empty

pow :: Interval -> Int -> Interval
pow x 0 = singleton 1
pow x n | n > 0 = f x (n-1) x
                  where f _ 0 y = y
                        f x n y = g x n  where
                                  g x n | even n  = g (mul x x) (n `quot` 2)
                                        | otherwise = f x (n-1) (mul x y)
pow _ _            = error "negative exponent"

sqrt :: Interval -> Interval
sqrt = mapIncreasing Prelude.sqrt
