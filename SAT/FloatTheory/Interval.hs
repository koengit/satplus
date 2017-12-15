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
  negate,
  hull,
  abs,
  symmetric,
  add, sub, mul, invmul, square, sqrt
  ) where

import Prelude hiding (sqrt, negate, abs)
import qualified Prelude (sqrt, negate, abs)

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

negate :: Interval -> Interval
negate (Interval a b) = Interval (min (-a) (-b)) (max (-a) (-b))
negate _ = Empty

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
  where m = max (Prelude.abs a) (Prelude.abs b)
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

hull :: Interval -> Interval -> Interval
hull (Interval a1 a2) (Interval b1 b2) = Interval (min a1 b1) (max a2 b2)
hull Empty x = x
hull x _ = x

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

square :: Interval -> Interval
square a = abs (mul a a)

abs :: Interval -> Interval
abs x@(Interval a b)
  | a >= 0 = x
  | b <= 0 = negate x
  | otherwise = interval 0 (max (-a) b)
abs _ = Empty

sqrt :: Interval -> Interval
sqrt a = mapIncreasing Prelude.sqrt (abs a)
