# SAT+

This is a Haskell library for constraint programming using a SAT-solver,
in particular MiniSAT.

## Basic MiniSAT

The basic MiniSAT functions are:

```haskell
newSolver  :: IO Solver
newLit     :: Solver -> IO Lit
addClause  :: Solver -> [Lit] -> IO ()
solve      :: Solver -> [Lit] -> IO Bool
modelValue :: Solver -> Lit -> IO Bool
conflict   :: Solver -> IO [Lit]

valueMaybe      :: Solver -> Lit -> IO (Maybe Bool)
modelValueMaybe :: Solver -> Lit -> IO (Maybe Bool)
```

## Boolean functions

This library also supports boolean operators:

```haskell
andl, orl, xorl :: Solver -> [Lit] -> IO Lit
```
And binary operators:

```haskell
implies :: Solver -> Lit -> Lit -> IO Lit
equiv   :: Solver -> Lit -> Lit -> IO Lit
```

## Values

We also have implemented a convenient type that links Haskell values
with the SAT-solver:

```haskell
type Val a

newVal :: Ord a => Solver -> [a] -> IO (Val a)
val    ::          a -> Val a
(.=)   :: Ord a => Val a -> a -> Lit
domain ::          Val a -> [a]
```

We also provide:

```haskell
modelValue :: Solver -> Val a -> IO a
```

## Equality

We often want to add constraints that say that two things are equal,
or not equal, to each other.

```haskell
class Equal a where
  equal    :: Solver -> a -> a -> IO ()
  notEqual :: Solver -> a -> a -> IO ()
  ...
```

Instances of this class are:

```haskell
instance Equal ()
instance Equal Lit
instance (Equal a, Equal b) => Equal (a,b)
instance (Equal a, Equal b) => Equal (Either a b)
instance Equal a => Equal [a]
instance Equal a => Equal (Maybe a)
instance Ord a => Equal (Val a)
instance Equal Unary
instance Equal Binary
```

## Order

We often want to add constraints that say that one thing is smaller than
another.

```haskell
class Order a where
  lessThan         :: Solver -> a -> a -> IO ()
  lessThanEqual    :: Solver -> a -> a -> IO ()
  greaterThan      :: Solver -> a -> a -> IO ()
  greaterThanEqual :: Solver -> a -> a -> IO ()
  ...
```

Instances of this class are:

```haskell
instance Order ()
instance Order Lit
instance (Order a, Order b) => Equal (a,b)
instance (Order a, Order b) => Equal (Either a b)
instance Order a => Order [a]
instance Order a => Order (Maybe a)
instance Ord a => Order (Val a)
instance Order Unary
instance Order Binary
```

## Unary numbers

We have support for unary numbers (represented as sorted lists of Lits).
These are handy when you want to count number of literals in a set being
true, for example.

```haskell
type Unary

zero   :: Unary
one    :: Lit -> Unary
number :: Int -> Unary

count    :: Solver ->        [Lit] -> IO Unary
countMax :: Solver -> Int -> [Lit] -> IO Unary

add     :: Solver -> Unary -> Unary -> IO Unary
addList :: Solver -> [Unary] -> IO Unary

(.<=), (.<), (.>=), (.>) :: Unary -> Int -> Lit
```

We also provide:

```haskell
modelValue :: Solver -> Unary -> IO Int
```

## Binary numbers

We have support for binary numbers (represented as lists of Lits).
These are handy when you want to represent numbers that are large.

```haskell
type Binary

zero   :: Binary
one    :: Lit -> Binary
number :: Integer -> Binary

count    :: Solver ->        [Lit] -> IO Binary
countMax :: Solver -> Int -> [Lit] -> IO Binary

add     :: Solver -> Binary -> Binary -> IO Binary
addList :: Solver -> [Binary] -> IO Binary
```

We also provide:

```haskell
modelValue :: Solver -> Binary -> IO Integer
```

## Terms

We also support linear arithmetic terms over a base type of variables
(for example Lit, Unary, or Binary).

```haskell
type Term a

var   :: a -> Term a
con   :: Integer -> Term a
(.+.) :: Term a -> Term a -> Term a
(.*)  :: Integer -> Term a -> Term a
```

For these, we can generate equality and ordering constraints:

```haskell
instance Equal a => Equal (Term a)
instance Order a => Order (Term a)
```

We also provide:

```haskell
modelValue :: Num b => (Solver -> a -> IO b) -> Solver -> Term a -> IO b
```

## Minimization / Maximization

We also support finding solutions that are minimized or maximized w.r.t.
a particular argument.

```haskell
minimize :: Order a => Solver -> [Lit] -> a -> IO Bool
maximize :: Order a => Solver -> [Lit] -> a -> IO Bool
```
    
These functions will only find a minimal/maximal *solution*. In order to
also *constrain* the problem to not exceed the found solution after the
minimization/maximization, use these:

```haskell
minimizeAndConstrain :: Order a => Solver -> [Lit] -> a -> IO Bool
maximizeAndConstrain :: Order a => Solver -> [Lit] -> a -> IO Bool
```

TODO: Add a verbose mode. Add a timeout option of some sort.
