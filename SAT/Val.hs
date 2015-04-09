module SAT.Val where

import SAT
import SAT.Util( usort )
import SAT.Bool( atMostOne )
import SAT.Equal

------------------------------------------------------------------------

newtype Val a = Val [(Lit,a)]
 deriving ( Eq, Ord, Show )

newVal :: Ord a => Solver -> [a] -> IO (Val a)
newVal s xs =
  case xs' of
    []    -> do error "newVal gets an empty list"
    [x]   -> do return (val x)
    [x,y] -> do q <- newLit s
                return (Val [(q,x),(neg q,y)])
    _     -> do qs <- sequence [ newLit s | x <- xs' ]
                addClause s qs
                atMostOne s qs
                return (Val (qs `zip` xs'))
 where
  xs' = usort xs

val :: a -> Val a
val x = Val [(true,x)]

domain :: Val a -> [a]
domain (Val qxs) = map snd qxs

(.=) :: Ord a => Val a -> a -> Lit
Val qxs .= x = go qxs
 where
  go []          = false
  go ((q,y):qxs) =
    case x `compare` y of
      LT -> false
      EQ -> true
      GT -> go qxs

------------------------------------------------------------------------

instance Ord a => Equal (Val a) where
  equalOr s pre p q =
    sequence_
    [ case pqx of
        (Just p,  Nothing, _) -> addClause s (neg p : pre)
        (Nothing, Just q,  _) -> addClause s (neg q : pre)
        (Just p,  Just q,  _) -> addClause s (neg p : q : pre)
    | pqx <- stitch p q
    ]

  notEqualOr s pre p q =
    sequence_
    [ case pqx of
        (Just p, Just q, _) -> addClause s (neg p : neg q : pre)
        _                   -> return ()
    | pqx <- stitch p q
    ]

stitch :: Ord a => Val a -> Val a -> [(Maybe Lit, Maybe Lit, a)]
stitch (Val pxs) (Val qys) = go pxs qys
 where
  go [] qys = [ (Nothing, Just q, y) | (q,y) <- qys ]
  go pxs [] = [ (Just p, Nothing, x) | (p,x) <- pxs ]
  go ((p,x):pxs) ((q,y):qys) =
    case x `compare` y of
      LT -> (Just p,  Nothing, x) : go pxs ((q,y):qys)
      EQ -> (Just p,  Just q,  x) : go pxs qys
      GT -> (Nothing, Just q,  y) : go ((p,x):pxs) qys

------------------------------------------------------------------------
