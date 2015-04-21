{-|
Module      : SAT.Value
Description : Reading off the value of things in models
-}
{-# LANGUAGE TypeFamilies #-}
module SAT.Value where

import SAT ( Solver )
import qualified SAT       as S
import qualified SAT.Val   as V
import qualified SAT.Unary as U
import qualified SAT.Term  as T

import Control.Monad ( liftM2, liftM3 )

------------------------------------------------------------------------------

-- | A class for symbolic objects that have Haskell values in models.
class Value a where
  -- | The Haskell type for the symbolic object a.
  type Type a

  -- | Return the value of the object in the current model.
  -- /Only use if 'solve' has returned True!/
  getValue :: Solver -> a -> IO (Type a)

------------------------------------------------------------------------------

instance Value () where
  type Type () = ()

  getValue _ _ = return ()

instance Value S.Lit where
  type Type S.Lit = Bool

  getValue = S.modelValue

instance Value Bool where
  type Type Bool = Bool

  getValue _ = return

instance Value Int where
  type Type Int = Int

  getValue _ = return

instance Value Integer where
  type Type Integer = Integer

  getValue _ = return

------------------------------------------------------------------------------

instance (Value a, Value b) => Value (a,b) where
  type Type (a,b) = (Type a, Type b)

  getValue s (x,y) = liftM2 (,) (getValue s x) (getValue s y)

instance (Value a, Value b, Value c) => Value (a,b,c) where
  type Type (a,b,c) = (Type a, Type b, Type c)

  getValue s (x,y,z) = liftM3 (,,) (getValue s x) (getValue s y) (getValue s z)

instance (Value a, Value b) => Value (Either a b) where
  type Type (Either a b) = Either (Type a) (Type b)

  getValue s (Left x)  = Left  `fmap` getValue s x
  getValue s (Right y) = Right `fmap` getValue s y

instance Value a => Value [a] where
  type Type [a] = [Type a]

  getValue s xs = sequence [ getValue s x | x <- xs ]

instance Value a => Value (Maybe a) where
  type Type (Maybe a) = Maybe (Type a)

  getValue s Nothing  = return Nothing
  getValue s (Just x) = Just `fmap` getValue s x

------------------------------------------------------------------------------

instance Value (V.Val a) where
  type Type (V.Val a) = a

  getValue = V.modelValue

instance Value U.Unary where
  type Type U.Unary = Int

  getValue = U.modelValue

instance Value T.Term where
  type Type T.Term = Integer

  getValue = T.modelValue

------------------------------------------------------------------------------

