module Data.Array

import public Data.Array.Core
import public Data.Array.Index
import public Data.Array.Indexed
import Syntax.T1

%default total

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
Eq a => Eq (Array a) where
  A _ a1 == A _ a2 = heq a1 a2

export %inline
Ord a => Ord (Array a) where
  compare (A _ a1) (A _ a2) = hcomp a1 a2

export
Show a => Show (Array a) where
  showPrec p (A size arr) = showCon p "A" (showArg size ++ showArg arr)

export
Functor Array where
  map f (A s arr) = A s $ map f arr

export
Foldable Array where
  foldr f x (A _ arr) = foldr f x arr
  foldl f x (A _ arr) = foldl f x arr
  toList (A _ arr)    = toList arr
  null   (A _ arr)    = null arr

export
Traversable Array where
  traverse f (A s arr) = A s <$> traverse f arr

export
Semigroup (Array a) where
  A m a1 <+> A n a2 = A (m+n) $ append a1 a2

export
Monoid (Array a) where
  neutral = A 0 empty

bind : Array a -> (a -> Array b) -> Array b
bind x f =
  let sb := foldl (\sa,v => sa :< f v) [<] x
   in A (SnocSize sb) (snocConcat sb)

export
Applicative Array where
  pure v = A 1 $ fill 1 v
  af <*> av = bind af (\fun => map fun av)

export
Monad Array where
  (>>=) = bind

export
Alternative Array where
  empty = A 0 empty
  A 0 _ <|> ys = ys
  xs    <|> _  = xs

--------------------------------------------------------------------------------
--          Initializing Arrays
--------------------------------------------------------------------------------

export %inline
fromList : (ls : List a) -> Array a
fromList ls = A _ $ arrayL ls

export %inline
fill : (n : Nat) -> a -> Array a
fill n v = A n $ fill n v

export %inline
generate : (n : Nat) -> (Fin n -> a) -> Array a
generate n f = A n $ generate n f

export %inline
iterate : (n : Nat) -> (a -> a) -> a -> Array a
iterate n f x = A n $ iterate n f x

export %inline
force : Array a -> Array a
force (A s arr) = A s $ force arr

--------------------------------------------------------------------------------
--          Subarrays
--------------------------------------------------------------------------------

export %inline
take : Nat -> Array a -> Array a
take k (A size arr) with (k <= size) proof eq
  _ | True  = A k $ take k arr @{lteOpReflectsLTE _ _ eq}
  _ | False = A size arr

export %inline
drop : Nat -> Array a -> Array a
drop n (A size arr) = A (size `minus` n) (drop n arr)

export %inline
filter : (a -> Bool) -> Array a -> Array a
filter f (A size arr) = filter f arr

export %inline
mapMaybe : (a -> Maybe b) -> Array a -> Array b
mapMaybe f (A size arr) = mapMaybe f arr
