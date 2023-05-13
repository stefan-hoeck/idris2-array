module Data.Array

import public Data.Array.Core
import public Data.Array.Index
import public Data.Array.Indexed
import public Data.Array.Mutable

%default total

||| An immutable array paired with its size (= number of values).
public export
record Array a where
  constructor A
  size : Nat
  arr  : IArray size a

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

--------------------------------------------------------------------------------
--          Initializing Arrays
--------------------------------------------------------------------------------

export
empty : Array a
empty = A 0 empty

export %inline
fromList : (ls : List a) -> Array a
fromList ls = A _ $ array ls

export %inline
generate : (n : Nat) -> ((m : Nat) -> {auto 0 lt : LT m n} -> a) -> Array a
generate n f = A n $ generate n f

export %inline
iterate : (n : Nat) -> (a -> a) -> a -> Array a
iterate n f x = A n $ iterate n f x
