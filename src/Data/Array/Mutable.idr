module Data.Array.Mutable

import public Data.Linear.Token
import public Data.Array.Core
import public Data.Array.Index
import Data.List
import Data.Vect

%default total

--------------------------------------------------------------------------------
--          Reading and writing mutable arrays
--------------------------------------------------------------------------------

||| Set a value in an array corresponding to a position in a list
||| used for filling said array.
export %inline
setAtSuffix : (s : MArray (length ys) a) => Suffix (x::xs) ys -> a -> F1' s
setAtSuffix v = set (suffixToFin v)

parameters {auto s : MArray n a}

  ||| Set a value at index `n - m` in a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  setIx : (0 m : Nat) -> (x : Ix (S m) n) => a -> F1' s
  setIx _ = set (ixToFin x)

  ||| Set a value at index `m` in a mutable array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  setNat : (m : Nat) -> (0 lt : LT m n) => a -> F1' s
  setNat x = set (natToFinLT x)

  ||| Read a value at index `n - m` from a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this also returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  getIx : (0 m : Nat) -> (x : Ix (S m) n) => F1 s a
  getIx _ = get (ixToFin x)

  ||| Read a value at index `m` from a mutable array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this also returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  getNat : (m : Nat) -> (0 lt : LT m n) => F1 s a
  getNat x = get (natToFinLT x)

  ||| Modify a value at index `n - m` in a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  modifyIx : (0 m : Nat) -> (x : Ix (S m) n) => (a -> a) -> F1' s
  modifyIx _ = modify (ixToFin x)

  ||| Modify a value at index `m` in a mutable array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  modifyNat : (m : Nat) -> (0 lt : LT m n) => (a -> a) -> F1' s
  modifyNat m = modify (natToFinLT m)

--------------------------------------------------------------------------------
--          Allocating Arrays
--------------------------------------------------------------------------------

||| Writes the data from a list to a mutable array.
|||
||| This uses the `Suffix` proof for safely indexing into the array.
export
writeList :
     {auto s : MArray (length xs) a}
  -> (ys : List a)
  -> {auto p : Suffix ys xs}
  -> F1' s
writeList []        x = x
writeList (y :: ys) x = writeList ys (setAtSuffix p y x)

||| Allocate an new array filled with the values in a non-empty list.
export
allocList : (as : List a) -> (0 _ : NonEmpty as) => WithMArray (length as) a b -@ Ur b
allocList (x::xs) f = alloc (S $ length xs) x (f . writeList {xs = x::xs} xs)

||| Writes the data from a vector to a mutable array.
export
writeVect : (s : MArray n a) => Vect k a -> Ix k n => F1' s
writeVect           []        x = x
writeVect {k = S m} (y :: ys) x = writeVect ys (setIx m y x)

||| Writes the data from a vector to a mutable array in reverse order.
writeVectRev : (s : MArray n a) => (m : Nat) -> Vect k a -> (0 _ : LTE m n) => F1' s
writeVectRev (S l) (y :: ys) x = writeVectRev l ys (setNat l y x)
writeVectRev _     _         x = x

||| Allocate an new array filled with the values in a non-empty vector.
export
allocVect : {n : _} -> Vect (S n) a -> WithMArray (S n) a b -@ Ur b
allocVect (x::xs) f = alloc (S n) x (f . writeVect xs)

||| Allocate an new array filled with the values in a non-empty vector
||| in reverse order.
export
allocRevVect : {n : _} -> Vect (S n) a -> WithMArray (S n) a b -@ Ur b
allocRevVect (x::xs) f = alloc (S n) x (f . writeVectRev n xs)

||| Overwrite the values in a mutable array from the
||| given index downward with the result of the given function.
export
genFrom : (s : MArray n a) => (m : Nat) -> (0 _ : LTE m n) => (Fin n -> a) -> F1' s
genFrom 0     f t = t
genFrom (S k) f t =
  let t2 := setNat k (f $ natToFinLT k) t in genFrom k f t2

||| Allocate an new array filled with the values from the given
||| generating function.
export
allocGen : (n : Nat) -> (0 p : IsSucc n) => (Fin n -> a) -> WithMArray n a b -@ Ur b
allocGen (S k) f g = alloc (S k) (f last) (g . genFrom k f)

||| Overwrite the values in a mutable array from the
||| given index upward with the results of applying the given
||| function repeatedly.
export
iterateFrom : (s : MArray n a) => (m : Nat) -> Ix m n => (a -> a) -> a -> F1' s
iterateFrom 0     f v t = t
iterateFrom (S k) f v t =
  let t2 := setIx k v t in iterateFrom k f (f v) t2

||| Allocate an new array filled with the values by applying
||| the given function repeatedly to its argument.
export
allocIter : (n : Nat) -> (0 p : IsSucc n) => (a -> a) -> a -> WithMArray n a b -@ Ur b
allocIter (S k) f v g = alloc (S k) v (g . iterateFrom k f (f v))

--------------------------------------------------------------------------------
-- Linear Utilities
--------------------------------------------------------------------------------

parameters {k      : Nat}
           {auto s : MArray k a}

  ||| Accumulate the values stored in a mutable, linear array.
  export
  foldrLin : (a -> b -> b) -> b -> F1 s b
  foldrLin f = go k
    where
      go : (n : Nat) -> (0 lt : LTE n k) => b -> F1 s b
      go 0     v m = v # m
      go (S k) v m = let el # m2 := getNat k m in go k (f el v) m2


  ||| Store the values in a linear array in a `Vect` of the same size.
  export
  toVect : F1 s (Vect k a)
  toVect = go [] k
    where
      go : Vect m a -> (n : Nat) -> (0 lt : LTE n k) => F1 s (Vect (m+n) a)
      go vs 0     t = rewrite plusCommutative m 0 in vs # t
      go vs (S x) t =
        let v # t := getNat x t
         in rewrite sym (plusSuccRightSucc m x) in go (v::vs) x t

  ||| Extract and convert the values stored in a linear array
  ||| and store them in a `Vect` of the same size.
  export
  toVectWith : (Fin k -> a -> b) -> F1 s (Vect k b)
  toVectWith f = go [] k
    where
      go : Vect m b -> (n : Nat) -> (0 lt : LTE n k) => F1 s (Vect (m+n) b)
      go vs 0     t = rewrite plusCommutative m 0 in vs # t
      go vs (S x) t =
        let v # t := getNat x t
            vb       := f (natToFinLT x) v
         in rewrite sym (plusSuccRightSucc m x) in go (vb::vs) x t
