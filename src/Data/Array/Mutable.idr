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
setAtSuffix :
     (0 tag : _)
  -> {auto _ : MArray tag s (length ys) a}
  -> Suffix (x::xs) ys
  -> a
  -> F1' s
setAtSuffix tag v = setAt tag (suffixToFin v)

parameters (0 tag  : _)
           {auto arr : MArray tag s n a}

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
  setIxAt : (0 m : Nat) -> (x : Ix (S m) n) => a -> F1' s
  setIxAt _ = setAt tag (ixToFin x)

  ||| Set a value at index `m` in a mutable array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  setNatAt : (m : Nat) -> (0 lt : LT m n) => a -> F1' s
  setNatAt x = setAt tag (natToFinLT x)

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
  getIxAt : (0 m : Nat) -> (x : Ix (S m) n) => F1 s a
  getIxAt _ = getAt tag (ixToFin x)

  ||| Read a value at index `m` from a mutable array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this also returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  getNatAt : (m : Nat) -> (0 lt : LT m n) => F1 s a
  getNatAt x = getAt tag (natToFinLT x)

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
  modifyIxAt : (0 m : Nat) -> (x : Ix (S m) n) => (a -> a) -> F1' s
  modifyIxAt _ = modifyAt tag (ixToFin x)

  ||| Modify a value at index `m` in a mutable array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MArray` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  modifyNatAt : (m : Nat) -> (0 lt : LT m n) => (a -> a) -> F1' s
  modifyNatAt m = modifyAt tag (natToFinLT m)

parameters {auto arr : MArray () s n a}

  export %inline
  setIx : (0 m : Nat) -> (x : Ix (S m) n) => a -> F1' s
  setIx = setIxAt ()

  export %inline
  setNat : (m : Nat) -> (0 lt : LT m n) => a -> F1' s
  setNat = setNatAt ()

  export %inline
  getIx : (0 m : Nat) -> (x : Ix (S m) n) => F1 s a
  getIx = getIxAt ()

  export %inline
  getNat : (m : Nat) -> (0 lt : LT m n) => F1 s a
  getNat = getNatAt ()

  export %inline
  modifyIx : (0 m : Nat) -> (x : Ix (S m) n) => (a -> a) -> F1' s
  modifyIx = modifyIxAt ()

  export %inline
  modifyNat : (m : Nat) -> (0 lt : LT m n) => (a -> a) -> F1' s
  modifyNat = modifyNatAt ()

--------------------------------------------------------------------------------
--          Allocating Arrays
--------------------------------------------------------------------------------

||| Writes the data from a list to a mutable array.
|||
||| This uses the `Suffix` proof for safely indexing into the array.
export
writeList :
     (0 tag : _)
  -> {auto arr : MArray tag s (length xs) a}
  -> (ys : List a)
  -> {auto p : Suffix ys xs}
  -> F1' s
writeList tag []        t = t
writeList tag (y :: ys) t = writeList {xs} tag ys (setAtSuffix tag p y t)

||| Writes the data from a vector to a mutable array.
export
writeVect : (0 tag : _) -> MArray tag s n a => Vect k a -> Ix k n => F1' s
writeVect           tag []        x = x
writeVect {k = S m} tag (y :: ys) x = writeVect tag ys (setIxAt tag m y x)

||| Writes the data from a vector to a mutable array in reverse order.
writeVectRev :
     (0 tag : _)
  -> {auto arr : MArray tag s n a}
  -> (m : Nat)
  -> Vect k a
  -> {auto 0 _ : LTE m n}
  -> F1' s
writeVectRev tag (S l) (y :: ys) x = writeVectRev tag l ys (setNatAt tag l y x)
writeVectRev tag _     _         x = x

||| Overwrite the values in a mutable array from the
||| given index downward with the result of the given function.
export
genFrom :
     (0 tag : _)
  -> {auto arr : MArray tag s n a}
  -> (m : Nat)
  -> {auto 0 _ : LTE m n}
  -> (Fin n -> a)
  -> F1' s
genFrom tag 0     f t = t
genFrom tag (S k) f t = genFrom tag k f (setNatAt tag k (f $ natToFinLT k) t)

||| Overwrite the values in a mutable array from the
||| given index upward with the results of applying the given
||| function repeatedly.
export
iterateFrom :
     (0 tag : _)
  -> {auto arr : MArray tag s n a}
  -> (m : Nat)
  -> {auto ix : Ix m n}
  -> (a -> a)
  -> a
  -> F1' s
iterateFrom tag 0     f v t = t
iterateFrom tag (S k) f v t = iterateFrom tag k f (f v) (setIxAt tag k v t)

--------------------------------------------------------------------------------
-- Linear Utilities
--------------------------------------------------------------------------------

parameters (0 tag    : _)
           {k        : Nat}
           {auto arr : MArray tag s k a}

  ||| Accumulate the values stored in a mutable, linear array.
  export
  foldrLin : (a -> b -> b) -> b -> F1 s b
  foldrLin f = go k
    where
      go : (n : Nat) -> (0 lt : LTE n k) => b -> F1 s b
      go 0     v m = v # m
      go (S k) v m = let el # m2 := getNatAt tag k m in go k (f el v) m2


  ||| Store the values in a linear array in a `Vect` of the same size.
  export
  toVect : F1 s (Vect k a)
  toVect = go [] k
    where
      go : Vect m a -> (n : Nat) -> (0 lt : LTE n k) => F1 s (Vect (m+n) a)
      go vs 0     t = rewrite plusCommutative m 0 in vs # t
      go vs (S x) t =
        let v # t := getNatAt tag x t
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
        let v # t := getNatAt tag x t
            vb       := f (natToFinLT x) v
         in rewrite sym (plusSuccRightSucc m x) in go (vb::vs) x t
