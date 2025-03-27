module Data.Buffer.Mutable

import public Data.Array.Index
import public Data.Buffer.Core
import public Data.Linear.Token
import Data.List
import Data.Vect

%default total

--------------------------------------------------------------------------------
--          Reading and writing mutable byte arrays
--------------------------------------------------------------------------------

||| Set a value in a byte array corresponding to a position in a list
||| used for filling said array.
export %inline
setAtSuffix : MBuffer s (length ys) -> Suffix (x::xs) ys -> Bits8 -> F1' s
setAtSuffix r v = set r (suffixToFin v)

parameters (r : MBuffer s n)

  ||| Set a value at index `n - m` in a mutable byte array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  setIx : (0 m : Nat) -> (x : Ix (S m) n) => Bits8 -> F1' s
  setIx _ = set r (ixToFin x)

  ||| Set a value at index `m` in a mutable byte array.
  export %inline
  setNat : (m : Nat) -> (0 lt : LT m n) => Bits8 -> F1' s
  setNat x = set r (natToFinLT x)

  ||| Read a value at index `n - m` from a mutable byte array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  getIx : (0 m : Nat) -> (x : Ix (S m) n) => F1 s Bits8
  getIx _ = get r (ixToFin x)

  ||| Read a value at index `m` from a mutable byte array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this also returns a new `MBuffer` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  getNat : (m : Nat) -> (0 lt : LT m n) => F1 s Bits8
  getNat x = get r (natToFinLT x)

  ||| Modify a value at index `n - m` in a mutable byte array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  modifyIx : (0 m : Nat) -> (x : Ix (S m) n) => (Bits8 -> Bits8) -> F1' s
  modifyIx _ = modify r (ixToFin x)

  ||| Modify a value at index `m` in a mutable byte array.
  export %inline
  modifyNat : (m : Nat) -> (0 lt : LT m n) => (Bits8 -> Bits8) -> F1' s
  modifyNat m = modify r (natToFinLT m)

--------------------------------------------------------------------------------
--          Allocating Buffers
--------------------------------------------------------------------------------

||| Writes the data from a list to a mutable byte vector.
export
writeList :
     MBuffer s (length xs)
  -> (ys : List Bits8)
  -> {auto p : Suffix ys xs}
  -> F1' s
writeList r []        t = () # t
writeList r (y :: ys) t =
  let _ # t := setAtSuffix r p y t
   in writeList {xs} r ys t

parameters (r : MBuffer s n)

  ||| Writes the data from a vector to a mutable array.
  export
  writeVect : Vect k Bits8 -> Ix k n => F1' s
  writeVect           []        t = () # t
  writeVect {k = S m} (y :: ys) t =
    let _ # t := setIx r m y t
     in writeVect ys t

  ||| Writes the data from a vector to a mutable array in reverse order.
  export
  writeVectRev : (m : Nat) -> Vect k Bits8 -> (0 _ : LTE m n) => F1' s
  writeVectRev (S l) (y :: ys) t =
    let _ # t := setNat r l y t
     in writeVectRev l ys t
  writeVectRev _     _         t = () # t

  ||| Overwrite the values in a mutable array from the
  ||| given index downward with the result of the given function.
  export
  genFrom : (m : Nat) -> (0 _ : LTE m n) => (Fin n -> Bits8) -> F1' s
  genFrom 0     f t = () # t
  genFrom (S k) f t =
    let _ # t := setNat r k (f $ natToFinLT k) t
     in genFrom k f t

  ||| Overwrite the values in a mutable array from the
  ||| given index upward with the results of applying the given
  ||| function repeatedly.
  export
  iterateFrom : (m : Nat) -> (ix : Ix m n) => (Bits8 -> Bits8) -> Bits8 -> F1' s
  iterateFrom 0     f v t = () # t
  iterateFrom (S k) f v t =
    let _ # t := setIx r k v t
     in iterateFrom k f (f v) t

--------------------------------------------------------------------------------
--          Growing Arrays
--------------------------------------------------------------------------------

parameters {n : Nat}
           (r : MBuffer s n)
  ||| Allocates a new mutable buffer and adds the elements from `r`
  ||| at its beginning.
  export
  mgrow : (m : Nat) -> F1 s (MBuffer s (m+n))
  mgrow m t =
    let tgt # t := mbuffer1 (m+n) t
        _   # t := copy r 0 0 n @{reflexive} @{lteAddLeft n} tgt t
     in tgt # t
