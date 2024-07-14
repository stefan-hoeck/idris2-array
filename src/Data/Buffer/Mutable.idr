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
setAtSuffix :
     (0 tag : _)
  -> {auto _ : MBuffer tag s (length ys)}
  -> Suffix (x::xs) ys
  -> Bits8
  -> F1' s
setAtSuffix tag v = setAt tag (suffixToFin v)

parameters (0 tag : _)
           {auto buf : MBuffer tag s n}

  ||| Set a value at index `n - m` in a mutable byte array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MBuffer` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  setIxAt : (0 m : Nat) -> (x : Ix (S m) n) => Bits8 -> F1' s
  setIxAt _ = setAt tag (ixToFin x)

  ||| Set a value at index `m` in a mutable byte array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MBuffer` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  setNatAt : (m : Nat) -> (0 lt : LT m n) => Bits8 -> F1' s
  setNatAt x = setAt tag (natToFinLT x)

  ||| Read a value at index `n - m` from a mutable byte array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this also returns a new `MBuffer` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  getIxAt : (0 m : Nat) -> (x : Ix (S m) n) => F1 s Bits8
  getIxAt _ = getAt tag (ixToFin x)

  ||| Read a value at index `m` from a mutable byte array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this also returns a new `MBuffer` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  getNatAt : (m : Nat) -> (0 lt : LT m n) => F1 s Bits8
  getNatAt x = getAt tag (natToFinLT x)

  ||| Modify a value at index `n - m` in a mutable byte array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MBuffer` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  modifyIxAt : (0 m : Nat) -> (x : Ix (S m) n) => (Bits8 -> Bits8) -> F1' s
  modifyIxAt _ = modifyAt tag (ixToFin x)

  ||| Modify a value at index `m` in a mutable byte array.
  |||
  ||| Since mutable arrays must be used in a linear context, and this
  ||| function "uses up" its input as far as the linearity checker is
  ||| concerned, this returns a new `MBuffer` wrapper, which must then
  ||| again be used exactly once.
  export %inline
  modifyNatAt : (m : Nat) -> (0 lt : LT m n) => (Bits8 -> Bits8) -> F1' s
  modifyNatAt m = modifyAt tag (natToFinLT m)

parameters {auto arr : MBuffer () s n}

  export %inline
  setIx : (0 m : Nat) -> (x : Ix (S m) n) => Bits8 -> F1' s
  setIx = setIxAt ()

  export %inline
  setNat : (m : Nat) -> (0 lt : LT m n) => Bits8 -> F1' s
  setNat = setNatAt ()

  export %inline
  getIx : (0 m : Nat) -> (x : Ix (S m) n) => F1 s Bits8
  getIx = getIxAt ()

  export %inline
  getNat : (m : Nat) -> (0 lt : LT m n) => F1 s Bits8
  getNat = getNatAt ()

  export %inline
  modifyIx : (0 m : Nat) -> (x : Ix (S m) n) => (Bits8 -> Bits8) -> F1' s
  modifyIx = modifyIxAt ()

  export %inline
  modifyNat : (m : Nat) -> (0 lt : LT m n) => (Bits8 -> Bits8) -> F1' s
  modifyNat = modifyNatAt ()

--------------------------------------------------------------------------------
--          Allocating Buffers
--------------------------------------------------------------------------------

||| Writes the data from a list to a mutable byte vector.
export
writeList :
     (0 tag : _)
  -> {auto arr : MBuffer tag s (length xs)}
  -> (ys : List Bits8)
  -> {auto p : Suffix ys xs}
  -> F1' s
writeList tag []        t = t
writeList tag (y :: ys) t = writeList {xs} tag ys (setAtSuffix tag p y t)

||| Writes the data from a vector to a mutable array.
export
writeVect : (0 tag : _) -> MBuffer tag s n => Vect k Bits8 -> Ix k n => F1' s
writeVect           tag []        x = x
writeVect {k = S m} tag (y :: ys) x = writeVect tag ys (setIxAt tag m y x)

||| Writes the data from a vector to a mutable array in reverse order.
export
writeVectRev :
     (0 tag : _)
  -> {auto arr : MBuffer tag s n}
  -> (m : Nat)
  -> Vect k Bits8
  -> {auto 0 _ : LTE m n}
  -> F1' s
writeVectRev tag (S l) (y :: ys) x = writeVectRev tag l ys (setNatAt tag l y x)
writeVectRev tag _     _         x = x

||| Overwrite the values in a mutable array from the
||| given index downward with the result of the given function.
export
genFrom :
     (0 tag : _)
  -> {auto arr : MBuffer tag s n}
  -> (m : Nat)
  -> {auto 0 _ : LTE m n}
  -> (Fin n -> Bits8)
  -> F1' s
genFrom tag 0     f t = t
genFrom tag (S k) f t = genFrom tag k f (setNatAt tag k (f $ natToFinLT k) t)

||| Overwrite the values in a mutable array from the
||| given index upward with the results of applying the given
||| function repeatedly.
export
iterateFrom :
     (0 tag : _)
  -> {auto arr : MBuffer tag s n}
  -> (m : Nat)
  -> {auto ix : Ix m n}
  -> (Bits8 -> Bits8)
  -> Bits8
  -> F1' s
iterateFrom tag 0     f v t = t
iterateFrom tag (S k) f v t = iterateFrom tag k f (f v) (setIxAt tag k v t)
