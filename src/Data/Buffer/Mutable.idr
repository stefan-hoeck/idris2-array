module Data.Buffer.Mutable

import public Data.Array.Core
import public Data.Array.Index
import public Data.Buffer.Core
import public Data.Linear
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
     (s : Suffix (x::xs) ys)
  -> Bits8
  -> MBuffer (length ys)
  -@ MBuffer (length ys)
setAtSuffix s = set (suffixToFin s)

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
setIx : (0 m : Nat) -> (x : Ix (S m) n) => Bits8 -> MBuffer n -@ MBuffer n
setIx _ = set (ixToFin x)

||| Set a value at index `m` in a mutable byte array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this returns a new `MBuffer` wrapper, which must then
||| again be used exactly once.
export %inline
setNat : (m : Nat) -> (0 lt : LT m n) => Bits8 -> MBuffer n -@ MBuffer n
setNat x = set (natToFinLT x)

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
getIx : (0 m : Nat) -> (x : Ix (S m) n) => MBuffer n -@ CRes Bits8 (MBuffer n)
getIx _ = get (ixToFin x)

||| Read a value at index `m` from a mutable byte array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this also returns a new `MBuffer` wrapper, which must then
||| again be used exactly once.
export %inline
getNat : (m : Nat) -> (0 lt : LT m n) => MBuffer n -@ CRes Bits8 (MBuffer n)
getNat x = get (natToFinLT x)

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
modifyIx :
     (0 m : Nat)
  -> {auto x : Ix (S m) n}
  -> (Bits8 -> Bits8)
  -> MBuffer n
  -@ MBuffer n
modifyIx _ = modify (ixToFin x)

||| Modify a value at index `m` in a mutable byte array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this returns a new `MBuffer` wrapper, which must then
||| again be used exactly once.
export %inline
modifyNat :
     (m : Nat)
  -> {auto 0 lt : LT m n}
  -> (Bits8 -> Bits8)
  -> MBuffer n
  -@ MBuffer n
modifyNat m = modify (natToFinLT m)

--------------------------------------------------------------------------------
--          Allocating Arrays
--------------------------------------------------------------------------------

||| Writes the data from a list to a mutable byte array.
|||
||| This uses the `Suffix` proof for safely indexing into the array.
export
writeList :
     (ys : List Bits8)
  -> {auto s : Suffix ys xs}
  -> MBuffer (length xs)
  -@ MBuffer (length xs)
writeList []        x = x
writeList (y :: ys) x = writeList ys (setAtSuffix s y x)

||| Allocate an new byte array filled with the values in a non-empty list.
export
allocList : (as : List Bits8) -> (MBuffer (length as) -@ Ur b) -@ Ur b
allocList xs f = alloc (length xs) (f . writeList xs)

||| Writes the data from a vector to a mutable byte array.
export
writeVect : Vect k Bits8 -> Ix k n => MBuffer n -@ MBuffer n
writeVect           []        x = x
writeVect {k = S m} (y :: ys) x = writeVect ys (setIx m y x)

||| Writes the data from a vector to a mutable byte array in reverse order.
writeVectRev :
     (m : Nat)
  -> Vect k Bits8
  -> {auto 0 _ : LTE m n}
  -> MBuffer n
  -@ MBuffer n
writeVectRev (S l) (y :: ys) x = writeVectRev l ys (setNat l y x)
writeVectRev _     _         x = x

||| Allocate an new byte array filled with the values in a non-empty vector.
export
allocVect :
     {n : _}
  -> Vect n Bits8
  -> (MBuffer n -@ Ur b)
  -@ Ur b
allocVect xs f = alloc n (f . writeVect xs)

||| Allocate an new byte array filled with the values in a non-empty vector
||| in reverse order.
export
allocRevVect : {n : _} -> Vect n Bits8 -> (MBuffer n -@ Ur b) -@ Ur b
allocRevVect xs f = alloc n (f . writeVectRev n xs)

||| Overwrite the values in a mutable byte array from the
||| given index downward with the result of the given function.
export
genFrom :
     (m : Nat)
  -> {auto 0 _ : LTE m n}
  -> (Fin n -> Bits8)
  -> MBuffer n
  -@ MBuffer n
genFrom 0     f buf = buf
genFrom (S k) f buf =
  let buf' := setNat k (f $ natToFinLT k) buf in genFrom k f buf'

||| Allocate an new byte array filled with the values from the given
||| generating function.
export
allocGen : (n : Nat) -> (Fin n -> Bits8) -> (MBuffer n -@ Ur b) -@ Ur b
allocGen k f g = alloc k (g . genFrom k f)

||| Overwrite the values in a mutable array from the
||| given index upward with the results of applying the given
||| function repeatedly.
export
iterateFrom :
     (m : Nat)
  -> {auto x : Ix m n}
  -> (Bits8 -> Bits8)
  -> Bits8
  -> MBuffer n
  -@ MBuffer n
iterateFrom 0     f v buf = buf
iterateFrom (S k) f v buf =
  let buf' := setIx k v buf in iterateFrom k f v buf'

||| Allocate an new byte array filled with the values by applying
||| the given function repeatedly to its argument.
export
allocIter : (n : Nat) -> (Bits8 -> Bits8) -> Bits8 -> (MBuffer n -@ Ur b) -@ Ur b
allocIter k f v g = alloc k (g . iterateFrom k f v)
