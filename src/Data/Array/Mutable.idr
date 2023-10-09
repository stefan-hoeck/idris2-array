module Data.Array.Mutable

import public Data.Linear
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
     (s : Suffix (x::xs) ys)
  -> a
  -> MArray (length ys) a
  -@ MArray (length ys) a
setAtSuffix s = set (suffixToFin s)

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
setIx : (0 m : Nat) -> (x : Ix (S m) n) => a -> MArray n a -@ MArray n a
setIx _ = set (ixToFin x)

||| Set a value at index `m` in a mutable array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this returns a new `MArray` wrapper, which must then
||| again be used exactly once.
export %inline
setNat : (m : Nat) -> (0 lt : LT m n) => a -> MArray n a -@ MArray n a
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
getIx : (0 m : Nat) -> (x : Ix (S m) n) => MArray n a -@ CRes a (MArray n a)
getIx _ = get (ixToFin x)

||| Read a value at index `m` from a mutable array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this also returns a new `MArray` wrapper, which must then
||| again be used exactly once.
export %inline
getNat : (m : Nat) -> (0 lt : LT m n) => MArray n a -@ CRes a (MArray n a)
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
modifyIx :
     (0 m : Nat)
  -> {auto x : Ix (S m) n}
  -> (a -> a)
  -> MArray n a
  -@ MArray n a
modifyIx _ = modify (ixToFin x)

||| Modify a value at index `m` in a mutable array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this returns a new `MArray` wrapper, which must then
||| again be used exactly once.
export %inline
modifyNat : (m : Nat) -> (0 lt : LT m n) => (a -> a) -> MArray n a -@ MArray n a
modifyNat m = modify (natToFinLT m)

--------------------------------------------------------------------------------
--          Allocating Arrays
--------------------------------------------------------------------------------

||| Writes the data from a list to a mutable array.
|||
||| This uses the `Suffix` proof for safely indexing into the array.
export
writeList :
     (ys : List a)
  -> {auto s : Suffix ys xs}
  -> MArray (length xs) a
  -@ MArray (length xs) a
writeList []        x = x
writeList (y :: ys) x = writeList ys (setAtSuffix s y x)

||| Allocate an new array filled with the values in a non-empty list.
export
allocList :
     (as : List a)
  -> {auto 0 prf : NonEmpty as}
  -> (MArray (length as) a -@ Ur b)
  -@ Ur b
allocList (x::xs) f = alloc (S $ length xs) x (f . writeList {xs = x::xs} xs)

||| Writes the data from a vector to a mutable array.
export
writeVect : Vect k a -> Ix k n => MArray n a -@ MArray n a
writeVect           []        x = x
writeVect {k = S m} (y :: ys) x = writeVect ys (setIx m y x)

||| Writes the data from a vector to a mutable array in reverse order.
writeVectRev : (m : Nat) -> Vect k a -> (0 _ : LTE m n) => MArray n a -@ MArray n a
writeVectRev (S l) (y :: ys) x = writeVectRev l ys (setNat l y x)
writeVectRev _     _         x = x

||| Allocate an new array filled with the values in a non-empty vector.
export
allocVect : {n : _} -> Vect (S n) a -> (MArray (S n) a -@ Ur b) -@ Ur b
allocVect (x::xs) f = alloc (S n) x (f . writeVect xs)

||| Allocate an new array filled with the values in a non-empty vector
||| in reverse order.
export
allocRevVect : {n : _} -> Vect (S n) a -> (MArray (S n) a -@ Ur b) -@ Ur b
allocRevVect (x::xs) f = alloc (S n) x (f . writeVectRev n xs)

||| Overwrite the values in a mutable array from the
||| given index downward with the result of the given function.
export
genFrom : (m : Nat) -> (0 _ : LTE m n) => (Fin n -> a) -> MArray n a -@ MArray n a
genFrom 0     f arr = arr
genFrom (S k) f arr =
  let arr' := setNat k (f $ natToFinLT k) arr in genFrom k f arr'

||| Allocate an new array filled with the values from the given
||| generating function.
export
allocGen :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> (Fin n -> a)
  -> (MArray n a -@ Ur b)
  -@ Ur b
allocGen (S k) f g = alloc (S k) (f last) (g . genFrom k f)

||| Overwrite the values in a mutable array from the
||| given index upward with the results of applying the given
||| function repeatedly.
export
iterateFrom :
     (m : Nat)
  -> {auto x : Ix m n}
  -> (a -> a)
  -> a
  -> MArray n a
  -@ MArray n a
iterateFrom 0     f v arr = arr
iterateFrom (S k) f v arr =
  let arr' := setIx k v arr in iterateFrom k f (f v) arr'

||| Allocate an new array filled with the values by applying
||| the given function repeatedly to its argument.
export
allocIter :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> (a -> a)
  -> a
  -> (MArray n a -@ Ur b)
  -@ Ur b
allocIter (S k) f v g = alloc (S k) v (g . iterateFrom k f (f v))
