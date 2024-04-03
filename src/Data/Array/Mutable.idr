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

--------------------------------------------------------------------------------
-- Linear Utilities
--------------------------------------------------------------------------------

||| Filter a list via a linear function.
export
filterLin : (a -> m -@ CRes Bool m) -> List a -> m -@ CRes (List a) m
filterLin f vs = go [<] vs
  where
    go : SnocList a -> List a -> m -@ CRes (List a) m
    go sv [] m = (sv <>> []) # m
    go sv (h::t) m =
      let True # m2 := f h m | _ # m2 => go sv t m2
       in go (sv :< h) t m2

||| Map a list via a linear function.
export
mapLin : (a -> m -@ CRes b m) -> List a -> m -@ CRes (List b) m
mapLin f vs = go [<] vs
  where
    go : SnocList b -> List a -> m -@ CRes (List b) m
    go sv [] m = (sv <>> []) # m
    go sv (h::t) m = let v # m2 := f h m in go (sv :< v) t m2

||| Map and filter a list via a linear function.
export
mapMaybeLin : (a -> m -@ CRes (Maybe b) m) -> List a -> m -@ CRes (List b) m
mapMaybeLin f vs = go [<] vs
  where
    go : SnocList b -> List a -> m -@ CRes (List b) m
    go sv [] m = (sv <>> []) # m
    go sv (h::t) m =
      let Just v # m2 := f h m | _ # m2 => go sv t m2
       in go (sv :< v) t m2

||| Accumulate the values stored in a mutable, linear array.
export
foldrLin : {k : _} -> (e -> a -> a) -> a -> MArray k e -@ CRes a (MArray k e)
foldrLin f = go k
  where
    go : (n : Nat) -> (0 lt : LTE n k) => a -> MArray k e -@ CRes a (MArray k e)
    go 0     v m = v # m
    go (S k) v m = let el # m2 := getNat k m in go k (f el v) m2

||| Store the values in a linear array in a `Vect` of the same size.
export
toVect : {k : _} -> MArray k a -@ CRes (Vect k a) (MArray k a)
toVect = go [] k
  where
    go :
         Vect m a
      -> (n : Nat)
      -> {auto 0 lt : LTE n k}
      -> MArray k a
      -@ CRes (Vect (m+n) a) (MArray k a)
    go vs 0     arr = rewrite plusCommutative m 0 in vs # arr
    go vs (S x) arr =
      let v # arr2 := getNat x arr
       in rewrite sym (plusSuccRightSucc m x) in go (v::vs) x arr2

||| Extract and convert the values stored in a linear array
||| and store them in a `Vect` of the same size.
export
toVectWith :
     {k : _}
  -> (Fin k -> a -> b)
  -> MArray k a
  -@ CRes (Vect k b) (MArray k a)
toVectWith f = go [] k
  where
    go :
         Vect m b
      -> (n : Nat)
      -> {auto 0 lt : LTE n k}
      -> MArray k a
      -@ CRes (Vect (m+n) b) (MArray k a)
    go vs 0     arr = rewrite plusCommutative m 0 in vs # arr
    go vs (S x) arr =
      let v # arr2 := getNat x arr
          vb       := f (natToFinLT x) v
       in rewrite sym (plusSuccRightSucc m x) in go (vb::vs) x arr2
