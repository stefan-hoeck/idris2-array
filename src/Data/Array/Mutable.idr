module Data.Array.Mutable

import public Data.Linear.Token
import public Data.Array.Core
import public Data.Array.Index

import Data.List
import Data.Vect

import Syntax.T1

%default total

--------------------------------------------------------------------------------
--          Reading and writing mutable arrays
--------------------------------------------------------------------------------

||| Set a value in an array corresponding to a position in a list
||| used for filling said array.
export %inline
setAtSuffix :
     (r : MArray s (length ys) a)
  -> Suffix (x::xs) ys
  -> a
  -> F1' s
setAtSuffix r v = set r (suffixToFin v)

||| Safely access a value at the given byte position.
export %inline
setBits8 : MArray s 256 a -> Bits8 -> a -> F1' s
setBits8 r x = set r (bits8ToFin x)

||| Safely access a value at the given byte position.
export %inline
getBits8 : MArray s 256 a -> Bits8 -> F1 s a
getBits8 r x = get r (bits8ToFin x)

parameters (r : MArray s n a)

  ||| Set a value at index `n - m` in a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  setIx : (0 m : Nat) -> (x : Ix (S m) n) => a -> F1' s
  setIx _ = set r (ixToFin x)

  ||| Set a value at index `m` in a mutable array.
  export %inline
  setNat : (m : Nat) -> (0 lt : LT m n) => a -> F1' s
  setNat x = set r (natToFinLT x)

  ||| Read a value at index `n - m` from a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  getIx : (0 m : Nat) -> (x : Ix (S m) n) => F1 s a
  getIx _ = get r (ixToFin x)

  ||| Read a value at index `m` from a mutable array.
  export %inline
  getNat : (m : Nat) -> (0 lt : LT m n) => F1 s a
  getNat x = get r (natToFinLT x)

  ||| Modify a value at index `n - m` in a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  modifyIx : (0 m : Nat) -> (x : Ix (S m) n) => (a -> a) -> F1' s
  modifyIx _ = modify r (ixToFin x)

  ||| Modify a value at index `m` in a mutable array.
  export %inline
  modifyNat : (m : Nat) -> (0 lt : LT m n) => (a -> a) -> F1' s
  modifyNat m = modify r (natToFinLT m)

--------------------------------------------------------------------------------
--          Filling Arrays
--------------------------------------------------------------------------------

||| Writes the data from a list to a mutable array.
|||
||| This uses the `Suffix` proof for safely indexing into the array.
export
writeList :
     (r  : MArray s (length xs) a)
  -> (ys : List a)
  -> {auto p : Suffix ys xs}
  -> F1' s
writeList r []        = pure ()
writeList r (y :: ys) = T1.do
  setAtSuffix r p y
  writeList {xs} r ys

||| Writes the data from a list to a mutable array.
|||
||| This uses the `Suffix` proof for safely indexing into the array.
export
writeListWith :
     (r  : MArray s (length xs) b)
  -> (ys : List a)
  -> (f : a -> b)
  -> {auto p : Suffix ys xs}
  -> F1' s
writeListWith r []        f = pure ()
writeListWith r (y :: ys) f = T1.do
  setAtSuffix r p (f y)
  writeListWith {xs} r ys f

parameters (r : MArray s n a)

  ||| Writes the data from a vector to a mutable array.
  export
  writeVect : Vect k a -> Ix k n => F1' s
  writeVect           []        = pure ()
  writeVect {k = S m} (y :: ys) = T1.do
    setIx r m y
    writeVect ys

  ||| Writes the data from a vector to a mutable array in reverse order.
  export
  writeVectRev : (m : Nat) -> Vect k a -> (0 _ : LTE m n) => F1' s
  writeVectRev (S l) (y :: ys) = T1.do
    setNat r l y
    writeVectRev l ys
  writeVectRev _     _         = pure ()

  ||| Overwrite the values in a mutable array from the
  ||| given index downward with the result of the given function.
  export
  genFrom : (m : Nat) -> (0 _ : LTE m n) => (Fin n -> a) -> F1' s
  genFrom 0     f = pure ()
  genFrom (S k) f = T1.do
    setNat r k (f $ natToFinLT k)
    genFrom k f

  ||| Overwrite the values in a mutable array from the
  ||| given index upward with the results of applying the given
  ||| function repeatedly.
  export
  iterateFrom : (m : Nat) -> (ix : Ix m n) => (a -> a) -> a -> F1' s
  iterateFrom 0     f v = pure ()
  iterateFrom (S k) f v = T1.do
    setIx r k v
    iterateFrom k f (f v)

export
allocList : (xs : List a) -> WithMArray (length xs) a b -> b
allocList xs g =
  unsafeAlloc (length xs) $ \r => T1.do
    writeList {xs} r xs
    g r

export
allocListWith : (xs : List a) -> (a -> b) -> WithMArray (length xs) b c -> c
allocListWith xs f g =
  unsafeAlloc (length xs) $ \r => T1.do
    writeListWith {xs} r xs f
    g r

export
allocVect : {n : _} -> Vect n a -> WithMArray n a b -> b
allocVect xs g =
  unsafeAlloc n $ \r => T1.do
    writeVect r xs
    g r

export
allocVectRev : {n : _} -> Vect n a -> WithMArray n a b -> b
allocVectRev xs g =
  unsafeAlloc n $ \r => T1.do
    writeVectRev r n xs
    g r

export
allocGen : (n : Nat) -> (Fin n -> a) -> WithMArray n a b -> b
allocGen n f g =
  unsafeAlloc n $ \r => T1.do
    genFrom r n f
    g r

export
allocIter : (n : Nat) -> (a -> a) -> a -> WithMArray n a b -> b
allocIter n f v g =
  unsafeAlloc n $ \r => T1.do
    iterateFrom r n f v
    g r

--------------------------------------------------------------------------------
--          Growing Arrays
--------------------------------------------------------------------------------

parameters {n : Nat}
           (r : MArray s n a)

  ||| Allocates a new mutable array and adds the elements from `r`
  ||| at its beginning.
  export
  mgrow : (m : Nat) -> (deflt : a) -> F1 s (MArray s (m+n) a)
  mgrow m deflt t =
    let tgt # t := marray1 (m+n) deflt t
        _   # t := copy r 0 0 n @{reflexive} @{lteAddLeft n} tgt t
     in tgt # t

--------------------------------------------------------------------------------
--          Appending Arrays
--------------------------------------------------------------------------------

parameters {m, n : Nat}
           (p : MArray s m a)
           (q : MArray s n a)

  ||| Allocates a new mutable array and adds the elements from `p`
  ||| at its beginning, followed by adding the elements from `q`.
  export
  mappend : F1 s (MArray s (m+n) a)
  mappend t =
    let tgt # t := unsafeMArray1 (m+n) t
        _   # t := copy p 0 0 m @{reflexive} @{lteAddRight m} tgt t
        _   # t := copy q 0 m n @{reflexive} tgt t
      in tgt # t

--------------------------------------------------------------------------------
--          Subarrays
--------------------------------------------------------------------------------

parameters {m, n : Nat}
           (f : a -> Bool)
           (p : MArray s n a)

  ||| Filters the values in a mutable array according to the given predicate.
  export
  mfilter : F1 s (m ** MArray s m a)
  mfilter t =
    let tft         # t := unsafeMArray1 n t
        (m ** tft') # t := go 0 n p tft t
        tft''       # t := mtake tft' m t
      in (m ** tft'') # t
    where
      go :  (m, x : Nat)
         -> (p : MArray s n a)
         -> (q : MArray s n a)
         -> F1 s (m : Nat ** MArray s n a)
      go m 0     p q t =
        (m ** q) # t
      go m (S j) p q t =
        case tryNatToFin j of
          Nothing =>
            go m j p q t
          Just j' =>
            let j'' # t := get p j' t
              in case f j'' of
                   True  =>
                     case tryNatToFin m of
                       Nothing =>
                         go m j p q t
                       Just m' =>
                         let () # t := set q m' j'' t
                           in go (S m) j p q t
                   False =>
                     go m j p q t

--------------------------------------------------------------------------------
--          Linear Utilities
--------------------------------------------------------------------------------

parameters {k : Nat}
           (r : MArray s k a)

  ||| Accumulate the values stored in a mutable array.
  export
  foldrLin : (a -> b -> b) -> b -> F1 s b
  foldrLin f = go k
    where
      go : (n : Nat) -> (0 lt : LTE n k) => b -> F1 s b
      go 0     v = pure v
      go (S k) v = T1.do
        el <- getNat r k
        go k (f el v)

  ||| Store the values in a mutable array in a `Vect` of the same size.
  export
  toVect : F1 s (Vect k a)
  toVect = go [] k
    where
      go : Vect m a -> (n : Nat) -> (0 lt : LTE n k) => F1 s (Vect (m+n) a)
      go vs 0     t = rewrite plusCommutative m 0 in vs # t
      go vs (S x) t =
        let v # t := getNat r x t
         in rewrite sym (plusSuccRightSucc m x) in go (v::vs) x t

  ||| Extract and convert the values stored in a mutable array
  ||| and store them in a `Vect` of the same size.
  export
  toVectWith : (Fin k -> a -> b) -> F1 s (Vect k b)
  toVectWith f = go [] k
    where
      go : Vect m b -> (n : Nat) -> (0 lt : LTE n k) => F1 s (Vect (m+n) b)
      go vs 0     t = rewrite plusCommutative m 0 in vs # t
      go vs (S x) t =
        let v # t := getNat r x t
            vb       := f (natToFinLT x) v
         in rewrite sym (plusSuccRightSucc m x) in go (vb::vs) x t
