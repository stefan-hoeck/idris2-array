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
     (r : MArray' t (length ys) a)
  -> {auto 0 p : Res r rs}
  -> Suffix (x::xs) ys
  -> a
  -> F1' rs
setAtSuffix r v = set r (suffixToFin v)

parameters {0 rs : Resources}
           (r : MArray' t n a)
           {auto 0 p : Res r rs}

  ||| Set a value at index `n - m` in a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  setIx : (0 m : Nat) -> (x : Ix (S m) n) => a -> F1' rs
  setIx _ = set r (ixToFin x)

  ||| Set a value at index `m` in a mutable array.
  export %inline
  setNat : (m : Nat) -> (0 lt : LT m n) => a -> F1' rs
  setNat x = set r (natToFinLT x)

  ||| Read a value at index `n - m` from a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  getIx : (0 m : Nat) -> (x : Ix (S m) n) => F1 rs a
  getIx _ = get r (ixToFin x)

  ||| Read a value at index `m` from a mutable array.
  export %inline
  getNat : (m : Nat) -> (0 lt : LT m n) => F1 rs a
  getNat x = get r (natToFinLT x)

  ||| Modify a value at index `n - m` in a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  modifyIx : (0 m : Nat) -> (x : Ix (S m) n) => (a -> a) -> F1' rs
  modifyIx _ = modify r (ixToFin x)

  ||| Modify a value at index `m` in a mutable array.
  export %inline
  modifyNat : (m : Nat) -> (0 lt : LT m n) => (a -> a) -> F1' rs
  modifyNat m = modify r (natToFinLT m)

--------------------------------------------------------------------------------
--          Filling Arrays
--------------------------------------------------------------------------------

||| Writes the data from a list to a mutable array.
|||
||| This uses the `Suffix` proof for safely indexing into the array.
export
writeList :
     (r  : MArray' t (length xs) a)
  -> {auto 0 _ : Res r rs}
  -> (ys : List a)
  -> {auto p : Suffix ys xs}
  -> F1' rs
writeList r []        = pure ()
writeList r (y :: ys) = T1.do
  setAtSuffix r p y
  writeList {xs} r ys

||| Writes the data from a list to a mutable array.
|||
||| This uses the `Suffix` proof for safely indexing into the array.
export
writeListWith :
     (r  : MArray' t (length xs) b)
  -> {auto 0 _ : Res r rs}
  -> (ys : List a)
  -> (f : a -> b)
  -> {auto p : Suffix ys xs}
  -> F1' rs
writeListWith r []        f = pure ()
writeListWith r (y :: ys) f = T1.do
  setAtSuffix r p (f y)
  writeListWith {xs} r ys f

parameters {0 rs : Resources}
           (r : MArray' t n a)
           {auto 0 p : Res r rs}

  ||| Writes the data from a vector to a mutable array.
  export
  writeVect : Vect k a -> Ix k n => F1' rs
  writeVect           []        = pure ()
  writeVect {k = S m} (y :: ys) = T1.do
    setIx r m y
    writeVect ys

  ||| Writes the data from a vector to a mutable array in reverse order.
  export
  writeVectRev : (m : Nat) -> Vect k a -> (0 _ : LTE m n) => F1' rs
  writeVectRev (S l) (y :: ys) = T1.do
    setNat r l y
    writeVectRev l ys
  writeVectRev _     _         = pure ()

  ||| Overwrite the values in a mutable array from the
  ||| given index downward with the result of the given function.
  export
  genFrom : (m : Nat) -> (0 _ : LTE m n) => (Fin n -> a) -> F1' rs
  genFrom 0     f = pure ()
  genFrom (S k) f = T1.do
    setNat r k (f $ natToFinLT k)
    genFrom k f

  ||| Overwrite the values in a mutable array from the
  ||| given index upward with the results of applying the given
  ||| function repeatedly.
  export
  iterateFrom : (m : Nat) -> (ix : Ix m n) => (a -> a) -> a -> F1' rs
  iterateFrom 0     f v = pure ()
  iterateFrom (S k) f v = T1.do
    setIx r k v
    iterateFrom k f (f v)

export
allocList : (xs : List a) -> FromMArray (length xs) a b -> b
allocList xs g =
  unsafeCreate (length xs) $ \r => T1.do
    writeList {xs} r xs
    g r

export
allocListWith : (xs : List a) -> (a -> b) -> FromMArray (length xs) b c -> c
allocListWith xs f g =
  unsafeCreate (length xs) $ \r => T1.do
    writeListWith {xs} r xs f
    g r

export
allocVect : {n : _} -> Vect n a -> FromMArray n a b -> b
allocVect xs g =
  unsafeCreate n $ \r => T1.do
    writeVect r xs
    g r

export
allocVectRev : {n : _} -> Vect n a -> FromMArray n a b -> b
allocVectRev xs g =
  unsafeCreate n $ \r => T1.do
    writeVectRev r n xs
    g r

export
allocGen : (n : Nat) -> (Fin n -> a) -> FromMArray n a b -> b
allocGen n f g =
  unsafeCreate n $ \r => T1.do
    genFrom r n f
    g r

export
allocIter : (n : Nat) -> (a -> a) -> a -> FromMArray n a b -> b
allocIter n f v g =
  unsafeCreate n $ \r => T1.do
    iterateFrom r n f v
    g r

--------------------------------------------------------------------------------
--          Growing Arrays
--------------------------------------------------------------------------------

parameters {0 rs : Resources}
           {n : Nat}
           (r : MArray n a)
           {auto 0 p : Res r rs}

  writeMArray :  (k : Nat)
              -> {auto 0 lte : LTE k n}
              -> (tgt : MArray (m+n) a)
              -> F1' (tgt::rs)
  writeMArray 0     tgt t = () # t
  writeMArray (S k) tgt t =
    let v # t := getNat r k t
        _ # t := setNat tgt k {lt = ltAddLeft lte} v t
     in writeMArray k tgt t

  ||| Allocates a new mutable array and adds the elements from `r`
  ||| at its beginning.
  export
  mgrow :  (m : Nat)
        -> (deflt : a)
        -> (1 t : T1 rs)
        -> A1 rs (MArray (m+n) a)
  mgrow m deflt t =
    let tgt # t := newMArray (m+n) deflt t
        _   # t := writeMArray n tgt t
     in tgt # t

||| Utility for growing and replacing a single mutable array.
export
mgrow1 :
     {n : Nat}
  -> (r : MArray n a)
  -> (m : Nat)
  -> (deflt : a)
  -> (1 t : T1 [r])
  -> A1 [] (MArray (m+n) a)
mgrow1 r m dflt t =
  let tgt # t := mgrow r m dflt t
      _   # t := release r t
   in tgt # t

--------------------------------------------------------------------------------
--          Linear Utilities
--------------------------------------------------------------------------------

parameters {0 rs : Resources}
           {k    : Nat}
           (r    : MArray' t k a)
           {auto 0 p : Res r rs}

  ||| Accumulate the values stored in a mutable, linear array.
  export
  foldrLin : (a -> b -> b) -> b -> F1 rs b
  foldrLin f = go k
    where
      go : (n : Nat) -> (0 lt : LTE n k) => b -> F1 rs b
      go 0     v = pure v
      go (S k) v = T1.do
        el <- getNat r k
        go k (f el v)

  ||| Store the values in a linear array in a `Vect` of the same size.
  export
  toVect : F1 rs (Vect k a)
  toVect = go [] k
    where
      go : Vect m a -> (n : Nat) -> (0 lt : LTE n k) => F1 rs (Vect (m+n) a)
      go vs 0     t = rewrite plusCommutative m 0 in vs # t
      go vs (S x) t =
        let v # t := getNat r x t
         in rewrite sym (plusSuccRightSucc m x) in go (v::vs) x t

  ||| Extract and convert the values stored in a linear array
  ||| and store them in a `Vect` of the same size.
  export
  toVectWith : (Fin k -> a -> b) -> F1 rs (Vect k b)
  toVectWith f = go [] k
    where
      go : Vect m b -> (n : Nat) -> (0 lt : LTE n k) => F1 rs (Vect (m+n) b)
      go vs 0     t = rewrite plusCommutative m 0 in vs # t
      go vs (S x) t =
        let v # t := getNat r x t
            vb       := f (natToFinLT x) v
         in rewrite sym (plusSuccRightSucc m x) in go (vb::vs) x t
