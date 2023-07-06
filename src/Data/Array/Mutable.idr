module Data.Array.Mutable

import public Data.Array.Core
import public Data.Array.Index
import Data.List
import Data.Vect

%default total

--------------------------------------------------------------------------------
--          Reading and writing mutable arrays
--------------------------------------------------------------------------------

export %inline
setAtSuffix :
     (s : Suffix (x::xs) ys)
  -> a
  -> MArray (length ys) a
  -@ MArray (length ys) a
setAtSuffix s = set (suffixToFin s)

export %inline
setIx : (0 m : Nat) -> {auto x : Ix (S m) n} -> a -> MArray n a -@ MArray n a
setIx _ = set (ixToFin x)

export %inline
setNat : (m : Nat) -> {auto 0 lt : LT m n} -> a -> MArray n a -@ MArray n a
setNat x = set (natToFinLT x)

export %inline
getIx : (0 m : Nat) -> {auto x : Ix (S m) n} -> MArray n a -@ Res a (const $ MArray n a)
getIx _ = get (ixToFin x)

export %inline
getNat : (m : Nat) -> {auto 0 lt : LT m n} -> MArray n a -@ Res a (const $ MArray n a)
getNat x = get (natToFinLT x)

export
modify : Fin n -> (a -> a) -> MArray n a -@ MArray n a
modify m f arr = let v # arr1 := get m arr in set m (f v) arr1

export %inline
modifyIx :
     (0 m : Nat)
  -> {auto x : Ix (S m) n}
  -> (a -> a)
  -> MArray n a
  -@ MArray n a
modifyIx _ = modify (ixToFin x)

export %inline
modifyNat : (m : Nat) -> {auto 0 lt : LT m n} -> (a -> a) -> MArray n a -@ MArray n a
modifyNat m = modify (natToFinLT m)

--------------------------------------------------------------------------------
--          Allocating Arrays
--------------------------------------------------------------------------------

fromL :
     (ys : List a)
  -> {auto s : Suffix ys xs}
  -> (MArray (length xs) a -@ !* b)
  -@ MArray (length xs) a
  -@ !* b
fromL []        f x = f x
fromL (y :: ys) f x = fromL ys f (setAtSuffix s y x)

export
allocList :
     (as : List a)
  -> {auto 0 prf : NonEmpty as}
  -> (MArray (length as) a -@ !* b)
  -@ !* b
allocList (x::xs) f = alloc (S $ length xs) x (fromL {xs = x::xs} xs f)

fromV : Vect k a -> Ix k n => (MArray n a -@ !* b) -@ MArray n a -@ !* b
fromV           []        f x = f x
fromV {k = S m} (y :: ys) f x = fromV ys f (setIx m y x)

fromRevV :
     (m : Nat)
  -> Vect k a
  -> {auto 0 prf : LTE m n}
  -> (MArray n a -@ !* b) -@ MArray n a
  -@ !* b
fromRevV (S l) (y :: ys) f x = fromRevV l ys f (setNat l y x)
fromRevV _     _         f x = f x

export
allocVect : {n : _} -> Vect (S n) a -> (MArray (S n) a -@ !* b) -@ !* b
allocVect (x::xs) f = alloc (S n) x (fromV xs f)

export
allocRevVect : {n : _} -> Vect (S n) a -> (MArray (S n) a -@ !* b) -@ !* b
allocRevVect (x::xs) f = alloc (S n) x (fromRevV n xs f)

gen :
     (m : Nat)
  -> {auto 0 lte : LTE m n}
  -> (Fin n -> a)
  -> (MArray n a -@ !* b)
  -@ MArray n a
  -@ !* b
gen 0     f g arr = g arr
gen (S k) f g arr =
  let arr' := setNat k (f $ natToFinLT k) arr in gen k f g arr'

export
allocGen :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> (Fin n -> a)
  -> (MArray n a -@ !* b)
  -@ !* b
allocGen (S k) f g = alloc (S k) (f last) (gen k f g)

iter :
     (m : Nat)
  -> {auto x : Ix m n}
  -> (a -> a)
  -> a
  -> (MArray n a -@ !* b)
  -@ MArray n a
  -@ !* b
iter 0     f v g arr = g arr
iter (S k) f v g arr = let arr' := setIx k v arr in iter k f (f v) g arr'

export
allocIter :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> (a -> a)
  -> a
  -> (MArray n a -@ !* b)
  -@ !* b
allocIter (S k) f v g = alloc (S k) v (iter k f (f v) g)
