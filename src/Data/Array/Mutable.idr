module Data.Array.Mutable

import public Data.Array.Core
import public Data.Array.Index
import Data.List

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
setAtSuffix s = set (suffixToNat s) @{suffixLT s}

export %inline
setIx : (0 m : Nat) -> {auto x : Ix (S m) n} -> a -> MArray n a -@ MArray n a
setIx _ = set (ixToNat x) @{ixLT x}

export %inline
setFin : Fin n -> a -> MArray n a -@ MArray n a
setFin x = set (finToNat x) @{finLT x}

export %inline
getIx : (0 m : Nat) -> {auto x : Ix (S m) n} -> MArray n a -@ P1 a (MArray n a)
getIx _ = get (ixToNat x) @{ixLT x}

export %inline
getFin : Fin n -> MArray n a -@ P1 a (MArray n a)
getFin x = get (finToNat x) @{finLT x}

export
modify : (m : Nat) -> {auto 0 p : LT m n} -> (a -> a) -> MArray n a -@ MArray n a
modify m f arr = let v # arr1 := get m arr in set m (f v) arr1

export %inline
modifyIx :
     (0 m : Nat)
  -> {auto x : Ix (S m) n}
  -> (a -> a)
  -> MArray n a
  -@ MArray n a
modifyIx _ = modify (ixToNat x) @{ixLT x}

export %inline
modifyFin : Fin n -> (a -> a) -> MArray n a -@ MArray n a
modifyFin x = modify (finToNat x) @{finLT x}

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

gen :
     (m : Nat)
  -> {auto 0 lte : LTE m n}
  -> ((k : Nat) -> {auto 0 lt : LT k n} -> a)
  -> (MArray n a -@ !* b)
  -@ MArray n a
  -@ !* b
gen 0     f g arr = g arr
gen (S k) f g arr = let arr' := set k (f k) arr in gen k f g arr'

export
allocGen :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> ((k : Nat) -> {auto 0 lt : LT k n} -> a)
  -> (MArray n a -@ !* b)
  -@ !* b
allocGen (S k) f g = alloc (S k) (f k) (gen k f g)

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
