module Data.FXArray.Mutable

import public Data.Linear.Token
import public Data.FXArray.Core
import public Data.Array.Index

import Data.List
import Data.Vect

import Syntax.T1

%default total

--------------------------------------------------------------------------------
--          Reading and writing mutable arrays
--------------------------------------------------------------------------------

||| Set a value in a mutable array corresponding to a position in a list
||| used for filling said array.
export %inline
fxsetAtSuffix :
     (r : FXMArray s (length ys))
  -> Suffix (x::xs) ys
  -> Bits32
  -> F1' s
fxsetAtSuffix r v = fxset r (suffixToFin v)

parameters (r : FXMArray s n)

  ||| Set a value at index `n - m` in a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  fxsetIx : (0 m : Nat) -> (x : Ix (S m) n) => Bits32 -> F1' s
  fxsetIx _ = fxset r (ixToFin x)

  ||| Set a value at index `m` in a mutable array.
  export %inline
  fxsetNat : (m : Nat) -> (0 lt : LT m n) => Bits32 -> F1' s
  fxsetNat x = fxset r (natToFinLT x)

  ||| Read a value at index `n - m` from a mutable array.
  |||
  ||| This actually uses the auto implicit argument for accessing the
  ||| the array. It is mainly useful for iterating over an array from the left
  ||| by using a natural number for counting down (see also the documentation
  ||| for `Ix`).
  export %inline
  fxgetIx : (0 m : Nat) -> (x : Ix (S m) n) => F1 s Bits32
  fxgetIx _ = fxget r (ixToFin x)

  ||| Read a value at index `m` from a mutable array.
  export %inline
  fxgetNat : (m : Nat) -> (0 lt : LT m n) => F1 s Bits32
  fxgetNat x = fxget r (natToFinLT x)
