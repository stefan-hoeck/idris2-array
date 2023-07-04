module Data.Array.Core

import public Data.Linear
import public Data.Fin
import public Data.Nat

%default total

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

export
data ArrayData : Type -> Type where [external]

%extern prim__newArray : forall a . Bits32 -> a -> %World -> (ArrayData a)
%extern prim__arrayGet : forall a . ArrayData a -> Bits32 -> %World -> a
%extern prim__arraySet : forall a . ArrayData a -> Bits32 -> a -> PrimIO ()

destroy : (1 _ : %World) -> a -> a
destroy %MkWorld x = x

set' : (m : Nat) -> a -> ArrayData a -> ArrayData a
set' m y z =
  let MkIORes () w2 := prim__arraySet z (cast m) y %MkWorld
   in destroy w2 z

--------------------------------------------------------------------------------
--          Immutable Arrays
--------------------------------------------------------------------------------

export
record IArray (n : Nat) (a : Type) where
  constructor IA
  arr : ArrayData a

export
at : IArray n a -> Fin n -> a
at (IA ad) m = prim__arrayGet ad (cast $ finToNat m) %MkWorld

export
take : (0 m : Nat) -> IArray n a -> {auto 0 lte : LTE m n} -> IArray m a
take _ (IA arr) = IA arr

--------------------------------------------------------------------------------
--          Mutable Arrays
--------------------------------------------------------------------------------

export
record MArray (n : Nat) (a : Type) where
  constructor MA
  arr : ArrayData a

export
alloc : (n : Nat) -> a -> (MArray n a -@ !* b) -@ !* b
alloc n v f = f (MA $ prim__newArray (cast n) v %MkWorld)

export
unsafeAlloc : (n : Nat) -> (MArray n a -@ !* b) -@ !* b
unsafeAlloc n f = alloc n (believe_me ()) f

export
set : Fin n -> a -> MArray n a -@ MArray n a
set m x (MA arr) = MA $ set' (finToNat m) x arr

export
get : Fin n -> MArray n a -@ Res a (const $ MArray n a)
get m (MA arr) = prim__arrayGet arr (cast $ finToNat m) %MkWorld # MA arr

export
mod : Fin n -> (a -> a) -> MArray n a -@ MArray n a
mod m f arr = let v # arr2 := get m arr in set m (f v) arr2

export
freezeLTE : (0 m : Nat) -> {auto 0 lte : LTE m n} -> MArray n a -@ !* IArray m a
freezeLTE _ (MA arr) = MkBang $ IA arr

export %inline
freeze : MArray n a -@ !* IArray n a
freeze = freezeLTE n @{reflexive}
