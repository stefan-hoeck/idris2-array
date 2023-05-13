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
set : Fin n -> a -> MArray n a -@ MArray n a
set m x (MA arr) = MA $ set' (finToNat m) x arr

export
get : Fin n -> MArray n a -@ Res a (const $ MArray n a)
get m (MA arr) = prim__arrayGet arr (cast $ finToNat m) %MkWorld # MA arr

export
freeze : MArray n a -@ !* IArray n a
freeze (MA arr) = MkBang $ IA arr
