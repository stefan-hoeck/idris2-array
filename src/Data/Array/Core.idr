module Data.Array.Core

import public Data.Linear
import Data.Nat

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
record Array (n : Nat) (a : Type) where
  constructor A
  arr : ArrayData a

export
at : Array n a -> (m : Nat) -> {auto 0 lt : LT m n} -> a
at (A ad) m = prim__arrayGet ad (cast m) %MkWorld

--------------------------------------------------------------------------------
--          Mutable Arrays
--------------------------------------------------------------------------------

public export
record P1 a b where
  constructor (#)
  fst   : a
  1 snd : b

export
record MArray (n : Nat) (a : Type) where
  constructor MA
  arr : ArrayData a

export
alloc : (n : Nat) -> a -> (MArray n a -@ !* b) -@ !* b
alloc n v f = f (MA $ prim__newArray (cast n) v %MkWorld)

export
set : (m : Nat) -> {auto 0 p : LT m n} -> a -> MArray n a -@ MArray n a
set m x (MA arr) = MA $ set' m x arr

export
get : (m : Nat) -> {auto 0 p : LT m n} -> MArray n a -@ P1 a (MArray n a)
get m (MA arr) = prim__arrayGet arr (cast m) %MkWorld # MA arr

export
freeze : MArray n a -@ !* Array n a
freeze (MA arr) = MkBang $ A arr
