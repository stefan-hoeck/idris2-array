||| Core data types and functions for working with immutable and
||| mutable (linear) arrays.
module Data.Array.Core

import public Data.Linear
import public Data.Fin
import public Data.Nat

%default total

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

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

||| An immutable array of size `n` holding values of type `a`.
export
record IArray (n : Nat) (a : Type) where
  constructor IA
  arr : ArrayData a

||| Safely access a value in an array at the given position.
export
at : IArray n a -> Fin n -> a
at (IA ad) m = prim__arrayGet ad (cast $ finToNat m) %MkWorld

||| We can wrap a prefix of an array in O(1) simply by giving it
||| a new size index.
|||
||| Note: If you only need a small portion of a potentially large
|||       array the resto of which you no longer need, consider to
|||       release the large array from memory by invoking `force`.
export
take : (0 m : Nat) -> IArray n a -> {auto 0 lte : LTE m n} -> IArray m a
take _ (IA arr) = IA arr

--------------------------------------------------------------------------------
--          Mutable Arrays
--------------------------------------------------------------------------------

||| An alias for the `!*` type constructor.
|||
||| `Ur` is an abbreviation for "unrestricted", meaning the wrapped value
||| can be used an arbitrary number of times, even if the `Ur` itself is used
||| in a linear context.
public export
0 Ur : Type -> Type
Ur = (!*)

||| A mutable array.
export
record MArray (n : Nat) (a : Type) where
  constructor MA
  arr : ArrayData a

||| Allocate and release a mutable array in a linear context.
|||
||| Function `fun` must use the given array exactly once, while
||| its result must be wrapped in a `Ur`, guaranteeing, that the
||| mutable array will never be used outside of `fun`, especially
||| that the result `b` does not hold a reference to the mutable
||| array.
export
alloc : (n : Nat) -> a -> (1 fun : MArray n a -@ Ur b) -> Ur b
alloc n v f = f (MA $ prim__newArray (cast n) v %MkWorld)

||| Like `alloc` but the initially created array will not hold any
||| sensible data.
|||
||| Use with care: Client code is responsible to properly initialize
||| the array with data. This is usefule for creating arrays of unknown
||| size, when it is not immediately clear, whether it will hold any
||| data at all.
|||
||| See for instance the implementation of `filter` or `mapMaybe`.
export
unsafeAlloc : (n : Nat) -> (MArray n a -@ Ur b) -@ Ur b
unsafeAlloc n f = alloc n (believe_me ()) f

||| Safely write a value to a mutable array.
|||
||| Since the array must be used exactly once, a "new" array (the
||| same array wrapped in a new `MA`) must be returned, which will
||| then again be used exactly once.
|||
||| Implementation note: This works, because the `ArrayData` value
||| wrapped in an `MArray` has unrestricted quantity. So "using an `MArray`
||| exactly once" means "pattern match on the value, extract the inner
||| array data, and use it as often as you like". This is the reason why
||| `MArray` and `IArray` are not `public export`: We don't want to leak
||| the wrapped `ArrayData` to the outer world.
export
set : Fin n -> a -> MArray n a -@ MArray n a
set m x (MA arr) = MA $ set' (finToNat m) x arr

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new `MArray` of quantity one to be further used in the
||| linear context. See implementation notes on `set` about some details,
||| how this works.
export
get : Fin n -> MArray n a -@ Res a (const $ MArray n a)
get m (MA arr) = prim__arrayGet arr (cast $ finToNat m) %MkWorld # MA arr

||| Wrap a mutable array in an `IArray`, which can then be freely shared.
|||
||| It is not possible the extract and share the underlying `ArrayData`
||| wrapped in an `IArray`, so we don't have to be afraid of shared mutable
||| state: The interface of `IArray` does not support to further mutate
||| the wrapped array.
|||
||| It is safe to only use a prefix of a properly constructed array,
||| therefore we are free to give the resulting array a smaller size.
||| Most of the time, we'd like to use the whole array, in which case
||| we can just use `freeze`.
export
freezeLTE : (0 m : Nat) -> (0 _ : LTE m n) => MArray n a -@ Ur (IArray m a)
freezeLTE _ (MA arr) = MkBang $ IA arr

||| Wrap a mutable array in an `IArray`, which can then be freely shared.
|||
||| See `freezeLTE` for some additional notes about how this works under
||| the hood.
export %inline
freeze : MArray n a -@ Ur (IArray n a)
freeze = freezeLTE n @{reflexive}
