||| Core data types and functions for working with immutable and
||| mutable (linear) arrays.
module Data.Array.Core

import Data.Linear
import Data.Linear.Token
import Data.Fin
import Data.Nat

%default total

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

data ArrayData : Type -> Type where [external]

%extern prim__newArray : forall a . Bits32 -> a -> %World -> (ArrayData a)
%extern prim__arrayGet : forall a . ArrayData a -> Bits32 -> %World -> a
%extern prim__arraySet : forall a . ArrayData a -> Bits32 -> a -> PrimIO ()

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

||| A mutable array.
export
record MArray (n : Nat) (a : Type) where
  [noHints]
  constructor MA
  arr : ArrayData a

public export
0 WithMArray : Nat -> (a,b : Type) -> Type
WithMArray n a b = (s : MArray n a) => (1 t : T1 s) -> Ur b

||| Allocate and release a mutable array in a linear context.
|||
||| Function `fun` must use the given array exactly once, while
||| its result must be wrapped in a `Ur`, guaranteeing, that the
||| mutable array will never be used outside of `fun`, especially
||| that the result `b` does not hold a reference to the mutable
||| array.
export
alloc : (n : Nat) -> a -> (1 fun : WithMArray n a b) -> Ur b
alloc n v f = f @{MA $ prim__newArray (cast n) v %MkWorld} (MkT1 %MkWorld)

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
unsafeAlloc : (n : Nat) -> (1 fun : WithMArray n a b) -> Ur b
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
export %inline
set : (s : MArray n a) => Fin n -> a -> F1' s
set @{MA arr} ix v (MkT1 w) =
  let MkIORes () w2 := prim__arraySet arr (cast $ finToNat ix) v w
   in MkT1 w2

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new `MArray` of quantity one to be further used in the
||| linear context. See implementation notes on `set` about some details,
||| how this works.
export %inline
get : (s : MArray n a) => Fin n -> F1 s a
get @{MA arr} ix (MkT1 w) =
  prim__arrayGet arr (cast $ finToNat ix) %MkWorld # MkT1 w

||| Safely modify a value in a mutable array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this returns a new `MArray` wrapper, which must then
||| again be used exactly once.
export
modify : (s : MArray n a) => Fin n -> (a -> a) -> F1' s
modify ix f t =
  let v # t1 := get ix t
   in set ix (f v) t1

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
freezeLTE :
     {auto 0 _ : LTE m n}
  -> {auto s : MArray n a}
  -> (0 m : Nat)
  -> T1 s
  -@ Ur (IArray m a)
freezeLTE @{_} @{MA arr} _ t = unsafeDiscard t (MkBang $ IA arr)

||| Wrap a mutable array in an `IArray`, which can then be freely shared.
|||
||| See `freezeLTE` for some additional notes about how this works under
||| the hood.
export %inline
freeze : WithMArray n a (IArray n a)
freeze = freezeLTE @{reflexive} n

||| Safely discard a linear mutable array.
export %inline
discard : (s : MArray n a) => T1 s -@ ()
discard t = unsafeDiscard t ()

||| Safely discard a linear mutable array, returning a non-linear
||| result at the same time.
export %inline
discarding : (s : MArray n a) => (1 t : T1 s) -> x -> x
discarding t x = unsafeDiscard t x
