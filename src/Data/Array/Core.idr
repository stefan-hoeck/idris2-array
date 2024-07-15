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

%foreign "scheme:(lambda (u n x) (make-vector n x))"
         "javascript:lambda:(u,n,x) => new Array(n).fill(x)"
prim__fillArr : Bits32 -> a -> ArrayData a

%foreign "scheme:(lambda (u x) (make-vector x))"
         "javascript:lambda:(u,x) => new Array(n)"
prim__newArr : Bits32 -> ArrayData a

%foreign "scheme:(lambda (u v x) (vector-ref v x))"
         "javascript:lambda:(u,v,x) => v[x]"
%extern prim__arrGet : ArrayData a -> Bits32 -> a

%foreign "scheme:(lambda (s u v x w t) (begin (vector-set! v x w) t))"
         "javascript:lambda:(s,u,v,x,w,t) => {v[x] = w; return t}"
%extern prim__arrSet : ArrayData a -> Bits32 -> a -> (1 t : T1 s) -> T1 s

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
at (IA ad) m = prim__arrGet ad (cast $ finToNat m)

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
data MArray : (tag : k) -> (s : Type) -> (n : Nat) -> (a : Type) -> Type where
  [search tag s]
  MA : (arr : ArrayData a) -> MArray tag s n a

--------------------------------------------------------------------------------
-- Tagged utilities
--------------------------------------------------------------------------------

||| Fills a new mutable bound to linear computation `s`.
export %noinline
newMArrayAt : (0 tag : _) -> (n : Nat) -> a -> F1 s (MArray tag s n a)
newMArrayAt tag n v t = MA (prim__fillArr (cast n) v) # t

export %noinline
unsafeNewMArrayAt : (0 tag : _) -> (n : Nat) -> F1 s (MArray tag s n a)
unsafeNewMArrayAt tag n t = MA (prim__newArr (cast n)) # t

||| Safely write a value to a mutable array.
export %noinline
setAt : (0 tag : _) -> MArray tag s n a => Fin n -> a -> F1' s
setAt tag @{MA arr} ix v t = prim__arrSet arr (cast $ finToNat ix) v t

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new linear token of quantity one to be further used in the
||| linear context.
export %noinline
getAt : (0 tag : _) -> MArray tag s n a => Fin n -> F1 s a
getAt tag @{MA arr} ix t = prim__arrGet arr (cast $ finToNat ix) # t

||| Safely modify a value in a mutable array.
export
modifyAt : (0 tag : _) -> MArray tag s n a => Fin n -> (a -> a) -> F1' s
modifyAt tag ix f t =
  let v # t1 := Core.getAt tag ix t
   in setAt tag ix (f v) t1

--------------------------------------------------------------------------------
-- Untagged utilities
--------------------------------------------------------------------------------

||| Untagged version of `newMArrayAt`
export %inline
newMArray : (n : Nat) -> a -> F1 s (MArray () s n a)
newMArray = newMArrayAt ()

export %inline
unsafeNewMArray : (n : Nat) -> F1 s (MArray () s n a)
unsafeNewMArray = unsafeNewMArrayAt ()

||| Untagged version of `setAt`
export %inline
set : MArray () s n a => Fin n -> a -> F1' s
set = setAt ()

||| Untagged version of `getAt`
export %inline
get : MArray () s n a => Fin n -> F1 s a
get = getAt ()

||| Untagged version of `modifyAt`
export %inline
modify : MArray () s n a => Fin n -> (a -> a) -> F1' s
modify = modifyAt ()

--------------------------------------------------------------------------------
-- Allocating Arrays
--------------------------------------------------------------------------------

public export
0 WithMArray : Nat -> (a,b : Type) -> Type
WithMArray n a b = forall s . MArray () s n a => F1 s b

public export
0 WithMArrayUr : Nat -> (a,b : Type) -> Type
WithMArrayUr n a b = forall s . MArray () s n a => (1 t : T1 s) -> Ur b

||| Allocate a mutable array in a linear context.
|||
||| Note: In case you want to freeze the array and return it in the
||| result, use `allocUr`.
export
alloc : (n : Nat) -> a -> (fun : WithMArray n a b) -> b
alloc n v f =
  run1 $ \t => let arr # t2 := newMArray n v t in f @{arr} t2

||| Allocate and potentially freeze a mutable array in a linear context.
|||
||| Note: In case you don't need to freeze the array in the end, you
|||       might also use `alloc`
export
allocUr : (n : Nat) -> a -> (fun : WithMArrayUr n a b) -> b
allocUr n v f =
  runUr $ \t => let arr # t2 := newMArray n v t in f @{arr} t2

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
unsafeAlloc : (n : Nat) -> (fun : WithMArray n a b) -> b
unsafeAlloc n f = alloc n (believe_me ()) f

||| Like `allocUr` but the initially created array will not hold any
||| sensible data.
|||
||| Use with care: Client code is responsible to properly initialize
||| the array with data. This is usefule for creating arrays of unknown
||| size, when it is not immediately clear, whether it will hold any
||| data at all.
|||
||| See for instance the implementation of `filter` or `mapMaybe`.
export
unsafeAllocUr : (n : Nat) -> (fun : WithMArrayUr n a b) -> b
unsafeAllocUr n f = allocUr n (believe_me ()) f

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
export %noinline
freezeAtLTE :
     (0 tag : _)
  -> {auto 0 _ : LTE m n}
  -> {auto arr : MArray tag s n a}
  -> (0 m : Nat)
  -> T1 s
  -@ Ur (IArray m a)
freezeAtLTE tag @{_} @{MA arr} _ t = discard t (MkBang $ IA arr)

||| Wrap a mutable array in an `IArray`, which can then be freely shared.
|||
||| See `freezeLTE` for some additional notes about how this works under
||| the hood.
export %inline
freezeAt : (0 tag : _) -> MArray tag s n a => T1 s -@ Ur (IArray n a)
freezeAt tag = freezeAtLTE tag @{reflexive} n

||| Untagged version of `freezeAtLTE`
export %inline
freezeLTE :
     {auto 0 p : LTE m n}
  -> {auto arr : MArray () s n a}
  -> (0 m : Nat)
  -> T1 s
  -@ Ur (IArray m a)
freezeLTE = freezeAtLTE () @{p}

||| Untagged version of `freeze`
export %inline
freeze : MArray () s n a => T1 s -@ Ur (IArray n a)
freeze = freezeAt ()
