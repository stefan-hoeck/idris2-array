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

%foreign "scheme:(lambda (n x) (make-vector n x))"
         "javascript:lambda:(n,x) => new Array(n).fill(x)"
prim__fillArr : Bits32 -> AnyPtr -> AnyPtr

%foreign "scheme:(lambda (x) (make-vector x))"
         "javascript:lambda:(n) => new Array(n)"
prim__newArr : Bits32 -> AnyPtr

%foreign "scheme:(lambda (v x) (vector-ref v x))"
         "javascript:lambda:(v,x) => v[x]"
%extern prim__arrGet : AnyPtr -> Bits32 -> AnyPtr

%foreign "scheme:(lambda (v x w t) (begin (vector-set! v x w) t))"
         "javascript:lambda:(v,x,w,t) => {v[x] = w; return t}"
%extern prim__arrSet : AnyPtr -> Bits32 -> AnyPtr -> (1 t : AnyPtr) -> AnyPtr

--------------------------------------------------------------------------------
--          Immutable Arrays
--------------------------------------------------------------------------------

||| An immutable array of size `n` holding values of type `a`.
export
record IArray (n : Nat) (a : Type) where
  constructor IA
  arr : AnyPtr

||| Safely access a value in an array at the given position.
export
at : IArray n a -> Fin n -> a
at (IA ad) m = believe_me (prim__arrGet ad (cast $ finToNat m))

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
data MArray : (n : Nat) -> (a : Type) -> Type where
  MA : (arr : AnyPtr) -> MArray n a

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Fills a new mutable bound to linear computation `s`.
export %noinline
newMArray : (n : Nat) -> a -> (1 t : T1 rs) -> A1 rs (MArray n a)
newMArray n v t = A (MA (prim__fillArr (cast n) (believe_me v))) (unsafeBind t)

export %noinline
unsafeNewMArray : (n : Nat) -> (1 t : T1 rs) -> A1 rs (MArray n a)
unsafeNewMArray n t = A (MA (prim__newArr (cast n))) (unsafeBind t)

||| Safely write a value to a mutable array.
export %noinline
set : (r : MArray n a) -> (0 p : Res r rs) => Fin n -> a -> F1' rs
set (MA arr) ix v = ffi (prim__arrSet arr (cast $ finToNat ix) (believe_me v))

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new linear token of quantity one to be further used in the
||| linear context.
export %noinline
get : (r : MArray n a) -> (0 p : Res r rs) => Fin n -> F1 rs a
get (MA arr) ix t = believe_me (prim__arrGet arr (cast $ finToNat ix)) # t

||| Safely modify a value in a mutable array.
export
modify : (r : MArray n a) -> (0 p : Res r rs) => Fin n -> (a -> a) -> F1' rs
modify r ix f t = let v # t1 := get r ix t in set r ix (f v) t1

||| Release a mutable array.
|||
||| Afterwards, it can no longer be use with the given linear token.
export %inline
release :
     (0 r : MArray n a)
  -> {auto 0 p : Res r rs}
  -> (1 t : T1 rs)
  -> T1 (Drop rs p)
release _ = unsafeRelease p

--------------------------------------------------------------------------------
-- Allocating Arrays
--------------------------------------------------------------------------------

public export
0 WithMArray : Nat -> (a,b : Type) -> Type
WithMArray n a b = (r : MArray n a) -> F1 [r] b

public export
0 FromMArray : Nat -> (a,b : Type) -> Type
FromMArray n a b = (r : MArray n a) -> (1 t : T1 [r]) -> R1 [] b

||| Allocate and potentially freeze a mutable array in a linear context.
|||
||| Note: In case you don't need to freeze the array in the end, using `alloc`
|||       might be more convenient.
export
create : (n : Nat) -> a -> (fun : FromMArray n a b) -> b
create n v f = run1 $ \t => let A r t2 := newMArray n v t in f r t2

||| Allocate, use, and release a mutable array in a linear computation.
|||
||| Note: In case you want to freeze the array and return it in the
|||       result, use `create`.
export
alloc : (n : Nat) -> a -> (fun : WithMArray n a b) -> b
alloc n v f = create n v $ \r,t => let v # t2 := f r t in v # release r t2

||| Like `create` but the initially created array will not hold any
||| sensible data.
|||
||| Use with care: Client code is responsible to properly initialize
||| the array with data. This is usefule for creating arrays of unknown
||| size, when it is not immediately clear, whether it will hold any
||| data at all.
|||
||| See for instance the implementation of `filter` or `mapMaybe`.
export
unsafeCreate : (n : Nat) -> (fun : FromMArray n a b) -> b
unsafeCreate n f = run1 $ \t => let A r t2 := unsafeNewMArray n t in f r t2

||| Like `alloc` but the initially created array will not hold any
||| sensible data.
|||
||| Use with care: Client code is responsible to properly initialize
||| the array with data. This is useful for creating arrays of unknown
||| size, when it is not immediately clear whether it will hold any
||| data at all.
|||
||| See for instance the implementation of `filter` or `mapMaybe`.
export
unsafeAlloc : (n : Nat) -> (fun : WithMArray n a b) -> b
unsafeAlloc n f =
  unsafeCreate n $ \r,t => let v # t2 := f r t in v # release r t2

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
export %inline
freezeLTE :
     {auto 0 _ : LTE m n}
  -> (r        : MArray n a)
  -> {auto 0 p : Res r rs}
  -> (0 m : Nat)
  -> (1 t : T1 rs)
  -> R1 (Drop rs p) (IArray m a)
freezeLTE (MA arr) _ t = IA arr # unsafeRelease p t

||| Wrap a mutable array in an `IArray`, which can then be freely shared.
|||
||| See `freezeLTE` for some additional notes about how this works under the hood.
export %inline
freeze :
     (r : MArray n a)
  -> {auto 0 p : Res r rs}
  -> (1 t : T1 rs)
  -> R1 (Drop rs p) (IArray n a)
freeze r = freezeLTE @{reflexive} r n
