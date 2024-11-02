||| Core data types and functions for working with immutable and
||| mutable (linear) arrays.
module Data.Array.Core

import Data.Linear
import Data.Linear.Token
import Data.Fin
import Data.Nat

import Syntax.T1

%default total

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (x) (make-vector x))"
         "javascript:lambda:(n) => new Array(n)"
prim__emptyArray : Bits32 -> PrimIO AnyPtr

%extern prim__newArray : forall a . Bits32 -> a -> PrimIO AnyPtr
%extern prim__arrayGet : forall a . AnyPtr -> Bits32 -> PrimIO a
%extern prim__arraySet : forall a . AnyPtr -> Bits32 -> a -> PrimIO ()

--------------------------------------------------------------------------------
--          Immutable Arrays
--------------------------------------------------------------------------------

||| An immutable array of size `n` holding values of type `a`.
export
record IArray (n : Nat) (a : Type) where
  constructor IA
  arr : AnyPtr

||| Safely access a value in an array at the given position.
export %inline
at : IArray n a -> Fin n -> a
at (IA ad) m =
  let MkIORes v _ := prim__arrayGet ad (cast $ finToNat m) %MkWorld
   in v

||| We can wrap a prefix of an array in O(1) simply by giving it
||| a new size index.
|||
||| Note: If you only need a small portion of a potentially large
|||       array the rest of which you no longer need, consider to
|||       release the large array from memory by invoking `force`.
export
take : (0 m : Nat) -> IArray n a -> {auto 0 lte : LTE m n} -> IArray m a
take _ (IA arr) = IA arr

||| We can drop n elements from the start of an array. O(n)
|||
||| Note: If you only need a small portion of a potentially large
|||       array the rest of which you no longer need, consider to
|||       release the large array from memory by invoking `force`.
export
drop : (0 m : Nat) -> IArray n a -> {auto 0 lte : LTE m n} -> IArray (minus n m) a
drop _ (IA arr) = IA arr

--------------------------------------------------------------------------------
--          Mutable Arrays
--------------------------------------------------------------------------------

||| A mutable array.
export
data MArray' : (t : RTag) -> (n : Nat) -> (a : Type) -> Type where
  MA : (arr : AnyPtr) -> MArray' t n a

||| Convenience alias for `MArray' RPure`
public export
0 MArray : Nat -> Type -> Type
MArray = MArray' RPure

||| Convenience alias for `MArray' RIO`
public export
0 IOArray : Nat -> Type -> Type
IOArray = MArray' RIO

public export
InIO (MArray' RIO n a) where

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Fills a new mutable bound to linear computation `s`.
export %inline
newMArray : (n : Nat) -> a -> (1 t : T1 rs) -> A1 rs (MArray n a)
newMArray n v t =
  let m # t := ffi (prim__newArray (cast n) v) t in A (MA m) (unsafeBind t)

||| Fills a new mutable array in `T1 [World]`
export %inline
arrayIO : (n : Nat) -> a -> F1 [World] (IOArray n a)
arrayIO n v t = let m # t := ffi (prim__newArray (cast n) v) t in MA m # t

||| Fills a new mutable array in `IO`
export %inline
newIOArray : HasIO io => (n : Nat) -> a -> io (IOArray n a)
newIOArray n v =
  primIO $ \w =>
    let MkIORes m w := prim__newArray (cast n) v w
     in MkIORes (MA m) w

export %inline
unsafeNewMArray : (n : Nat) -> (1 t : T1 rs) -> A1 rs (MArray n a)
unsafeNewMArray n t =
  let m # t := ffi (prim__emptyArray (cast n)) t in A (MA m) (unsafeBind t)

||| Allocates a new, empty, mutable array in `T1 [Wrold]`
export %inline
unsafeArrayIO : (n : Nat) -> F1 [World] (IOArray n a)
unsafeArrayIO n t = let m # t := ffi (prim__emptyArray (cast n)) t in MA m # t

||| Allocates a new, empty, mutable array in `IO`
export %inline
unsafeNewIOArray : HasIO io => (n : Nat) -> io (IOArray n a)
unsafeNewIOArray n =
  primIO $ \w =>
    let MkIORes m w := prim__emptyArray (cast n) w
     in MkIORes (MA m) w

||| Safely write a value to a mutable array.
export %inline
set : (r : MArray' t n a) -> (0 p : Res r rs) => Fin n -> a -> F1' rs
set (MA arr) ix v = ffi (prim__arraySet arr (cast $ finToNat ix) v)

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new linear token of quantity one to be further used in the
||| linear context.
export %inline
get : (r : MArray' t n a) -> (0 p : Res r rs) => Fin n -> F1 rs a
get (MA arr) ix = ffi (prim__arrayGet arr (cast $ finToNat ix))

||| Safely modify a value in a mutable array.
export %inline
modify : (r : MArray' t n a) -> (0 p : Res r rs) => Fin n -> (a -> a) -> F1' rs
modify r ix f t = let v # t1 := get r ix t in set r ix (f v) t1

||| Wraps a mutable array in a shorter one.
export %inline
mtake :
     (r   : IOArray n a)
  -> (0 m : Nat)
  -> {auto 0 lte : LTE m n}
  -> F1 [World] (IOArray m a)
mtake (MA arr) _ t = MA arr # t

||| Release a mutable linear array.
|||
||| Afterwards, it can no longer be use with the given linear token.
export %inline
release : (0 r : MArray n a) -> (0 p : Res r rs) => C1' rs (Drop rs p)
release _ = unsafeRelease p

--------------------------------------------------------------------------------
-- Allocating Arrays
--------------------------------------------------------------------------------

public export
0 WithMArray : Nat -> (a,b : Type) -> Type
WithMArray n a b = (r : MArray n a) -> F1 [r] b

public export
0 FromMArray : Nat -> (a,b : Type) -> Type
FromMArray n a b = (r : MArray n a) -> C1 [r] [] b

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
alloc n v f =
  create n v $ \r => T1.do
    v <- f r
    release r
    pure v

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
  unsafeCreate n $ \r,t =>
    let v # t := f r t
        _ # t := release r t
     in v # t

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
  -> C1 rs (Drop rs p) (IArray m a)
freezeLTE (MA arr) _ = T1.do
  unsafeRelease p
  pure (IA arr)

||| Wrap a mutable array in an `IArray`, which can then be freely shared.
|||
||| See `freezeLTE` for some additional notes about how this works under the hood.
export %inline
freeze : (r : MArray n a) -> (0 p : Res r rs) => C1 rs (Drop rs p) (IArray n a)
freeze r = freezeLTE @{reflexive} r n
