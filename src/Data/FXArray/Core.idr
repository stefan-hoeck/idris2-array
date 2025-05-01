||| Mutable and immutable integer arrays
module Data.FXArray.Core

import Data.Array.Index
import Data.Linear
import Data.Linear.Token
import Data.Fin
import Data.Nat

import Syntax.T1

%default total

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (x i) (make-fxvector x i))"
         "javascript:lambda:(bi,x,w) => Array(Number(bi)).fill(x)"
prim__newArray : Integer -> Bits32 -> PrimIO AnyPtr

%foreign "scheme:(lambda (x i) (fxvector-ref x i))"
         "javascript:lambda:(x,bi) => x[Number(bi)]"
prim__arrayGet : AnyPtr -> Integer -> Bits32

%foreign "scheme:(lambda (x i w) (fxvector-set! x i w))"
         "javascript:lambda:(x,bi,w) => {const i = Number(bi); x[i] = w}"
prim__arraySet : AnyPtr -> Integer -> (val : Bits32) -> PrimIO ()

--------------------------------------------------------------------------------
--          Immutable Arrays
--------------------------------------------------------------------------------

||| An immutable array of size `n` holding values of type `a`.
export
record FXArray (n : Nat) where
  constructor FA
  arr : AnyPtr

||| Safely access a value in an array at the given position.
export %inline
at : FXArray n -> Fin n -> Bits32
at (FA ad) m = prim__arrayGet ad (cast $ finToNat m)

||| Safely use a byte as an index into an array.
export %inline
atByte : FXArray 256 -> Bits8 -> Bits32
atByte (FA ad) m = prim__arrayGet ad (cast m)

--------------------------------------------------------------------------------
--          Mutable Arrays
--------------------------------------------------------------------------------

||| A mutable array.
export
data FXMArray : (s : Type) -> (n : Nat) -> Type where
  MA : (arr : AnyPtr) -> FXMArray s n

||| Convenience alias for `FXMArray World`.
public export
0 IOFXArray : Nat -> Type
IOFXArray = FXMArray World

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Fills a new mutable bound to linear computation `s`.
export %inline
fxmarray1 : (n : Nat) -> Bits32 -> F1 s (FXMArray s n)
fxmarray1 n v t =
  let p # t := ffi (prim__newArray (cast n) (believe_me v)) t in MA p # t

||| Fills a new mutable array in `IO`.
export %inline
fxmarray : Lift1 s f => (n : Nat) -> Bits32 -> f (FXMArray s n)
fxmarray n v = lift1 (fxmarray1 n v)

||| Safely write a value to a mutable array.
export %inline
fxset : (r : FXMArray s n) -> Fin n -> Bits32 -> F1' s
fxset (MA arr) ix v = ffi (prim__arraySet arr (cast $ finToNat ix) v)

||| Safely write a value to a mutable array.
export %inline
fxsetBits8 : (r : FXMArray s 256) -> Bits8 -> Bits32 -> F1' s
fxsetBits8 (MA arr) ix v = ffi (prim__arraySet arr (cast ix) v)

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new linear token of quantity one to be further used in the
||| linear context.
export %inline
fxget : (r : FXMArray s n) -> Fin n -> F1 s Bits32
fxget (MA arr) ix t = prim__arrayGet arr (cast $ finToNat ix) # t

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new linear token of quantity one to be further used in the
||| linear context.
export %inline
fxgetBits8 : (r : FXMArray s 256) -> Bits8 -> F1 s Bits32
fxgetBits8 (MA arr) ix t = prim__arrayGet arr (cast ix) # t

--------------------------------------------------------------------------------
-- Allocating Arrays
--------------------------------------------------------------------------------

public export
0 WithFXMArray : Nat -> (a : Type) -> Type
WithFXMArray n a = forall s . (r : FXMArray s n) -> F1 s a

||| Allocate and use a mutable array in a linear context.
export
alloc : (n : Nat) -> Bits32 -> (fun : WithFXMArray n a) -> a
alloc n v f = run1 $ \t => let r # t2 := fxmarray1 n v t in f r t2

||| Wrap a mutable array in an `FXArray`, which can then be freely shared.
|||
||| It is not possible the extract and share the underlying `ArrayData`
||| wrapped in an `IArray`, so we don't have to be afraid of shared mutable
||| state: The interface of `IArray` does not support to further mutate
||| the wrapped array.
|||
||| It is safe to only use a prefix of a properly constructed array,
||| therefore we are free to give the resulting array a smaller size.
||| Most of the time, we'd like to use the whole array, in which case
||| we can just use `unsafeFreeze`.
|||
||| Note: For reasons of efficiency, this does not copy the mutable array,
|||       and therefore, it must no longer be modified after calling
|||       this function.
export %inline
unsafeFreezeLTE :
     {auto 0 _ : LTE m n}
  -> (r        : FXMArray s n)
  -> (0 m : Nat)
  -> F1 s (FXArray m)
unsafeFreezeLTE (MA arr) _ t = FA arr # t

||| Wrap a mutable array in an `FXArray`, which can then be freely shared.
|||
||| Note: For reasons of efficiency, this does not copy the mutable array,
|||       and therefore, it must no longer be modified after calling
|||       this function.
export %inline
unsafeFreeze : (r : FXMArray s n) -> F1 s (FXArray n)
unsafeFreeze r = unsafeFreezeLTE @{reflexive} r n
