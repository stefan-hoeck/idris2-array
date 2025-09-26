||| Core data types and functions for working with immutable and
||| mutable (linear) arrays.
module Data.Array.Core

import Data.Array.Index
import Data.Buffer
import Data.Linear
import Data.Linear.Token
import Data.Fin
import Data.Nat

import Data.Buffer.Core as BC

import Syntax.T1

%default total

%hide BC.get
%hide BC.icopy
%hide BC.copy

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

export
%foreign "scheme:(lambda (x) (make-vector x))"
         "javascript:lambda:(n,w) => new Array(Number(n))"
prim__emptyArray : Integer -> PrimIO AnyPtr

export
%foreign "scheme:(lambda (x i) (make-vector x i))"
         "javascript:lambda:(bi,x,w) => Array(Number(bi)).fill(x)"
prim__newArray : Integer -> AnyPtr -> PrimIO AnyPtr

export
%foreign "scheme:(lambda (x i) (vector-ref x i))"
         "javascript:lambda:(x,bi) => x[Number(bi)]"
prim__arrayGet : AnyPtr -> Integer -> AnyPtr

-- This is an optimized version of `prim_arrayGet` that allows us to read
-- at an offset. On Chez, we can use the faster fixnum addition here,
-- which can lead to a performance boost.
%foreign "scheme:(lambda (b a o) (vector-ref b (+ a o)))"
         "scheme,chez:(lambda (b a o) (vector-ref b (fx+ a o)))"
         "javascript:lambda:(buf,at,offset)=>buf[Number(offset) + Number(at)]"
prim__arrayGetOffset : AnyPtr -> (at, offset : Integer) -> AnyPtr

export
%foreign "scheme:(lambda (x i w) (vector-set! x i w))"
         "javascript:lambda:(x,bi,w) => {const i = Number(bi); x[i] = w}"
prim__arraySet : AnyPtr -> Integer -> (val : AnyPtr) -> PrimIO ()

export
%foreign "scheme:(lambda (a x i v w) (if (vector-cas! x i v w) 1 0))"
         "javascript:lambda:(a,x,bi,v,w) => {const i = Number(bi); if (x[i] === v) {x[i] = w; return 1;} else {return 0;}}"
prim__casSet : AnyPtr -> Integer -> (prev,val : a) -> Bits8

export
%foreign "scheme: (lambda (b1 o1 len b2 o2) (letrec ((go (lambda (i) (when (< i len) (begin (vector-set! b2 (+ o2 i) (vector-ref b1 (+ o1 i))) (go (+ 1 i))))))) (go 0)))"
         "scheme,chez: (lambda (b1 o1 len b2 o2) (letrec ((go (lambda (i) (when (< i len) (begin (vector-set! b2 (fx+ o2 i) (vector-ref b1 (fx+ o1 i))) (go (fx+ 1 i))))))) (go 0)))"
         "javascript:lambda:(b1,bo1,blen,b2,bo2,t)=> {const o1 = Number(bo1); const len = Number(blen); const o2 = Number(bo2); for (let i = 0; i < len; i++) {b2[o2+i] = b1[o1+i];}; return t}"
prim__copyArray : (src : AnyPtr) -> (srcOffset, len : Integer) ->
                  (dst : AnyPtr) -> (dstOffset : Integer) -> PrimIO ()

export
%foreign "scheme: (lambda (b1 o1 len b2 o2) (letrec ((go (lambda (i) (when (< i len) (begin (vector-set! b2 (+ o2 i) (bytevector-u8-ref b1 (+ o1 i))) (go (+ 1 i))))))) (go 0)))"
         "scheme,chez: (lambda (b1 o1 len b2 o2) (letrec ((go (lambda (i) (when (< i len) (begin (vector-set! b2 (fx+ o2 i) (bytevector-u8-ref b1 (fx+ o1 i))) (go (fx+ 1 i))))))) (go 0)))"
         "javascript:lambda:(b1,bo1,blen,b2,bo2,t)=> {const o1 = Number(bo1); const len = Number(blen); const o2 = Number(bo2); for (let i = 0; i < len; i++) {b2[o2+i] = b1[o1+i];}; return t}"
prim__bufToArr : (src : Buffer) -> (srcOffset, len : Integer) ->
                 (dst : AnyPtr) -> (dstOffset : Integer) -> PrimIO ()

export
%foreign "scheme: (lambda (b1 o1 len b2 o2) (letrec ((go (lambda (i) (when (< i len) (begin (bytevector-u8-set! b2 (+ o2 i) (vector-ref b1 (+ o1 i))) (go (+ 1 i))))))) (go 0)))"
         "scheme,chez: (lambda (b1 o1 len b2 o2) (letrec ((go (lambda (i) (when (< i len) (begin (bytevector-u8-set! b2 (fx+ o2 i) (vector-ref b1 (fx+ o1 i))) (go (fx+ 1 i))))))) (go 0)))"
         "javascript:lambda:(b1,bo1,blen,b2,bo2,t)=> {const o1 = Number(bo1); const len = Number(blen); const o2 = Number(bo2); for (let i = 0; i < len; i++) {b2[o2+i] = b1[o1+i];}; return t}"
prim__arrToBuf : (src : AnyPtr) -> (srcOffset, len : Integer) ->
                 (dst : Buffer) -> (dstOffset : Integer) -> PrimIO ()

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
at (IA ad) m = believe_me $ prim__arrayGet ad (cast $ finToNat m)

||| Safely use a byte as an index into an array.
export %inline
atByte : IArray 256 a -> Bits8 -> a
atByte (IA ad) m = believe_me $ prim__arrayGet ad (cast m)

||| Safely access a value in an array at the given position
||| and offset.
export %inline
atOffset : IArray n a -> Fin m -> (off : Nat) -> (0 p : LTE (off+m) n) => a
atOffset (IA ad) m off =
  believe_me $ prim__arrayGetOffset ad (cast $ finToNat m) (cast off)

||| We can wrap a prefix of an array in O(1) simply by giving it
||| a new size index.
|||
||| Note: If you only need a small portion of a potentially large
|||       array the rest of which you no longer need, consider to
|||       release the large array from memory by invoking `force`.
export
take : (0 m : Nat) -> IArray n a -> {auto 0 lte : LTE m n} -> IArray m a
take _ (IA arr) = IA arr

--------------------------------------------------------------------------------
--          Mutable Arrays
--------------------------------------------------------------------------------

||| A mutable array.
export
data MArray : (s : Type) -> (n : Nat) -> (a : Type) -> Type where
  MA : (arr : AnyPtr) -> MArray s n a

||| Convenience alias for `MArray' RIO`.
public export
0 IOArray : Nat -> Type -> Type
IOArray = MArray World

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Fills a new mutable bound to linear computation `s`.
export %inline
marray1 : (n : Nat) -> a -> F1 s (MArray s n a)
marray1 n v t =
  let p # t := ffi (prim__newArray (cast n) (believe_me v)) t in MA p # t

||| Fills a new mutable array in `IO`.
export %inline
marray : Lift1 s f => (n : Nat) -> a -> f (MArray s n a)
marray n v = lift1 (marray1 n v)

export %inline
unsafeMArray1 : (n : Nat) -> F1 s (MArray s n a)
unsafeMArray1 n t =
  let p # t := ffi (prim__emptyArray (cast n)) t in MA p # t

||| Allocates a new, empty, mutable array in `IO`.
export %inline
unsafeMArray : Lift1 s f => (n : Nat) -> f (MArray s n a)
unsafeMArray n = lift1 (unsafeMArray1 n)

||| Safely write a value to a mutable array.
export %inline
set : (r : MArray s n a) -> Fin n -> a -> F1' s
set (MA arr) ix v = ffi (prim__arraySet arr (cast $ finToNat ix) (believe_me v))

||| Safely write a value to a mutable array.
export %inline
setBits8 : (r : MArray s 256 a) -> Bits8 -> a -> F1' s
setBits8 (MA arr) ix v = ffi (prim__arraySet arr (cast ix) (believe_me v))

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new linear token of quantity one to be further used in the
||| linear context.
export %inline
get : (r : MArray s n a) -> Fin n -> F1 s a
get (MA arr) ix t = believe_me (prim__arrayGet arr (cast $ finToNat ix)) # t

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new linear token of quantity one to be further used in the
||| linear context.
export %inline
getBits8 : (r : MArray s 256 a) -> Bits8 -> F1 s a
getBits8 (MA arr) ix t = believe_me (prim__arrayGet arr (cast ix)) # t

||| Safely modify a value in a mutable array.
export %inline
modify : (r : MArray s n a) -> Fin n -> (a -> a) -> F1' s
modify r ix f t = let v # t1 := get r ix t in set r ix (f v) t1

||| Atomically writes `val` at the given position of the mutable array
||| if its current value is equal to `pre`.
|||
||| This is supported and has been tested on the Chez and Racket backends.
||| It trivially works on the JavaScript backends, which are single-threaded
||| anyway.
export %inline
casset : (r : MArray s n a) -> Fin n -> (pre,val : a) -> F1 s Bool
casset (MA arr) x pre val t =
  case prim__casSet arr (cast $ finToNat x) pre val of
    0 => False # t
    _ => True # t

||| Atomic modification of an array position using a CAS-loop internally.
|||
||| This is supported and has been tested on the Chez and Racket backends.
||| It trivially works on the JavaScript backends, which are single-threaded
||| anyway.
export
casupdate : (r : MArray s n a) -> Fin n -> (a -> (a,b)) -> F1 s b
casupdate r x f t = assert_total (loop t)
  where
    covering loop : F1 s b
    loop t =
      let cur # t  := get r x t
          (new,v)  := f cur
          True # t := casset r x cur new t | _ # t => loop t
       in v # t

||| Atomic modification of an array position reference using a CAS-loop
||| internally.
|||
||| This is supported and has been tested on the Chez and Racket backends.
||| It trivially works on the JavaScript backends, which are single-threaded
||| anyway.
export
casmodify : (r : MArray s n a) -> Fin n -> (a -> a) -> F1' s
casmodify r x f t = assert_total (loop t)
  where
    covering loop : F1' s
    loop t =
      let cur  # t := get r x t
          True # t := casset r x cur (f cur) t | _ # t => loop t
       in () # t

||| Wraps a mutable array in a shorter one.
export %inline
mtake : MArray s n a -> (0 m : Nat) -> (0 lte : LTE m n) => F1 s (MArray s m a)
mtake (MA arr) _ t = MA arr # t

export %noinline
copy :
     MArray s m a
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MArray s n a)
  -> F1' s
copy (MA src) srcOffset dstOffset len (MA dst) =
  ffi (prim__copyArray src (cast srcOffset) (cast len) dst (cast dstOffset))

export %inline
icopy :
     IArray m a
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MArray s n a)
  -> F1' s
icopy (IA src) = copy {m} (MA src)

export %noinline
copyToBuf :
     MArray s m Bits8
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MBuffer s n)
  -> F1' s
copyToBuf (MA src) srcOffset dstOffset len dst =
  ffi (prim__arrToBuf src (cast srcOffset) (cast len) (unsafeFromMBuffer dst) (cast dstOffset))

export %inline
icopyToBuf :
     IArray m Bits8
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MBuffer s n)
  -> F1' s
icopyToBuf (IA src) = copyToBuf {m} (MA src)

export %noinline
copyToArray :
     MBuffer s m
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MArray s n Bits8)
  -> F1' s
copyToArray src srcOffset dstOffset len (MA dst) =
  ffi (prim__bufToArr (unsafeFromMBuffer src) (cast srcOffset) (cast len) dst (cast dstOffset))

export %inline
icopyToArray :
     IBuffer m
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MArray s n Bits8)
  -> F1' s
icopyToArray buf = copyToArray {m} (unsafeMBuffer $ unsafeGetBuffer buf)

||| Copy the content of an immutable array to a new mutable array.
export
thaw : {n : _} -> IArray n a -> F1 s (MArray s n a)
thaw src t =
    let r # t := unsafeMArray1 n t
        _ # t := icopy src 0 0 n @{reflexive} @{reflexive} r t
     in r # t

||| Make the content of an immutable array accessible as a mutable array.
|||
||| This is obviously unsafe. Don't use if you don't know exactly what you
||| are doing.
export
unsafeThaw : IArray n a -> MArray s n a
unsafeThaw (IA arr) = MA arr

--------------------------------------------------------------------------------
-- Allocating Arrays
--------------------------------------------------------------------------------

public export
0 WithMArray : Nat -> (a,b : Type) -> Type
WithMArray n a b = forall s . (r : MArray s n a) -> F1 s b

||| Allocate and use a mutable array in a linear context.
export
alloc : (n : Nat) -> a -> (fun : WithMArray n a b) -> b
alloc n v f = run1 $ \t => let r # t2 := marray1 n v t in f r t2

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
unsafeAlloc : (n : Nat) -> (fun : WithMArray n a b) -> b
unsafeAlloc n f = run1 $ \t => let r # t2 := unsafeMArray1 n t in f r t2

||| Wrap a mutable array in an immutable array, which can then be freely shared.
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
  -> (r        : MArray s n a)
  -> (0 m : Nat)
  -> F1 s (IArray m a)
unsafeFreezeLTE (MA arr) _ t = IA arr # t

||| Wrap a mutable array in an immutable array, which can then be freely shared.
|||
||| Note: For reasons of efficiency, this does not copy the mutable array,
|||       and therefore, it must no longer be modified after calling
|||       this function.
export %inline
unsafeFreeze : (r : MArray s n a) -> F1 s (IArray n a)
unsafeFreeze r = unsafeFreezeLTE @{reflexive} r n

||| Copy a prefix of a mutable array into an immutable array.
export
freezeLTE : MArray s n a -> (m : Nat) -> (0 p : LTE m n) => F1 s (IArray m a)
freezeLTE src m t =
  let r@(MA buf) # t := unsafeMArray1 m t
      _          # t := copy src 0 0 m @{p} @{reflexive} r t
   in IA buf     # t

||| Copy a mutable buffer into an `IBuffer`.
export %inline
freeze : {n : _} -> MArray s n a -> F1 s (IArray n a)
freeze src = freezeLTE src n @{reflexive}

--------------------------------------------------------------------------------
--          Array Conversions
--------------------------------------------------------------------------------

||| Copies an immutable array of bytes to a immutable buffer.
export
toIBuffer : {n : _} -> IArray n Bits8 -> IBuffer n
toIBuffer arr =
  alloc n $ \buf,t =>
   let _ # t := icopyToBuf arr 0 0 n buf t
    in unsafeFreeze buf t

||| Copies an immtuable buffer to an immutable array of bytes.
export
toIArray : {n : _} -> IBuffer n -> IArray n Bits8
toIArray buf =
  alloc n (the Bits8 0) $ \arr,t =>
   let _ # t := icopyToArray buf 0 0 n arr t
    in unsafeFreeze arr t
