module Data.Buffer.Packed

import Data.Buffer
import Data.Buffer.Core
import Data.Linear.Ref1
import Data.Linear.Token

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (b o) (bytevector-u8-ref b o))"
         "javascript:lambda:(buf,offset)=>buf[Number(offset)]"
prim__getBits8 : Buffer -> (offset : Integer) -> Bits8

%foreign "scheme:(lambda (b o v) (bytevector-u8-set! b o v))"
         "javascript:lambda:(buf,offset,value,t)=>{buf[Number(offset)] = value; return t}"
prim__setBits8 : Buffer -> (offset : Integer) -> Bits8 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-u16-ref b o 'little))"
         "javascript:lambda:(buf,offset)=>new DataView(buf.buffer, buf.byteOffset, buf.byteLength).getUint16(Number(offset), true)"
prim__getBits16 : Buffer -> (offset : Integer) -> Bits16

%foreign "scheme:(lambda (b o v) (bytevector-u16-set! b o v 'little))"
         "javascript:lambda:(buf,offset,value,t)=>{new DataView(buf.buffer, buf.byteOffset, buf.byteLength).setUint16(Number(offset), value, true); return t}"
prim__setBits16 : Buffer -> (offset : Integer) -> Bits16 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-u32-ref b o 'little))"
         "javascript:lambda:(buf,offset)=>new DataView(buf.buffer, buf.byteOffset, buf.byteLength).getUint32(Number(offset), true)"
prim__getBits32 : Buffer -> (offset : Integer) -> Bits32

%foreign "scheme:(lambda (b o v) (bytevector-u32-set! b o v 'little))"
         "javascript:lambda:(buf,offset,value,t)=>{new DataView(buf.buffer, buf.byteOffset, buf.byteLength).setUint32(Number(offset), value, true); return t}"
prim__setBits32 : Buffer -> (offset : Integer) -> Bits32 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-u64-ref b o 'little))"
         "javascript:lambda:(buf,offset)=>new DataView(buf.buffer, buf.byteOffset, buf.byteLength).getBigUint64(Number(offset), true)"
prim__getBits64 : Buffer -> (offset : Integer) -> Bits64

%foreign "scheme:(lambda (b o v) (bytevector-u64-set! b o v 'little))"
         "javascript:lambda:(buf,offset,value,t)=>{new DataView(buf.buffer, buf.byteOffset, buf.byteLength).setBigUint64(Number(offset), value, true); return t}"
prim__setBits64 : Buffer -> (offset : Integer) -> Bits64 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-s8-ref b o))"
         "javascript:lambda:(buf,offset)=>new Int8Array(buf.buffer, buf.byteOffset, buf.byteLength)[Number(offset)]"
prim__getInt8 : Buffer -> (offset : Integer) -> Int8

%foreign "scheme:(lambda (b o v) (bytevector-s8-set! b o v))"
         "javascript:lambda:(buf,offset,value,t)=>{new Int8Array(buf.buffer, buf.byteOffset, buf.byteLength)[Number(offset)] = value; return t}"
prim__setInt8 : Buffer -> (offset : Integer) -> Int8 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-s16-ref b o 'little))"
         "javascript:lambda:(buf,offset)=>new DataView(buf.buffer, buf.byteOffset, buf.byteLength).getInt16(Number(offset), true)"
prim__getInt16 : Buffer -> (offset : Integer) -> Int16

%foreign "scheme:(lambda (b o v) (bytevector-s16-set! b o v 'little))"
         "javascript:lambda:(buf,offset,value,t)=>{new DataView(buf.buffer, buf.byteOffset, buf.byteLength).setInt16(Number(offset), value, true); return t}"
prim__setInt16 : Buffer -> (offset : Integer) -> Int16 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-s32-ref b o 'little))"
         "javascript:lambda:(buf,offset)=>new DataView(buf.buffer, buf.byteOffset, buf.byteLength).getInt32(Number(offset), true)"
prim__getInt32 : Buffer -> (offset : Integer) -> Int32

%foreign "scheme:(lambda (b o v) (bytevector-s32-set! b o v 'little))"
         "javascript:lambda:(buf,offset,value,t)=>{new DataView(buf.buffer, buf.byteOffset, buf.byteLength).setInt32(Number(offset), value, true); return t}"
prim__setInt32 : Buffer -> (offset : Integer) -> Int32 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-s64-ref b o 'little))"
         "javascript:lambda:(buf,offset)=>new DataView(buf.buffer, buf.byteOffset, buf.byteLength).getBigInt64(Number(offset), true)"
prim__getInt64 : Buffer -> (offset : Integer) -> Int64

%foreign "scheme:(lambda (b o v) (bytevector-s64-set! b o v 'little))"
         "javascript:lambda:(buf,offset,value,t)=>{new DataView(buf.buffer, buf.byteOffset, buf.byteLength).setBigInt64(Number(offset), value, true); return t}"
prim__setInt64 : Buffer -> (offset : Integer) -> Int64 -> PrimIO ()

--------------------------------------------------------------------------------
-- PackedInteger
--------------------------------------------------------------------------------

||| Describes an integral type that can be stored in a packed byte buffer.
|||
||| `bytewidth` gives the number of bytes occupied by each element, while
||| `getPacked` and `setPacked` provide the corresponding low-level access
||| operations.
|||
||| Implementations are provided for `Bits8`, `Bits16`, `Bits32`, `Bits64`, `Int8`, `Int16`, `Int32`, and `Int64`.
public export
interface PackedInteger a where
  bytewidth : Nat
  getPacked : Buffer -> Integer -> a
  setPacked : Buffer -> Integer -> a -> PrimIO ()

public export
PackedInteger Bits8 where
  bytewidth = 1
  getPacked = prim__getBits8
  setPacked = prim__setBits8

public export
PackedInteger Bits16 where
  bytewidth = 2
  getPacked = prim__getBits16
  setPacked = prim__setBits16

public export
PackedInteger Bits32 where
  bytewidth = 4
  getPacked = prim__getBits32
  setPacked = prim__setBits32

public export
PackedInteger Bits64 where
  bytewidth = 8
  getPacked = prim__getBits64
  setPacked = prim__setBits64

public export
PackedInteger Int8 where
  bytewidth = 1
  getPacked = prim__getInt8
  setPacked = prim__setInt8

public export
PackedInteger Int16 where
  bytewidth = 2
  getPacked = prim__getInt16
  setPacked = prim__setInt16

public export
PackedInteger Int32 where
  bytewidth = 4
  getPacked = prim__getInt32
  setPacked = prim__setInt32

public export
PackedInteger Int64 where
  bytewidth = 8
  getPacked = prim__getInt64
  setPacked = prim__setInt64

--------------------------------------------------------------------------------
-- PackedBuffer
--------------------------------------------------------------------------------

||| A mutable, packed buffer containing `n` values of type `a`.
|||
||| Values are stored consecutively in the underlying byte buffer using the
||| representation specified by the `PackedInteger a` implementation. The logical index
||| of an element is translated to a byte offset by multiplying it by
||| `bytewidth`.
public export
record PackedBuffer (s : Type) (n : Nat) (a : Type) where
  constructor MkPackedBuffer
  buffer : Buffer

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Allocate a mutable packed buffer containing `n` elements.
|||
||| The resulting buffer is represented using the linear state `s` and must
||| therefore be consumed within its enclosing linear scope.
|||
||| The underlying byte buffer contains exactly `n * bytewidth` bytes.
export %inline
mpackedbuffer1 : PackedInteger e => (n : Nat) -> F1 s (PackedBuffer s n e)
mpackedbuffer1 {e} n t =
  let MkIORes pb _ := prim__newBuf (cast $ n * bytewidth {a = e}) %MkWorld
   in MkPackedBuffer pb # t

||| Lift packed-buffer allocation into an arbitrary linear effect.
|||
||| This is the lifted form of `mpackedbuffer1`, allowing a packed buffer to be
||| allocated within any effect supporting `Lift1`.
export %inline
mpackedbuffer : PackedInteger e => Lift1 s f => (n : Nat) -> f (PackedBuffer s n e)
mpackedbuffer {e} n = lift1 (mpackedbuffer1 n {e})

--------------------------------------------------------------------------------
-- Allocation
--------------------------------------------------------------------------------

||| The scoped computation associated with a packed buffer.
|||
||| A `WithPackedBuffer n e a` computation receives a mutable packed buffer
||| containing `n` elements of type `e` and produces a value of type `a`.
public export
0 WithPackedBuffer : Nat -> Type -> Type -> Type
WithPackedBuffer n e a = forall s . (r : PackedBuffer s n e) -> F1 s a

||| Allocate a packed buffer for the duration of a scoped computation.
|||
||| The buffer contains `n` elements of type `e`.
export
alloc : PackedInteger e => (n : Nat) -> WithPackedBuffer n e a -> a
alloc {e} n f =
  run1 $ \t =>
    let r # t := mpackedbuffer1 n {e} t
     in f r t

--------------------------------------------------------------------------------
-- Access
--------------------------------------------------------------------------------

||| Read the element at the given logical index.
|||
||| The logical index is converted to a byte offset using the element's
||| `bytewidth`. Access is therefore performed directly against the underlying
||| byte buffer without boxing each stored value.
export %inline
get : PackedInteger a => PackedBuffer s n a -> Fin n -> F1 s a
get {a} (MkPackedBuffer buf) ix t =
  getPacked buf (cast $ finToNat ix * bytewidth {a}) # t

||| Write a value at the given logical index.
|||
||| The logical index is converted to a byte offset using the element's
||| `bytewidth`. The value is written directly into the underlying byte buffer
||| using the representation defined by the `PackedInteger` implementation.
export %inline
set : PackedInteger a => PackedBuffer s n a -> Fin n -> a -> F1' s
set {a} (MkPackedBuffer buf) ix value =
  ffi (setPacked buf (cast $ finToNat ix * bytewidth {a}) value)
