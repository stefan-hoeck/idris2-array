module Data.Buffer.Packed

import Data.Buffer
import Data.Buffer.Core
import Data.Linear.Ref1
import Data.Linear.Token

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (b o) (bytevector-s8-ref b o))"
prim__getInt8 : Buffer -> (offset : Integer) -> Int8

%foreign "scheme:(lambda (b o v) (bytevector-s8-set! b o v))"
prim__setInt8 : Buffer -> (offset : Integer) -> Int8 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-s16-ref b o 'little))"
prim__getInt16 : Buffer -> (offset : Integer) -> Int16

%foreign "scheme:(lambda (b o v) (bytevector-s16-set! b o v 'little))"
prim__setInt16 : Buffer -> (offset : Integer) -> Int16 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-s32-ref b o 'little))"
prim__getInt32 : Buffer -> (offset : Integer) -> Int32

%foreign "scheme:(lambda (b o v) (bytevector-s32-set! b o v 'little))"
prim__setInt32 : Buffer -> (offset : Integer) -> Int32 -> PrimIO ()

%foreign "scheme:(lambda (b o) (bytevector-s64-ref b o 'little))"
prim__getInt64 : Buffer -> (offset : Integer) -> Int64

%foreign "scheme:(lambda (b o v) (bytevector-s64-set! b o v 'little))"
prim__setInt64 : Buffer -> (offset : Integer) -> Int64 -> PrimIO ()

--------------------------------------------------------------------------------
-- PackedInt
--------------------------------------------------------------------------------

public export
interface PackedInt a where
  bytewidth : Nat
  getPacked : Buffer -> Integer -> a
  setPacked : Buffer -> Integer -> a -> PrimIO ()

public export
PackedInt Int8 where
  bytewidth = 1
  getPacked = prim__getInt8
  setPacked = prim__setInt8

public export
PackedInt Int16 where
  bytewidth = 2
  getPacked = prim__getInt16
  setPacked = prim__setInt16

public export
PackedInt Int32 where
  bytewidth = 4
  getPacked = prim__getInt32
  setPacked = prim__setInt32

public export
PackedInt Int64 where
  bytewidth = 8
  getPacked = prim__getInt64
  setPacked = prim__setInt64

--------------------------------------------------------------------------------
-- PackedBuffer
--------------------------------------------------------------------------------

public export
record PackedBuffer (s : Type) (n : Nat) (a : Type) where
  constructor MkPackedBuffer
  buffer : Buffer

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export %inline
mpackedbuffer1 : PackedInt e => (n : Nat) -> F1 s (PackedBuffer s n e)
mpackedbuffer1 {e} n t =
  let MkIORes pb _ := prim__newBuf (cast $ n * bytewidth {a = e}) %MkWorld
   in MkPackedBuffer pb # t

export %inline
mpackedbuffer : PackedInt e => Lift1 s f => (n : Nat) -> f (PackedBuffer s n e)
mpackedbuffer {e} n = lift1 (mpackedbuffer1 n {e})

--------------------------------------------------------------------------------
-- Allocation
--------------------------------------------------------------------------------

public export
0 WithPackedBuffer : Nat -> Type -> Type -> Type
WithPackedBuffer n e a = forall s . (r : PackedBuffer s n e) -> F1 s a

export
alloc : PackedInt e => (n : Nat) -> WithPackedBuffer n e a -> a
alloc {e} n f =
  run1 $ \t =>
    let r # t := mpackedbuffer1 n {e} t
     in f r t

--------------------------------------------------------------------------------
-- Access
--------------------------------------------------------------------------------

export %inline
get : PackedInt a => PackedBuffer s n a -> Fin n -> F1 s a
get {a} (MkPackedBuffer buf) ix t =
  getPacked buf (cast $ finToNat ix * bytewidth {a}) # t

export %inline
set : PackedInt a => PackedBuffer s n a -> Fin n -> a -> F1' s
set {a} (MkPackedBuffer buf) ix value =
  ffi (setPacked buf (cast $ finToNat ix * bytewidth {a}) value)
