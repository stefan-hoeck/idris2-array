module Data.Buffer.Builder

import Data.Array.Index
import Data.Buffer
import Data.String
import Syntax.T1
import Data.Buffer.Indexed

import public Data.Buffer.Core
import public Data.Linear.Token

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (n) (cons (make-bytevector (max n 32) 0) 0))"
         "javascript:lambda:(sz,w)=> {const buf = new ArrayBuffer(sz); return {buffer:buf, view: new DataView(buf), pos: 0};}"
prim__builder : Bits32 -> PrimIO AnyPtr

%foreign "scheme:(lambda (n b) (let ((sz (bytevector-length (car b))) (tgt (+ n (cdr b)))) (if (> tgt sz) (let ((bv (make-bytevector (+ sz (max sz n)) 0))) (bytevector-copy! (car b) 0 bv 0 (cdr b)) (set-car! b bv)))))"
         "javascript:lambda:(n,b,w) => {const tgt = n + b.pos; const sz  = b.buffer.byteLength; if (tgt > sz) {const newSize = Math.max(2 * sz, tgt); const newBuffer = new ArrayBuffer(newSize); new Uint8Array(newBuffer).set(new Uint8Array(b.buffer)); b.buffer = newBuffer; b.view = new DataView(newBuffer);}}"
prim__checksize : Bits32 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (off sz buf b) (bytevector-copy! buf off (car b) (cdr b) sz) (set-cdr! b (+ sz (cdr b))))"
         "javascript:lambda:(o,len,buf,b,t)=> {new Uint8Array(b.buffer).set(buf.slice(o,o+len), b.pos); b.pos += len;}"
prim__putbytes : (offset, len : Bits32) -> Buffer -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-u8-set! (car b) (cdr b) v) (set-cdr! b (+ 1 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setUint8(b.pos, n); b.pos += 1;}"
prim__putbits8 : Bits8 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-u16-set! (car b) (cdr b) v 'little) (set-cdr! b (+ 2 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setUint16(b.pos, n, true); b.pos += 2;}"
prim__putbits16le : Bits16 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-u16-set! (car b) (cdr b) v 'big) (set-cdr! b (+ 2 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setUint16(b.pos, n, false); b.pos += 2;}"
prim__putbits16be : Bits16 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-u32-set! (car b) (cdr b) v 'little) (set-cdr! b (+ 4 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setUint32(b.pos, n, true); b.pos += 4;}"
prim__putbits32le : Bits32 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-u32-set! (car b) (cdr b) v 'big) (set-cdr! b (+ 4 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setUint32(b.pos, n, false); b.pos += 4;}"
prim__putbits32be : Bits32 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-u64-set! (car b) (cdr b) v 'little) (set-cdr! b (+ 8 (cdr b))))"
         "javascript:lambda:(n,b,w) => {const nx = Number(n & 0xffffffffn); const ny = Number((n >> 32n) & 0xffffffffn); b.view.setUint32(b.pos, nx, true); b.pos += 4; b.view.setUint32(b.pos, ny, true); b.pos += 4;}"
prim__putbits64le : Bits64 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-u64-set! (car b) (cdr b) v 'big) (set-cdr! b (+ 8 (cdr b))))"
         "javascript:lambda:(n,b,w) => {const nx = Number(n & 0xffffffffn); const ny = Number((n >> 32n) & 0xffffffffn); b.view.setUint32(b.pos, ny, false); b.pos += 4; b.view.setUint32(b.pos, nx, false); b.pos += 4;}"
prim__putbits64be : Bits64 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-s8-set! (car b) (cdr b) v) (set-cdr! b (+ 1 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setInt8(b.pos, n); b.pos += 1;}"
prim__putint8 : Int8 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-s16-set! (car b) (cdr b) v 'little) (set-cdr! b (+ 2 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setInt16(b.pos, n, true); b.pos += 2;}"
prim__putint16le : Int16 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-s16-set! (car b) (cdr b) v 'big) (set-cdr! b (+ 2 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setInt16(b.pos, n, false); b.pos += 2;}"
prim__putint16be : Int16 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-s32-set! (car b) (cdr b) v 'little) (set-cdr! b (+ 4 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setInt32(b.pos, n, true); b.pos += 4;}"
prim__putint32le : Int32 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-s32-set! (car b) (cdr b) v 'big) (set-cdr! b (+ 4 (cdr b))))"
         "javascript:lambda:(n,b,w) => {b.view.setInt32(b.pos, n, false); b.pos += 4;}"
prim__putint32be : Int32 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-s64-set! (car b) (cdr b) v 'little) (set-cdr! b (+ 8 (cdr b))))"
         "javascript:lambda:(x,b,w) => {const n = BigInt.asUintN(64,x); const nx = Number(n & 0xffffffffn); const ny = Number((n >> 32n) & 0xffffffffn); b.view.setUint32(b.pos, nx, true); b.pos += 4; b.view.setUint32(b.pos, ny, true); b.pos += 4;}"
prim__putint64le : Int64 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (v b) (bytevector-s64-set! (car b) (cdr b) v 'big) (set-cdr! b (+ 8 (cdr b))))"
         "javascript:lambda:(x,b,w) => {const n = BigInt.asUintN(64,x); const nx = Number(n & 0xffffffffn); const ny = Number((n >> 32n) & 0xffffffffn); b.view.setUint32(b.pos, ny, false); b.pos += 4; b.view.setUint32(b.pos, nx, false); b.pos += 4;}"
prim__putint64be : Int64 -> AnyPtr -> PrimIO ()

%foreign "scheme:(lambda (b) (cdr b))"
         "javascript:lambda:(b,w) => b.pos"
prim__buildersize : AnyPtr -> PrimIO Bits32

%foreign "scheme:(lambda (b) (let ((bv (make-bytevector (cdr b) 0))) (bytevector-copy! (car b) 0 bv 0 (cdr b)) (set-cdr! b 0) bv))"
         "javascript:lambda:(b,w) => {const res = new Uint8Array(b.buffer.slice(0, b.pos)); b.pos = 0; return res;}"
prim__builderbytes : AnyPtr -> PrimIO Buffer

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
record Builder q where
  [noHints]
  constructor B
  ptr : AnyPtr

export
builder : {default 128 size : Bits32} -> F1 q (Builder q)
builder t = let p # t := ffi (prim__builder size) t in B p # t

export %inline
withBuilder :
     {default 128 size : Bits32}
  -> (run : forall q . Builder q => F1 q a)
  -> a
withBuilder run =
  run1 $ \t => let b # t := builder t in run @{b} t

parameters {auto b : Builder q}

  %inline
  checksize : Bits32 -> F1' q
  checksize n = ffi $ prim__checksize n b.ptr

  export
  putBits8 : Bits8 -> F1' q
  putBits8 v t = let _ # t := checksize 1 t in ffi (prim__putbits8 v b.ptr) t

  export
  putBits16LE : Bits16 -> F1' q
  putBits16LE v t = let _ # t := checksize 2 t in ffi (prim__putbits16le v b.ptr) t

  export
  putBits16BE : Bits16 -> F1' q
  putBits16BE v t = let _ # t := checksize 2 t in ffi (prim__putbits16be v b.ptr) t

  export
  putBits32LE : Bits32 -> F1' q
  putBits32LE v t = let _ # t := checksize 4 t in ffi (prim__putbits32le v b.ptr) t

  export
  putBits32BE : Bits32 -> F1' q
  putBits32BE v t = let _ # t := checksize 4 t in ffi (prim__putbits32be v b.ptr) t

  export
  putBits64LE : Bits64 -> F1' q
  putBits64LE v t = let _ # t := checksize 8 t in ffi (prim__putbits64le v b.ptr) t

  export
  putBits64BE : Bits64 -> F1' q
  putBits64BE v t = let _ # t := checksize 8 t in ffi (prim__putbits64be v b.ptr) t

  export
  putInt8 : Int8 -> F1' q
  putInt8 v t = let _ # t := checksize 1 t in ffi (prim__putint8 v b.ptr) t

  export
  putInt16LE : Int16 -> F1' q
  putInt16LE v t = let _ # t := checksize 2 t in ffi (prim__putint16le v b.ptr) t

  export
  putInt16BE : Int16 -> F1' q
  putInt16BE v t = let _ # t := checksize 2 t in ffi (prim__putint16be v b.ptr) t

  export
  putInt32LE : Int32 -> F1' q
  putInt32LE v t = let _ # t := checksize 4 t in ffi (prim__putint32le v b.ptr) t

  export
  putInt32BE : Int32 -> F1' q
  putInt32BE v t = let _ # t := checksize 4 t in ffi (prim__putint32be v b.ptr) t

  export
  putInt64LE : Int64 -> F1' q
  putInt64LE v t = let _ # t := checksize 8 t in ffi (prim__putint64le v b.ptr) t

  export
  putInt64BE : Int64 -> F1' q
  putInt64BE v t = let _ # t := checksize 8 t in ffi (prim__putint64be v b.ptr) t

  export
  putBytesFrom :
       (offset, len : Nat)
    -> IBuffer n
    -> {auto 0 lte : LTE (offset+len) n}
    -> F1' q
  putBytesFrom offset len buf t =
   let sz    := cast len
       _ # t := checksize sz t
    in ffi (prim__putbytes (cast offset) sz (unsafeGetBuffer buf) b.ptr) t

  export
  putBytes : {n : _} -> IBuffer n -> F1' q
  putBytes buf t =
   let sz    := cast n
       _ # t := checksize sz t
    in ffi (prim__putbytes 0 sz (unsafeGetBuffer buf) b.ptr) t

  export %inline
  putAnyBytes : AnyBuffer -> F1' q
  putAnyBytes (AB _ ib) = putBytes ib

  export %inline
  putString : String -> F1' q
  putString s = putBytes (fromString s)

  export %inline
  putChar : Char -> F1' q
  putChar = putString . singleton

  export
  putMBytes : {n : _} -> MBuffer q n -> F1' q
  putMBytes m t = let ib # t := unsafeFreeze m t in putBytes ib t

  export
  getBytes : F1 q AnyBuffer
  getBytes t =
    let sz # t := ffi (prim__buildersize b.ptr) t
        buf # t := ffi (prim__builderbytes b.ptr) t
     in AB (cast sz) (unsafeMakeBuffer buf) # t

  export
  getString : F1 q String
  getString t = let ab # t := getBytes t in cast ab # t

export
fastConcat : List AnyBuffer -> AnyBuffer
fastConcat bs = withBuilder (go bs)
  where
    go : Builder q => List AnyBuffer -> F1 q AnyBuffer
    go []        t = getBytes t
    go (x :: xs) t = let _ # t := putAnyBytes x t in go xs t
