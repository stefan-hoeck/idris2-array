module Data.Buffer.Core

import Data.Buffer
import Data.Linear.Token
import public Data.Fin
import public Data.Nat

import System.File

%default total

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

export
%foreign "scheme:(lambda (b o) (bytevector-u8-ref b o))"
         "javascript:lambda:(buf,offset)=>buf[offset]"
prim__getByte : Buffer -> (offset : Bits32) -> Bits8

export
%foreign "scheme:(lambda (b o v) (bytevector-u8-set! b o v))"
         "javascript:lambda:(buf,offset,value,t)=>{buf[offset] = value; return t}"
prim__setByte : Buffer -> (offset : Bits32) -> (val : Bits8) -> PrimIO ()

export
%foreign "scheme:(lambda (n) (make-bytevector n 0))"
         "javascript:lambda:s=>new Uint8Array(s)"
prim__newBuf : Bits32 -> Buffer

export
%foreign "scheme:blodwen-buffer-getstring"
         "javascript:lambda:(buf,offset,len)=> new TextDecoder().decode(buf.subarray(offset, offset+len))"
prim__getString : Buffer -> (offset,len : Bits32) -> String

export
%foreign "scheme:(lambda (v) (string->utf8 v))"
         "javascript:lambda:(v)=> new TextEncoder().encode(v)"
prim__fromString : (val : String) -> Buffer

export
%foreign "scheme:(lambda (b1 o1 len b2 o2) (bytevector-copy! b1 o1 b2 o2 len))"
         "javascript:lambda:(b1,o1,len,b2,o2,t)=> {for (let i = 0; i < len; i++) {b2[o2+i] = b1[o1+i];}; return t}"
prim__copy : (src : Buffer) -> (srcOffset, len : Bits32) ->
             (dst : Buffer) -> (dstOffset : Bits32) -> PrimIO ()

--------------------------------------------------------------------------------
--          Immutable Buffers
--------------------------------------------------------------------------------

||| An immutable byte array of size `n`.
export
record IBuffer (n : Nat) where
  constructor IB
  buf : Buffer

||| Safely access a value in an byte array at the given position.
export %inline
at : IBuffer n -> Fin n -> Bits8
at (IB buf) m = prim__getByte buf (cast $ finToNat m)

||| We can wrap a prefix of a byte array in O(1) simply by giving it
||| a new size index.
|||
||| Note: If you only need a small portion of a potentially large
|||       byte array the rest of which you no longer need, consider to
|||       releasing the large byte array from memory by invoking `force`.
export
take : (0 m : Nat) -> IBuffer n -> {auto 0 lte : LTE m n} -> IBuffer m
take _ (IB buf) = IB buf

||| Convert an UTF-8 string to a buffer
export %noinline
fromString : (s : String) -> IBuffer (cast $ stringByteLength s)
fromString s = IB (prim__fromString s)

||| Convert a section of a byte array to an UTF-8 string.
export
toString : IBuffer n -> (off,len : Nat) -> (0 _ : LTE (off + len) n) => String
toString (IB buf) off len = prim__getString buf (cast off) (cast len)

||| Extracts the inner buffer held by a byte array without copying.
|||
||| This allows us to write efficiently write the data to a file
||| without copying it first. This is a highly unsafe operation,
||| and client code must make sure never ever to mutate the buffer!
export
unsafeGetBuffer : IBuffer n -> Buffer
unsafeGetBuffer (IB buf) = buf

||| Wrapps a bare mutable buffer in an `IBuffer`.
|||
||| Client code is responsible to make sure the original buffer is no longer
||| used.
export
unsafeMakeBuffer : Buffer -> IBuffer k
unsafeMakeBuffer = IB

--------------------------------------------------------------------------------
--          Mutable Byte Arrays
--------------------------------------------------------------------------------

||| A mutable byte array.
export
data MBuffer : (n : Nat) -> Type where
  MB : (buf : Buffer) -> MBuffer n

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Fills a new mutable bound to linear computation `s`.
export %inline
newMBuffer : (n : Nat) -> (1 t : T1 rs) -> A1 rs (MBuffer n)
newMBuffer n t = A (MB (prim__newBuf (cast n))) (unsafeBind t)

||| Safely write a value to a mutable byte vector.
export %inline
set : (r : MBuffer n) -> (0 p : Res r rs) => Fin n -> Bits8 -> F1' rs
set (MB buf) ix v = ffi (prim__setByte buf (cast $ finToNat ix) v)

||| Safely read a value from a mutable byte array.
export %inline
get : (r : MBuffer n) -> (0 p : Res r rs) => Fin n -> F1 rs Bits8
get (MB buf) ix t = prim__getByte buf (cast $ finToNat ix) # t

||| Safely modify a value in a mutable byte array.
export
modify :
     (r : MBuffer n)
  -> {auto 0 p : Res r rs}
  -> Fin n
  -> (Bits8 -> Bits8)
  -> F1' rs
modify r m f t = let v # t := get r m t in set r m (f v) t

||| Release a byte array.
|||
||| Afterwards, it can no longer be use with the given linear token.
export %inline
release : (0 r : MBuffer n) -> (0 p : Res r rs) => C1' rs (Drop rs p)
release _ = unsafeRelease p

--------------------------------------------------------------------------------
-- Allocating Byte Vectors
--------------------------------------------------------------------------------

public export
0 WithMBuffer : Nat -> (a : Type) -> Type
WithMBuffer n a = (r : MBuffer n) -> F1 [r] a

public export
0 FromMBuffer : Nat -> (a : Type) -> Type
FromMBuffer n a = (r : MBuffer n) -> C1 [r] [] a

||| Allocate and potentially freeze a mutable byte array in a linear context.
|||
||| Note: In case you don't need to freeze the array in the end, using `alloc`
|||       might be more convenient.
export
create : (n : Nat) -> (fun : FromMBuffer n a) -> a
create n f = run1 $ \t => let A r t := newMBuffer n t in f r t

||| Allocate, use, and release a mutable byte array in a linear computation.
|||
||| Note: In case you want to freeze the buffer and return it in the
|||       result, use `create`.
export
alloc : (n : Nat) -> (fun : WithMBuffer n a) -> a
alloc n f =
  create n $ \r,t =>
    let v # t := f r t
        _ # t := release r t
     in v # t

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export %noinline
copy :
     IBuffer m
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MBuffer n)
  -> {auto 0 p  : Res r rs}
  -> F1' rs
copy (IB src) srcOffset dstOffset len (MB dst) =
  ffi (prim__copy src (cast srcOffset) (cast len) dst (cast dstOffset))

||| Copy the content of an immutable buffer to a new buffer.
export
thaw : {n : _} -> IBuffer n -> (fun : FromMBuffer n b) -> b
thaw src f =
  create n $ \r,t =>
    let _ # t := copy src 0 0 n @{reflexive} @{reflexive} r t
     in f r t

||| Wrap a mutable buffer in an `IBuffer` without copying.
|||
||| In order to make this safe, the associated linear token has to
||| be discarded.
|||
||| It is safe to only use a prefix of a properly constructed array,
||| therefore we are free to give the resulting array a smaller size.
||| Most of the time, we'd like to use the whole buffer, in which case
||| we can just use `freezeBufAt`.
export %inline
freezeLTE :
     {auto 0 _ : LTE m n}
  -> (r        : MBuffer n)
  -> {auto 0 p : Res r rs}
  -> (0 m : Nat)
  -> (1 t : T1 rs)
  -> R1 (Drop rs p) (IBuffer m)
freezeLTE (MB buf) _ t = let _ # t := unsafeRelease p t in IB buf # t

export %inline
freeze :
     (r : MBuffer n)
  -> {auto 0 p : Res r rs}
  -> (1 t : T1 rs)
  -> R1 (Drop rs p) (IBuffer n)
freeze r = freezeLTE @{reflexive} r n

||| Release a mutable linear buffer to `IO`, thus making it freely
||| shareable.
export %inline
toIO :
     (r : MBuffer n)
  -> {auto 0 p : Res r rs}
  -> (1 t : T1 rs)
  -> R1 (Drop rs p) (IO Buffer)
toIO (MB buf) t = let _ # t := unsafeRelease p t in pure buf # t

--------------------------------------------------------------------------------
--          Reading and Writing Files
--------------------------------------------------------------------------------

||| Read up to `n` bytes from a file into an immutable buffer.
export
readIBuffer :
     {auto has : HasIO io}
  -> Nat
  -> File
  -> io (Either FileError (n ** IBuffer n))
readIBuffer max f =
  let buf  := prim__newBuf (cast max)
   in do
    Right r <- readBufferData f buf 0 (cast max) | Left x => pure (Left x)
    if r >= 0
       then pure (Right (cast r ** IB buf))
       else pure (Left FileReadError)

||| Write up to `len` bytes from a buffer to a file, starting
||| at the given offset.
export
writeIBuffer :
     {auto has : HasIO io}
  -> File
  -> (offset,len : Nat)
  -> IBuffer n
  -> {auto 0 prf : LTE (offset + len) n}
  -> io (Either (FileError,Int) ())
writeIBuffer h o s (IB buf) = writeBufferData h buf (cast o) (cast s)

||| Write up to `len` bytes from a buffer to a file, starting
||| at the given offset.
export
writeMBuffer :
     {auto has : HasIO io}
  -> File
  -> (offset,len : Nat)
  -> {auto 0 prf : LTE (offset + len) n}
  -> (r : MBuffer n)
  -> {auto 0 p : Res r rs}
  -> T1 rs
  -> R1 (Drop rs p) (io (Either (FileError,Int) ()))
writeMBuffer h o s (MB b) t =
  let _ # t := unsafeRelease p t in writeBufferData h b (cast o) (cast s) # t
