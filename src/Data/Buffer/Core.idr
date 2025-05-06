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
         "javascript:lambda:(buf,offset)=>buf[Number(offset)]"
prim__getByte : Buffer -> (offset : Integer) -> Bits8

||| This is an optimized version of `getByte` that allows us to read
||| at an offset. On Chez, we can use the faster fixnum addition here,
||| which can lead to a performance boost.
export
%foreign "scheme:(lambda (b a o) (bytevector-u8-ref b (+ a o)))"
         "scheme,chez:(lambda (b a o) (bytevector-u8-ref b (fx+ a o)))"
         "javascript:lambda:(buf,at,offset)=>buf[Number(offset) + Number(at)]"
prim__getByteOffset : Buffer -> (at, offset : Integer) -> Bits8

export
%foreign "scheme:(lambda (b o v) (bytevector-u8-set! b o v))"
         "javascript:lambda:(buf,offset,value,t)=>{buf[Number(offset)] = value; return t}"
prim__setByte : Buffer -> (offset : Integer) -> (val : Bits8) -> PrimIO ()

export
%foreign "scheme:(lambda (n) (make-bytevector n 0))"
         "javascript:lambda:(s,w)=>new Uint8Array(Number(s))"
prim__newBuf : Integer -> PrimIO Buffer

export
%foreign "scheme:blodwen-buffer-getstring"
         "javascript:lambda:(buf,offset,len)=> new TextDecoder().decode(buf.subarray(Number(offset), Number(offset+len)))"
prim__getString : Buffer -> (offset,len : Integer) -> String

export
%foreign "scheme:(lambda (v) (string->utf8 v))"
         "javascript:lambda:(v)=> new TextEncoder().encode(v)"
prim__fromString : (val : String) -> Buffer

export
%foreign "scheme:(lambda (b1 o1 len b2 o2) (bytevector-copy! b1 o1 b2 o2 len))"
         "javascript:lambda:(b1,bo1,blen,b2,bo2,t)=> {const o1 = Number(bo1); const len = Number(blen); const o2 = Number(bo2); for (let i = 0; i < len; i++) {b2[o2+i] = b1[o1+i];}; return t}"
prim__copy : (src : Buffer) -> (srcOffset, len : Integer) ->
             (dst : Buffer) -> (dstOffset : Integer) -> PrimIO ()

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

||| Safely access a value in an immutable byte array at the given position
||| and offset.
export %inline
atOffset : IBuffer n -> Fin m -> (off : Nat) -> (0 p : LTE (off+m) n) => Bits8
atOffset (IB buf) m off =
  prim__getByteOffset buf (cast $ finToNat m) (cast off)

||| We can wrap a prefix of an immutable byte array in O(1) simply by giving it
||| a new size index.
|||
||| Note: If you only need a small portion of a potentially large
|||       byte array the rest of which you no longer need, consider to
|||       releasing the large byte array from memory by invoking `force`.
export
take : (0 m : Nat) -> IBuffer n -> {auto 0 lte : LTE m n} -> IBuffer m
take _ (IB buf) = IB buf

||| Convert an UTF-8 string to an immutable byte array.
export %noinline
fromString : (s : String) -> IBuffer (cast $ stringByteLength s)
fromString s = IB (prim__fromString s)

||| Convert a section of an immutable byte array to an UTF-8 string.
export
toString : IBuffer n -> (off,len : Nat) -> (0 _ : LTE (off + len) n) => String
toString (IB buf) off len = prim__getString buf (cast off) (cast len)

||| Extracts the inner buffer held by an immutable byte array without copying.
|||
||| This allows us to write efficiently write the data to a file
||| without copying it first. This is a highly unsafe operation,
||| and client code must make sure never ever to mutate the buffer!
export
unsafeGetBuffer : IBuffer n -> Buffer
unsafeGetBuffer (IB buf) = buf

||| Wraps a bare mutable buffer in an `IBuffer`.
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
data MBuffer : (s : Type) -> (n : Nat) -> Type where
  MB : (buf : Buffer) -> MBuffer s n

||| Convenience alias for `MBuffer' RIO`
public export
0 IOBuffer : Nat -> Type
IOBuffer = MBuffer World

||| Wraps a `Buffer` in an `IOBuffer`. Use at your own risk.
export %inline
unsafeMBuffer : Buffer -> MBuffer s n
unsafeMBuffer = MB

||| Extracts the `Buffer` from an `MBuffer`. Use at your own risk.
export %inline
unsafeFromMBuffer : MBuffer s n -> Buffer
unsafeFromMBuffer (MB buf) = buf

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Creates a new mutable byte array bound to linear computation `s`.
export %inline
mbuffer1 : (n : Nat) -> F1 s (MBuffer s n)
mbuffer1 n t =
  let MkIORes b _ := prim__newBuf (cast n) %MkWorld
   in MB b # t

||| Creates a new mutable byte array in `IO`.
export %inline
mbuffer : Lift1 s f => (n : Nat) -> f (MBuffer s n)
mbuffer n = lift1 (mbuffer1 n)

||| Safely write a value to a mutable byte array.
export %inline
set : (r : MBuffer s n) -> Fin n -> Bits8 -> F1' s
set (MB buf) ix v = ffi (prim__setByte buf (cast $ finToNat ix) v)

||| Safely read a value from a mutable byte array.
export %inline
get : (r : MBuffer s n) -> Fin n -> F1 s Bits8
get (MB buf) ix t = prim__getByte buf (cast $ finToNat ix) # t

||| Safely modify a value in a mutable byte array.
export
modify : (r : MBuffer s n) -> Fin n -> (Bits8 -> Bits8) -> F1' s
modify r m f t = let v # t := get r m t in set r m (f v) t

||| Extracts a string from a (possibly partially) filled mutable byte array.
export %inline
bufString : (r : MBuffer s n) -> (m : Nat) -> (0 lte : LTE m n) => F1 s String
bufString (MB buf) m t = prim__getString buf 0 (cast m) # t

||| Wraps a mutable byte array in a shorter one.
export %inline
mtake : MBuffer s n -> (0 m : Nat) -> (0 lte : LTE m n) => F1 s (MBuffer s m)
mtake (MB buf) _ t = MB buf # t

--------------------------------------------------------------------------------
-- Allocating Byte Vectors
--------------------------------------------------------------------------------

public export
0 WithMBuffer : Nat -> (a : Type) -> Type
WithMBuffer n a = forall s . (r : MBuffer s n) -> F1 s a

||| Allocate and potentially freeze a mutable byte array in a linear context.
export
alloc : (n : Nat) -> (fun : WithMBuffer n a) -> a
alloc n f = run1 $ \t => let r # t := mbuffer1 n t in f r t

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export %noinline
copy :
     MBuffer s m
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MBuffer s n)
  -> F1' s
copy (MB src) srcOffset dstOffset len (MB dst) =
  ffi (prim__copy src (cast srcOffset) (cast len) dst (cast dstOffset))

export %inline
icopy :
     IBuffer m
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MBuffer s n)
  -> F1' s
icopy (IB src) = copy {m} (MB src)

||| Copy the content of an immutable byte array to a new byte array.
export
thaw : {n : _} -> IBuffer n -> F1 s (MBuffer s n)
thaw src t =
    let r # t := mbuffer1 n t
        _ # t := icopy src 0 0 n @{reflexive} @{reflexive} r t
     in r # t

||| Wrap a mutable byte array in an immutable byte array without copying.
|||
||| In order to make this safe, the associated linear token has to
||| be discarded.
|||
||| It is safe to only use a prefix of a properly constructed array,
||| therefore we are free to give the resulting array a smaller size.
||| Most of the time, we'd like to use the whole buffer, in which case
||| we can just use `freezeBufAt`.
|||
||| Note: For reasons of efficiency, this does not copy the buffer,
|||       and therefore, it must no longer be modified after calling
|||       this function.
export %inline
unsafeFreezeLTE :
     MBuffer s n
  -> (0 m : Nat)
  -> {auto 0 _ : LTE m n}
  -> F1 s (IBuffer m)
unsafeFreezeLTE (MB buf) _ t = IB buf # t

||| Convenience alias for `unsafeFreezeLTE @{reflexive}`
export %inline
unsafeFreeze : (r : MBuffer s n) -> F1 s (IBuffer n)
unsafeFreeze r = unsafeFreezeLTE @{reflexive} r n

||| Copy a prefix of a mutable byte arrya into an immutable byte array.
export
freezeLTE : MBuffer s n -> (m : Nat) -> (0 p : LTE m n) => F1 s (IBuffer m)
freezeLTE src m t =
  let r@(MB buf) # t := mbuffer1 m t
      _          # t := copy src 0 0 m @{p} @{reflexive} r t
   in IB buf     # t

||| Copy a mutable byte array into an immutable byte array.
export %inline
freeze : {n : _} -> MBuffer s n -> F1 s (IBuffer n)
freeze src = freezeLTE src n @{reflexive}

--------------------------------------------------------------------------------
--          Reading and Writing Files
--------------------------------------------------------------------------------

||| Read up to `n` bytes from a file into an immutable byte array.
export
readIBuffer :
     {auto has : HasIO io}
  -> Nat
  -> File
  -> io (Either FileError (n ** IBuffer n))
readIBuffer max f = do
  buf <- primIO (prim__newBuf (cast max))
  Right r <- readBufferData f buf 0 (cast max) | Left x => pure (Left x)
  if r >= 0
     then pure (Right (cast r ** IB buf))
     else pure (Left FileReadError)

||| Write up to `len` bytes from an immutable byte array to a file, starting
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

||| Write up to `len` bytes from a mutable byte array to a file, starting
||| at the given offset.
export
writeMBuffer :
     {auto has : HasIO io}
  -> File
  -> (offset,len : Nat)
  -> {auto 0 prf : LTE (offset + len) n}
  -> (r : MBuffer s n)
  -> io (Either (FileError,Int) ())
writeMBuffer h o s (MB b) =
  writeBufferData h b (cast o) (cast s)
