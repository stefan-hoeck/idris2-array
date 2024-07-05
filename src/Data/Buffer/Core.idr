module Data.Buffer.Core

import Data.Buffer
import Data.Linear.Token
import Data.Array.Core
import public Data.Fin
import public Data.Nat

import System.File

%default total

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-buffer-getbyte"
         "node:lambda:(buf,offset)=>buf.readUInt8(Number(offset))"
         "browser:lambda:(buf,offset)=>buf[Number(offset)]"
prim__getByte : Buffer -> (offset : Integer) -> Bits8

%foreign "scheme:blodwen-buffer-setbyte"
         "node:lambda:(buf,offset,value,w)=>buf.writeUInt8(value, Number(offset))"
         "browser:lambda:(buf,offset,value,w)=>{buf[Number(offset)] = value;}"
prim__setByte : Buffer -> (offset : Integer) -> (val : Bits8) -> PrimIO ()

%foreign "scheme:blodwen-new-buffer"
         "node:lambda:s=>Buffer.alloc(s)"
         "browser:lambda:s=>new Uint8Array(s)"
prim__newBuf : Bits32 -> Buffer

%foreign "scheme:blodwen-buffer-getstring"
         "node:lambda:(buf,offset,len)=>buf.slice(Number(offset), Number(offset+len)).toString('utf-8')"
prim__getString : Buffer -> (offset,len : Integer) -> String

%foreign "scheme:blodwen-buffer-copydata"
         "node:lambda:(b1,o1,length,b2,o2)=>b1.copy(b2,Number(o2),Number(o1),Number(o1+length))"
prim__copy : (src : Buffer) -> (srcOffset, len : Integer) ->
             (dst : Buffer) -> (dstOffset : Integer) -> PrimIO ()

destroy : (1 _ : %World) -> (1 _ : a) -> a
destroy %MkWorld x = x

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
export
fromString : (s : String) -> IBuffer (cast $ stringByteLength s)
fromString s =
  let buf            := prim__newBuf (cast $ stringByteLength s)
      MkIORes () w2  := toPrim (setString buf 0 s) %MkWorld
   in destroy w2 (IB buf)

||| Convert a section of a byte array to an UTF-8 string.
||| TODO: Test from/to String
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

||| Wrappes a bare mutable buffer in an `IBuffer`.
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
record MBuffer (n : Nat) where
  constructor MB
  buf : Buffer

public export
0 WithMBuffer : Nat -> (a : Type) -> Type
WithMBuffer n a = (s : MBuffer n) => (1 t : T1 s) -> Ur a

||| Allocate and release a mutable byte array in a linear context.
|||
||| Function `fun` must use the given array exactly once, while
||| its result must be wrapped in a `Ur`, guaranteeing, that the
||| mutable array will never be used outside of `fun`, especially
||| that the result `b` does not hold a reference to the mutable
||| array.
export
alloc : (n : Nat) -> (1 fun : WithMBuffer n a) -> Ur a
alloc n f = f @{MB $ prim__newBuf (cast n)} (MkT1 %MkWorld)

export
copy :
     IBuffer m
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> {auto s : MBuffer n}
  -> F1' s
copy (IB src) srcOffset dstOffset len (MkT1 w) =
  let MB dst        := s
      MkIORes () w2 :=
        prim__copy src (cast srcOffset) (cast len) dst (cast dstOffset) w
   in MkT1 w2

||| Copy the content of an immutable buffer to a new buffer.
export
thaw : {n : _} -> IBuffer n -> (1 fun : WithMBuffer n b) -> Ur b
thaw src f =
  alloc n $ \b =>
    let b2 := copy src 0 0 n @{reflexive} @{reflexive} b
     in f b2

||| Safely write a value to a mutable byte array.
|||
||| Since the array must be used exactly once, a "new" array (the
||| same array wrapped in a new `MB`) must be returned, which will
||| then again be used exactly once.
export
set : (s : MBuffer n) => Fin n -> Bits8 -> F1' s
set @{MB buf} o x (MkT1 w) =
  let MkIORes () w2 := Core.prim__setByte buf (cast $ finToNat o) x w
   in MkT1 w2

||| Safely read a value from a mutable byte array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new `MBuffer` of quantity one to be further used in the
||| linear context. See implementation notes on `set` about some details,
||| how this works.
export
get : (s : MBuffer n) => Fin n -> F1 s Bits8
get @{MB buf} m t = prim__getByte buf (cast $ finToNat m) # t

||| Safely modify a value in a mutable byte array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this returns a new `MBuffer` wrapper, which must then
||| again be used exactly once.
export
modify : (s : MBuffer n) => Fin n -> (Bits8 -> Bits8) -> F1' s
modify m f t =
  let v # t2 := Buffer.Core.get m t
   in set m (f v) t2

||| Wrap a mutable byte array in an `IBuffer`, which can then be freely shared.
|||
||| It is not possible the extract and share the underlying `ArrayData`
||| wrapped in an `IBuffer`, so we don't have to be afraid of shared mutable
||| state: The interface of `IBuffer` does not support to further mutate
||| the wrapped array.
|||
||| It is safe to only use a prefix of a properly constructed array,
||| therefore we are free to give the resulting array a smaller size.
||| Most of the time, we'd like to use the whole array, in which case
||| we can just use `freeze`.
export
freezeLTE : (0 m : Nat) -> (0 _ : LTE m n) => WithMBuffer n (IBuffer m)
freezeLTE _ @{_} @{MB buf} t = unsafeDiscard t $ MkBang $ IB buf

||| Wrap a mutable byte array in an `IBuffer`, which can then be freely shared.
|||
||| See `freezeLTE` for some additional notes about how this works under
||| the hood.
export %inline
freeze : WithMBuffer n (IBuffer n)
freeze = freezeLTE n @{reflexive}

export %inline
discard : (s : MBuffer n) => T1 s -@ ()
discard t = unsafeDiscard t ()

||| Safely discard a linear mutable array, returning a non-linear
||| result at the same time.
export %inline
discarding : (s : MBuffer n) => (1 t : T1 s) -> x -> x
discarding t x = unsafeDiscard t x

||| Release a mutable linear buffer to `IO`, thus making it freely
||| shareable.
export %inline
toIO : WithMBuffer n (IO Buffer)
toIO @{MB buf} t = unsafeDiscard t (MkBang $ pure buf)

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
  -> MBuffer n
  -@ Ur (io (Either (FileError,Int) ()))
writeMBuffer h o s (MB buf) =
  MkBang $ writeBufferData h buf (cast o) (cast s)
