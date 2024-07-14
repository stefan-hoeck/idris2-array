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
data MBuffer : (tag : k) -> (s : Type) -> (n : Nat) -> Type where
  [search tag s]
  MB : (buf : Buffer) -> MBuffer tag s n

--------------------------------------------------------------------------------
-- Tagged utilities
--------------------------------------------------------------------------------

||| Fills a new mutable bound to linear computation `s`.
export %inline
newMBufferAt : (0 tag : _) -> (n : Nat) -> F1 s (MBuffer tag s n)
newMBufferAt tag n t = MB (prim__newBuf (cast n)) # t

||| Safely write a value to a mutable byte vector.
export
setAt : (0 tag : _) -> MBuffer tag s n => Fin n -> Bits8 -> F1' s
setAt tag @{MB buf} ix v t =
  let MkIORes () w2 := prim__setByte buf (cast $ finToNat ix) v %MkWorld
   in t

||| Safely read a value from a mutable byte array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new `MBuffer` of quantity one to be further used in the
||| linear context. See implementation notes on `set` about some details,
||| how this works.
export %inline
getAt : (0 tag : _) -> MBuffer tag s n => Fin n -> F1 s Bits8
getAt tag @{MB buf} ix t = prim__getByte buf (cast $ finToNat ix) # t

||| Safely modify a value in a mutable byte array.
export
modifyAt : (0 tag : _) -> MBuffer tag s n => Fin n -> (Bits8 -> Bits8) -> F1' s
modifyAt tag m f t =
  let v # t2 := Core.getAt tag m t
   in setAt tag m (f v) t2

--------------------------------------------------------------------------------
-- Untagged utilities
--------------------------------------------------------------------------------

||| Untagged version of `newMBufferAt`
export %inline
newMBuffer : (n : Nat) -> F1 s (MBuffer () s n)
newMBuffer = newMBufferAt ()

||| Untagged version of `setAt`.
export %inline
set : MBuffer () s n => Fin n -> Bits8 -> F1' s
set = setAt ()

||| Untagged version of `getAt`
export %inline
get : MBuffer () s n => Fin n -> F1 s Bits8
get = getAt ()

||| Untagged version of `modifyAt`
export
modify : MBuffer () s n => Fin n -> (Bits8 -> Bits8) -> F1' s
modify = modifyAt ()

--------------------------------------------------------------------------------
-- Allocating Byte Vectors
--------------------------------------------------------------------------------

public export
0 WithMBuffer : Nat -> (a : Type) -> Type
WithMBuffer n a = forall s . MBuffer () s n => F1 s a

public export
0 WithMBufferUr : Nat -> (a : Type) -> Type
WithMBufferUr n a = forall s . MBuffer () s n => (1 t : T1 s) -> Ur a

||| Allocate a mutable byte vector in a linear context.
|||
||| Note: In case you want to freeze the array and return it in the
||| result, use `allocUr`.
export
alloc : (n : Nat) -> (fun : WithMBuffer n a) -> a
alloc n f =
  run1 $ \t => let buf # t2 := newMBuffer n t in f @{buf} t2

||| Allocate and potentially freeze a mutable array in a linear context.
|||
||| Note: In case you don't need to freeze the array in the end, you
|||       might also use `alloc`
export
allocUr : (n : Nat) -> (fun : WithMBufferUr n a) -> a
allocUr n f =
  runUr $ \t => let buf # t2 := newMBuffer n t in f @{buf} t2

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export
copy :
     IBuffer m
  -> (0 tag : _)
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> {auto buf : MBuffer tag s n}
  -> F1' s
copy (IB src) tag srcOffset dstOffset len t =
  let MB dst        := buf
      MkIORes () w2 :=
        prim__copy src (cast srcOffset) (cast len) dst (cast dstOffset) %MkWorld
   in t

||| Copy the content of an immutable buffer to a new buffer.
export
thaw : {n : _} -> IBuffer n -> (fun : WithMBufferUr n b) -> b
thaw src f =
  allocUr n $ \t =>
    let t1 := copy src () 0 0 n @{reflexive} @{reflexive} t
     in f t1

||| Wrap a mutable buffer in an `IBuffer` without copying.
|||
||| In order to make this safe, the associated linear token has to
||| be discarded.
|||
||| It is safe to only use a prefix of a properly constructed array,
||| therefore we are free to give the resulting array a smaller size.
||| Most of the time, we'd like to use the whole buffer, in which case
||| we can just use `freezeBufAt`.
export
freezeAtLTE :
     (0 tag : _)
  -> {auto 0 _ : LTE m n}
  -> {auto arr : MBuffer tag s n}
  -> (0 m : Nat)
  -> T1 s
  -@ Ur (IBuffer m)
freezeAtLTE _ @{_} @{MB buf} _ t = discard t (MkBang $ IB buf)

export %inline
freezeAt : (0 tag : _) -> MBuffer tag s n => T1 s -@ Ur (IBuffer n)
freezeAt tag = freezeAtLTE tag @{reflexive} n

||| Wrap a mutable byte array in an `IBuffer`, which can then be freely shared.
export %inline
freezeLTE :
     {auto 0 p : LTE m n}
  -> {auto arr : MBuffer () s n}
  -> (0 m : Nat)
  -> T1 s
  -@ Ur (IBuffer m)
freezeLTE = freezeAtLTE () @{p}

||| Wrap a mutable byte array in an `IBuffer`, which can then be freely shared.
export %inline
freeze : MBuffer () s n => T1 s -@ Ur (IBuffer n)
freeze = freezeAt ()

||| Release a mutable linear buffer to `IO`, thus making it freely
||| shareable.
export %inline
toIO : (0 tag : _) -> MBuffer tag s n => T1 s -@ Ur (IO Buffer)
toIO tag @{MB buf} t = discard t (MkBang $ pure buf)

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
  -> (0 tag : _)
  -> File
  -> (offset,len : Nat)
  -> {auto 0 prf : LTE (offset + len) n}
  -> {auto buf : MBuffer tag s n}
  -> T1 s
  -@ Ur (io (Either (FileError,Int) ()))
writeMBuffer tag h o s t =
  let MB b := buf
   in discard t (MkBang $ writeBufferData h b (cast o) (cast s))
