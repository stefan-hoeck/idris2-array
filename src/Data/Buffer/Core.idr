module Data.Buffer.Core

import Data.Buffer
import Data.Linear
import Data.Array.Core
import public Data.Fin
import public Data.Nat

%default total

--------------------------------------------------------------------------------
--          Raw Primitives
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-buffer-getbyte"
         "node:lambda:(buf,offset)=>buf.readUInt8(Number(offset))"
prim__getByte : Buffer -> (offset : Integer) -> Bits8

%foreign "scheme:blodwen-buffer-setbyte"
         "node:lambda:(buf,offset,value)=>buf.writeUInt8(value, Number(offset))"
prim__setByte : Buffer -> (offset : Integer) -> (val : Bits8) -> PrimIO ()

%foreign "scheme:blodwen-new-buffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuf : Bits32 -> Buffer

%foreign "scheme:blodwen-buffer-getstring"
         "node:lambda:(buf,offset,len)=>buf.slice(Number(offset), Number(offset+len)).toString('utf-8')"
prim__getString : Buffer -> (offset,len : Integer) -> String

%foreign "scheme:blodwen-buffer-copydata"
         "node:lambda:(b1,o1,length,b2,o2)=>b1.copy(Number(b2),Number(o2),Number(o1),Number(o1+length))"
prim__copy : (src : Buffer) -> (srcOffset, len : Integer) ->
             (dst : Buffer) -> (dstOffset : Integer) -> PrimIO ()

destroy : (1 _ : %World) -> (1 _ : a) -> a
destroy %MkWorld x = x

set' : (o : Nat) -> Bits8 -> Buffer -> Buffer
set' o v buf =
  let MkIORes () w2 := prim__setByte buf (cast o) v %MkWorld
   in destroy w2 buf

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

||| Extracts the inner buffer held by a byte array without copying.
|||
||| This allows us to write efficiently write the data to a file
||| without copying it first. This is a highly unsafe operation,
||| and client code must make sure never ever to mutate the buffer!
export
unsafeGetBuffer : IBuffer n -> Buffer
unsafeGetBuffer (IB buf) = buf

--------------------------------------------------------------------------------
--          Mutable Byte Arrays
--------------------------------------------------------------------------------

||| A mutable byte array.
export
record MBuffer (n : Nat) where
  constructor MB
  buf : Buffer

||| Allocate and release a mutable byte array in a linear context.
|||
||| Function `fun` must use the given array exactly once, while
||| its result must be wrapped in a `Ur`, guaranteeing, that the
||| mutable array will never be used outside of `fun`, especially
||| that the result `b` does not hold a reference to the mutable
||| array.
export
alloc : (n : Nat) -> (1 fun : MBuffer n -@ Ur b) -> Ur b
alloc n f = f (MB $ prim__newBuf (cast n))

||| Copy the content of an immutable buffer to a new buffer.
export
thaw : {n : _} -> IBuffer n -> (1 fun : MBuffer n -@ Ur b) -> Ur b
thaw (IB buf) f =
  let buf2 := prim__newBuf (cast n)
      MkIORes () w2 := prim__copy buf2 0 (cast n) buf 0 %MkWorld
   in destroy w2 (f $ MB buf2)

||| Safely write a value to a mutable byte array.
|||
||| Since the array must be used exactly once, a "new" array (the
||| same array wrapped in a new `MB`) must be returned, which will
||| then again be used exactly once.
export
set : Fin n -> Bits8 -> MBuffer n -@ MBuffer n
set m x (MB buf) = MB $ set' (finToNat m) x buf

||| Safely read a value from a mutable byte array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new `MBuffer` of quantity one to be further used in the
||| linear context. See implementation notes on `set` about some details,
||| how this works.
export
get : Fin n -> MBuffer n -@ CRes Bits8 (MBuffer n)
get m (MB buf) = prim__getByte buf (cast $ finToNat m) # MB buf

||| Safely modify a value in a mutable byte array.
|||
||| Since mutable arrays must be used in a linear context, and this
||| function "uses up" its input as far as the linearity checker is
||| concerned, this returns a new `MBuffer` wrapper, which must then
||| again be used exactly once.
export
modify : Fin n -> (Bits8 -> Bits8) -> MBuffer n -@ MBuffer n
modify m f (MB buf) =
  let v := prim__getByte buf (cast $ finToNat m)
   in MB $ set' (finToNat m) (f v) buf

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
freezeLTE : (0 m : Nat) -> (0 _ : LTE m n) => MBuffer n -@ Ur (IBuffer m)
freezeLTE _ (MB buf) = MkBang $ IB buf

||| Wrap a mutable byte array in an `IBuffer`, which can then be freely shared.
|||
||| See `freezeLTE` for some additional notes about how this works under
||| the hood.
export %inline
freeze : MBuffer n -@ Ur (IBuffer n)
freeze = freezeLTE n @{reflexive}

||| Safely discard a linear mutable array.
export %inline
discard : MBuffer n -@ ()
discard (MB _) = ()

||| Safely discard a linear mutable array, returning a non-linear
||| result at the same time.
export %inline
discarding : (1 _ : MBuffer n) -> x -> x
discarding (MB _) x = x
