module Data.Buffer.Builder

import Data.Array.Index
import Data.Buffer
import Data.Buffer.Mutable
import Data.String

import Syntax.T1

import public Data.Buffer.Core
import public Data.Linear.Ref1

%default total

--------------------------------------------------------------------------------
-- Internals
--------------------------------------------------------------------------------

record Pos (n : Nat) where
  constructor P
  val   : Nat
  0 lte : LTE val n

zero : Pos n
zero = P 0 LTEZero

record ST q where
  constructor MkST
  size : Nat
  buf  : MBuffer q size
  pos  : Ref q (Pos size)

putImpl : {n : _} -> Ref q (ST q) -> IBuffer n -> F1' q

putByteImpl : Ref q (ST q) -> Bits8 -> F1' q

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
record Builder q where
  [noHints]
  constructor B
  ref : Ref q (ST q)

export
withBuilder :
     {default 0xfff size : Bits32}
  -> (forall q . Builder q => F1 q a)
  -> a
withBuilder build =
  run1 $ \t =>
   let buf # t := mbuffer1 (cast size) t
       pos # t := ref1 zero t
       ref # t := ref1 (MkST _ buf pos) t
    in build @{B ref} t

export
getBytes : Builder q => F1 q (k ** IBuffer k)
getBytes @{B r} t =
 let st     # t := read1 r t
     P v lt # t := read1 st.pos t
     ib     # t := freezeLTE st.buf v t
     _      # t := write1 st.pos zero t
  in (v ** ib) # t

export
getString : Builder q => F1 q String
getString t = let (k ** ib) # t := getBytes t in toString ib 0 k # t

parameters {auto b : Builder q}

  export %inline
  putByte : Bits8 -> F1' q
  putByte = putByteImpl b.ref

  export %inline
  put : {n : _} -> IBuffer n -> F1' q
  put = putImpl b.ref

  export %inline
  putM : {n : _} -> MBuffer q n -> F1' q
  putM buf t = let ib # t := unsafeFreeze buf t in put ib t

  export %inline
  putStr : String -> F1' q
  putStr s = put (fromString s)

  export %inline
  putChar : Char -> F1' q
  putChar = putStr . singleton

--------------------------------------------------------------------------------
-- Here be dragons
--------------------------------------------------------------------------------

enlarge : Ref q (ST q) -> Nat -> F1' q
enlarge r n t =
 let st      # t := read1 r t
     sz          := max st.size n
     P v lte # t := read1 st.pos t
     buf2    # t := mgrow st.buf sz t
     pos2    # t := ref1 (P v (transitive lte $ lteAddLeft _)) t
  in write1 r (MkST (sz + st.size) buf2 pos2) t

putImpl r ib t =
 let st      # t := read1 r t
     P v lte # t := read1 st.pos t
  in case tryLTE {n = st.size} (v+n) of
       Just0 prf =>
        let _ # t := icopy ib 0 v n st.buf t
         in write1 st.pos (P (v+n) prf) t
       Nothing0  =>
        let _ # t := enlarge r n t
         in assert_total $ putImpl r ib t

putByteImpl r b t =
 let st      # t := read1 r t
     P v lte # t := read1 st.pos t
  in case tryLT {n = st.size} v of
       Just0 prf =>
        let _ # t := Mutable.setNat st.buf v b t
         in write1 st.pos (P (S v) prf) t
       Nothing0  =>
         let _ # t := enlarge r 1 t
          in assert_total $ putByteImpl r b t
