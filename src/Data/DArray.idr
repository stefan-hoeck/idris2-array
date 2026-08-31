module Data.DArray

import Data.List.Elem
import Data.Array.Core
import Data.Linear.Token
import public Data.Array.Index

%default total

public export
interface Enum (0 i : Type) (0 n : Nat) | i where
  toFin   : i -> Fin n

%inline
toInteger : Enum i n => i -> Integer
toInteger = cast . finToNat . toFin

export
record DArray (i : Type) (p : i -> Type) where
  constructor DA
  arr : AnyPtr

export %inline
at : Enum i n => DArray i p -> (x : i) -> p x
at (DA ad) x = believe_me $ prim__arrayGet ad (toInteger x)

export
record MDArray (s : Type) (i : Type) (p : i -> Type) where
  constructor MDA
  arr : AnyPtr

export %inline
dget : Enum i n => MDArray s i p -> (x : i) -> F1 s (p x)
dget (MDA ad) x t =
  believe_me (prim__arrayGet ad $ toInteger x) # t

export %inline
dset : Enum i n => MDArray s i p -> (x : i) -> p x -> F1' s
dset (MDA ad) x v =
  ffi (prim__arraySet ad (toInteger x) (believe_me v))

export %inline
unsafeFreeze : MDArray s i p -> F1 s (DArray i p)
unsafeFreeze (MDA ad) t = DA ad # t

export
freeze : {n : _} -> Enum i n => MDArray s i p -> F1 s (DArray i p)
freeze (MDA src) t =
  let dst # t := ffi (prim__emptyArray $ cast n) t
      _   # t := ffi (prim__copyArray src 0 (cast n) dst 0) t
   in DA dst # t

parameters (0 i       : Type)
           (0 p       : i -> Type)
           {n         : Nat}
           {auto enum : Enum i n}

  export %inline
  unsafeMDArray1 : F1 s (MDArray s i p)
  unsafeMDArray1 t =
    let p # t := ffi (prim__emptyArray $ cast n) t in MDA p # t

  ||| A safe constructor for mutable dependent arrays.
  export
  mdarray1 :
       (is : List i)
    -> (0 prf : (v : i) -> Elem v is)
    -> (val : (v : i) -> p v)
    -> F1 s (MDArray s i p)
  mdarray1 is _ val t = let md # t := unsafeMDArray1 t in go is md t
    where
      go : List i -> MDArray s i p -> F1 s (MDArray s i p)
      go []        m t = m # t
      go (x :: xs) m t = let _ # t := dset m x (val x) t in go xs m t

  export %inline
  darray :
       (is : List i)
    -> (0 prf : (v : i) -> Elem v is)
    -> (val : (v : i) -> p v)
    -> DArray i p
  darray is prf val =
    run1 $ \t => let m # t := mdarray1 is prf val t in freeze m t
