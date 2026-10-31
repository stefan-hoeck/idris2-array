module Data.TArray

import Data.Array.Core
import Data.Linear.Token
import Data.List.Quantifiers
import public Data.Enum

%default total

export
record TArray (i : k -> Type) (f : k -> Type) where
  constructor TA
  arr : AnyPtr

export %inline
at : TEnum i n => TArray i f -> (x : i t) -> f t
at (TA ad) x = believe_me $ prim__arrayGet ad (tenumToInteger x)

export
record MTArray (s : Type) (i : k -> Type) (f : k -> Type) where
  constructor MTA
  arr : AnyPtr

export %inline
tget : TEnum i n => MTArray s i f -> i t -> F1 s (f t)
tget (MTA ad) x t =
  believe_me (prim__arrayGet ad $ tenumToInteger x) # t

export %inline
tset : TEnum i n => MTArray s i f -> i t -> f t -> F1' s
tset (MTA ad) x v =
  ffi (prim__arraySet ad (tenumToInteger x) (believe_me v))

export %inline
unsafeFreeze : MTArray s i f -> F1 s (TArray i f)
unsafeFreeze (MTA ad) t = TA ad # t

export
freeze : {n : _} -> TEnum i n => MTArray s i f -> F1 s (TArray i f)
freeze (MTA src) t =
  let dst # t := ffi (prim__emptyArray $ cast n) t
      _   # t := ffi (prim__copyArray src 0 (cast n) dst 0) t
   in TA dst # t

public export
record Entry (i,f : k -> Type) where
  constructor E
  {0 type : k}
  index : i type
  value : f type

public export
0 Entries : (i,f : k -> Type) -> Type
Entries i f = List (Entry i f)

parameters (0 i,f     : k -> Type)
           {n         : Bits32}
           {auto enum : TEnum i n}

  export %inline
  unsafeMDArray1 : F1 s (MTArray s i f)
  unsafeMDArray1 t =
    let p # t := ffi (prim__emptyArray $ cast n) t in MTA p # t

  ||| A safe constructor for mutable dependent arrays.
  export
  mtarray1 : ({0 x : k} -> f x) -> F1 s (MTArray s i f)
  mtarray1 dflt t =
    let v     := the AnyPtr (believe_me $ dflt {x = believe_me 1})
        p # t := ffi (prim__newArray (cast n) v) t
     in MTA p # t

  ||| A safe constructor for mutable dependent arrays.
  export
  mtarrayVals1 : ({0 x : k} -> f x) -> Entries i f -> F1 s (MTArray s i f)
  mtarrayVals1 dflt vs t = let m # t := mtarray1 dflt t in go vs m t
    where
      go : Entries i f -> MTArray s i f -> F1 s (MTArray s i f)
      go []          m t = m # t
      go (E i v::xs) m t = let _ # t := tset m i v t in go xs m t

  export %inline
  tarray : ({0 x : k} -> f x) -> Entries i f -> TArray i f
  tarray d es = run1 $ \t => let m # t := mtarrayVals1 d es t in freeze m t
