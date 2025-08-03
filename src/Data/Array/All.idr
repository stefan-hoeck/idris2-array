module Data.Array.All

import public Data.List
import public Data.List.Elem
import public Data.List.Quantifiers

import Data.Array.Core
import Data.Array.Index
import Data.Linear
import Data.Linear.Token

%default total

public export
data El : List a -> List a -> Type where
  ZEl : El as as
  SEl : El as (v::bs) -> El as bs

export
elToNat : El as bs -> Nat
elToNat ZEl     = 0
elToNat (SEl k) = S $ elToNat k

export
0 elLemma : (el : El as (v::bs)) -> LT (elToNat el) (length as)
elLemma ZEl     = LTESucc LTEZero
elLemma (SEl x) =
 let p := elLemma x
  in ?foo

--------------------------------------------------------------------------------
-- Immutable heterogeneous arrays
--------------------------------------------------------------------------------

||| An immutable heterogeneous array of size `n`.
|||
||| This has different performance characteristics than
||| `Data.List.Quantifiers.All`: Lookup is `O(1)`, while
||| prepending and appending is `O(n)`.
export
record ArrAll (f : a -> Type) (as : List a) where
  constructor AA
  arr : AnyPtr

public export
0 HArr : List Type -> Type
HArr = ArrAll Prelude.id

public export
Index : (as : List a) -> Fin (length as) -> a
Index (x :: xs) FZ     = x
Index (x :: xs) (FS k) = Index xs k
Index [] _ impossible

export
elemToFin : Elem a as -> Fin (length as)
elemToFin {as = _::_} Here      = FZ
elemToFin {as = _::_} (There x) = FS $ elemToFin x

len : All f xs -> Nat
len []     = 0
len (_::t) = S $ len t

export
0 ElemLemma : (el : Elem a as) -> a === Index as (elemToFin el)
ElemLemma Here      = Refl
ElemLemma (There x) = ElemLemma x

||| Safely access a value in a heterogeneous array at the given position.
export %inline
at : ArrAll f as -> (x : Fin (length as)) -> f (Index as x)
at (AA ad) m = believe_me $ prim__arrayGet ad (cast $ finToNat m)


||| Safely access a value in a heterogeneous array
||| at the position of the given tag
export %inline
elem : ArrAll f as -> (0 a : _) -> (el : Elem a as) => f a
elem arr a = rewrite ElemLemma el in at arr (elemToFin el)

--------------------------------------------------------------------------------
--          Immutable Heterogeneous Arrays
--------------------------------------------------------------------------------

||| A mutable array.
export
data MArrAll : (s : Type) -> (f : a -> Type) -> (as : List a) -> Type where
  MA : (arr : AnyPtr) -> MArrAll s f as

public export
0 MHArr : Type -> List Type -> Type
MHArr s = MArrAll s Prelude.id

||| Safely write a value to a mutable heterogeneous array.
export %inline
set : MArrAll s f as -> (x : Fin (length as)) -> f (Index as x) -> F1' s
set (MA arr) ix v = ffi (prim__arraySet arr (cast $ finToNat ix) (believe_me v))

||| Safely write a value to a mutable heterogeneous array.
export %inline
setElem : MArrAll s f as -> f a -> (el : Elem a as) => F1' s
setElem arr v = All.set arr (elemToFin el) (rewrite sym (ElemLemma el) in v)

||| Safely write a value to a mutable heterogeneous array.
export
setEls : MArrAll s f as -> All f bs -> (el : El as bs) -> F1' s
setEls arr []             el t = () # t
setEls ma@(MA arr) (v :: vs) el t =
 let _ # t := ffi (prim__arraySet arr (cast $ elToNat el) (believe_me v)) t
  in setEls ma vs %search t

||| Safely read a value from a mutable array.
|||
||| This returns the values thus read with unrestricted quantity, paired
||| with a new linear token of quantity one to be further used in the
||| linear context.
export %inline
get : MArrAll s f as -> (x : Fin (length as)) -> F1 s (f $ Index as x)
get (MA arr) ix t = believe_me (prim__arrayGet arr (cast $ finToNat ix)) # t

export %inline
getElem : MArrAll s f as -> (0 a : _) -> (el : Elem a as) => F1 s (f a)
getElem arr ix = rewrite ElemLemma el in get arr (elemToFin el)

export
setElems : All f as -> All (`Elem` bs) as => MArrAll s f bs -> F1' s
setElems []              _ t = () # t
setElems (v::vs) @{_::_} x t = let _ # t := setElem x v t in setElems vs x t

||| Fills a new mutable heterogeneous array bound to linear computation `s`.
export
mall1 : All f as -> F1 s (MArrAll s f as)
mall1 vs t =
 let p # t := ffi (prim__emptyArray (cast $ len vs)) t
     arr   := MA p
     _ # t := setEls arr vs ZEl t
  in arr # t

export %inline
unsafeFreeze : MArrAll s f as -> F1 s (ArrAll f as)
unsafeFreeze (MA p) t = AA p # t

||| Fills a new mutable heterogeneous array
export %inline
mall : Lift1 s m => All f as -> m (MArrAll s f as)
mall as = lift1 (mall1 as)

--------------------------------------------------------------------------------
-- Immutable Utilities
--------------------------------------------------------------------------------

||| Creates a new immutable heterogeneous array
export %inline
all : All f as -> ArrAll f as
all vs = run1 $ \t => let ma # t := mall1 vs t in unsafeFreeze ma t
