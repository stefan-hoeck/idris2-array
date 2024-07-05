module Data.Linear.Token

import public Data.Linear

%default total

||| An alias for the `!*` type constructor.
|||
||| `Ur` is an abbreviation for "unrestricted", meaning the wrapped value
||| can be used an arbitrary number of times, even if the `Ur` itself is used
||| in a linear context.
public export
0 Ur : Type -> Type
Ur = (!*)

public export
data T1 : (s : t) -> Type where
  MkT1 : (1 w : %World) -> T1 s

export %inline
unsafeDiscard : (1 t : T1 s) -> (1 v : a) -> a
unsafeDiscard (MkT1 %MkWorld) x = x

public export
data R1 : (s : t) -> (a : Type) ->  Type where
  (#) : (v : a) -> (1 tok : T1 s) -> R1 s a

public export
0 F1' : (s : t) -> Type
F1' s = T1 s -@ T1 s

public export
0 F1 : (s : t) -> Type -> Type
F1 s a = T1 s -@ R1 s a

--------------------------------------------------------------------------------
-- Linear Utilities
--------------------------------------------------------------------------------

||| Filter a list via a linear function.
export
filterLin : (a -> F1 s Bool) -> List a -> F1 s (List a)
filterLin f vs = go [<] vs
  where
    go : SnocList a -> List a -> F1 s (List a)
    go sv [] m = (sv <>> []) # m
    go sv (h::t) m =
      let True # m2 := f h m | _ # m2 => go sv t m2
       in go (sv :< h) t m2

||| Map a list via a linear function.
export
mapLin : (a -> F1 s b) -> List a -> F1 s (List b)
mapLin f vs = go [<] vs
  where
    go : SnocList b -> List a -> F1 s (List b)
    go sv [] m = (sv <>> []) # m
    go sv (h::t) m = let v # m2 := f h m in go (sv :< v) t m2

||| Map and filter a list via a linear function.
export
mapMaybeLin : (a -> F1 s (Maybe b)) -> List a -> F1 s (List b)
mapMaybeLin f vs = go [<] vs
  where
    go : SnocList b -> List a -> F1 s (List b)
    go sv [] m = (sv <>> []) # m
    go sv (h::t) m =
      let Just v # m2 := f h m | _ # m2 => go sv t m2
       in go (sv :< v) t m2
