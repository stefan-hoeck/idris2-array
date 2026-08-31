module DArray.Util

import public Data.List.Elem
import public Decidable.HDecEq

%default total

public export
inList : HDecEq i => (v : i) -> List i -> Bool
inList v []        = False
inList v (x :: xs) =
  case hdecEq v x of
    Nothing0 => inList v xs
    Just0 _  => True

export
0 hdecEqInList : HDecEq i => (v : i) -> inList v is === True -> Elem v is
hdecEqInList v prf {is = []}    = absurd prf
hdecEqInList v prf {is = x::xs} with (hdecEq v x)
  _ | Nothing0  = There $ hdecEqInList v prf {is = xs}
  _ | Just0 p   = rewrite p in Here
