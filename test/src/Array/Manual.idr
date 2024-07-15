module Array.Manual

import Data.Array.Indexed
import Data.Array.Mutable
import Data.Linear.Token.Syntax
import Data.Vect
import Hedgehog

%default total

test1 : Eq a => Show a => a -> a -> Property
test1 x y = property1 (x === y)

getOnly : MArray () s 10 String => F1 s String
getOnly = get 3

setget : MArray () s 10 String => F1 s (String,String)
setget t =
  let t2 := set 3 "bar" t
      s1 # t3 := get 3 t2
      s2 # t4 := get 2 t3
   in (s1,s2) # t4

setgetSyntax : MArray () s 10 String => F1 s (String,String)
setgetSyntax = Syntax.do
  set 3 "bar"
  [| MkPair (get 3) (get 2) |]

writeLst : MArray () s 4 String => F1 s (String,String)
writeLst = Syntax.do
  writeList () {xs = ["1","2","3","4"]} ["1","2","3","4"]
  [| MkPair (get 0) (get 1) |]

writeVct : MArray () s 4 String => F1 s (String,String)
writeVct = Syntax.do
  writeVect () ["1","2","3","4"]
  [| MkPair (get 0) (get 1) |]

writeVctUr : MArray () s 4 String => (1 t : T1 s) -> Ur (IArray 4 String)
writeVctUr t =
  let t2 := writeVect () ["1","2","3","4"] t
   in freeze t2

export
props : Group
props =
  MkGroup "array-manual"
    [ ("getOnly", test1 (alloc 10 "foo" getOnly) "foo")
    , ("setget",  test1 (alloc 10 "foo" setget) ("bar","foo"))
    , ("setgetSyntax",  test1 (alloc 10 "foo" setgetSyntax) ("bar","foo"))
    , ("writeLst",  test1 (alloc 4 "foo" writeLst) ("1","2"))
    , ("writeVct",  test1 (alloc 4 "foo" writeVct) ("1","2"))
    , ("writeVctUr",  test1 (allocUr 4 "foo" writeVctUr) (array ["1","2","3","4"]))
    ]
