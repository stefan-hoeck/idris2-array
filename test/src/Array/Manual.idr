module Array.Manual

import Data.Array.Indexed
import Data.Array.Mutable
import Data.Linear.Token.Syntax
import Data.Vect
import Hedgehog

%default total

test1 : Eq a => Show a => a -> a -> Property
test1 x y = property1 (x === y)

getOnly : WithMArray 10 String String
getOnly r = get r 3

setget : WithMArray 10 String (String,String)
setget r t =
  let _  # t := set r 3 "bar" t
      s1 # t := get r 3 t
      s2 # t := get r 2 t
   in (s1,s2) # t

setgetSyntax : WithMArray 10 String (String,String)
setgetSyntax r = Syntax.do
  set r 3 "bar"
  [| MkPair (get r 3) (get r 2) |]

writeLst : WithMArray 4 String (String,String)
writeLst r = Syntax.do
  writeList r {xs = ["1","2","3","4"]} ["1","2","3","4"]
  [| MkPair (get r 0) (get r 1) |]

writeVct : WithMArray 4 String (String,String)
writeVct r = Syntax.do
  writeVect r ["1","2","3","4"]
  [| MkPair (get r 0) (get r 1) |]

writeVctUr : FromMArray 4 String (IArray 4 String)
writeVctUr r t =
  let _ # t := writeVect r ["1","2","3","4"] t
   in freeze r t

export
props : Group
props =
  MkGroup "array-manual"
    [ ("getOnly", test1 (alloc 10 "foo" getOnly) "foo")
    , ("setget",  test1 (alloc 10 "foo" setget) ("bar","foo"))
    , ("setgetSyntax",  test1 (alloc 10 "foo" setgetSyntax) ("bar","foo"))
    , ("writeLst",  test1 (alloc 4 "foo" writeLst) ("1","2"))
    , ("writeVct",  test1 (alloc 4 "foo" writeVct) ("1","2"))
    , ("writeVctUr",  test1 (create 4 "foo" writeVctUr) (array ["1","2","3","4"]))
    ]
