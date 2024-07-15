module Buffer.Manual

import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.Buffer.Mutable
import Data.Linear.Token.Syntax
import Data.Vect
import Hedgehog

%default total

test1 : Eq a => Show a => a -> a -> Property
test1 x y = property1 (x === y)

getOnly : MBuffer () s 10 => F1 s Bits8
getOnly = get 3

setget : MBuffer () s 10 => F1 s (Bits8,Bits8)
setget t =
  let t2 := set 3 127 t
      s1 # t3 := get 3 t2
      s2 # t4 := get 2 t3
   in (s1,s2) # t4

setgetSyntax : MBuffer () s 10 => F1 s (Bits8,Bits8)
setgetSyntax = Syntax.do
  set 3 155
  [| MkPair (get 3) (get 2) |]

writeLst : MBuffer () s 4 => F1 s (Bits8,Bits8)
writeLst = Syntax.do
  writeList () {xs = [1,2,3,4]} [1,2,3,4]
  [| MkPair (get 0) (get 1) |]

writeVct : MBuffer () s 4 => F1 s (Bits8,Bits8)
writeVct = Syntax.do
  writeVect () [1,2,3,4]
  [| MkPair (get 0) (get 1) |]

writeVctUr : MBuffer () s 4 => (1 t : T1 s) -> Ur (IBuffer 4)
writeVctUr t =
  let t2 := writeVect () [1,2,3,4] t
   in freeze t2

export
props : Group
props =
  MkGroup "buffer-manual"
    [ ("getOnly", test1 (alloc 10 getOnly) 0)
    , ("setget",  test1 (alloc 10 setget) (127,0))
    , ("setgetSyntax",  test1 (alloc 10 setgetSyntax) (155,0))
    , ("writeLst",  test1 (alloc 4 writeLst) (1,2))
    , ("writeVct",  test1 (alloc 4 writeVct) (1,2))
    , ("writeVctUr",  test1 (allocUr 4 writeVctUr) (buffer [1,2,3,4]))
    ]
