module Buffer.Manual

import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.Buffer.Mutable
import Data.Vect
import Hedgehog

import Syntax.T1

%default total

test1 : Eq a => Show a => a -> a -> Property
test1 x y = property1 (x === y)

getOnly : WithMBuffer 10 Bits8
getOnly r = get r 3

setget : WithMBuffer 10 (Bits8,Bits8)
setget r = T1.do
  set r 3 127
  s1 <- get r 3
  s2 <- get r 2
  pure (s1,s2)

setgetSyntax : WithMBuffer 10 (Bits8,Bits8)
setgetSyntax r = T1.do
  set r 3 155
  [| MkPair (get r 3) (get r 2) |]

writeLst : WithMBuffer 4 (Bits8,Bits8)
writeLst r = T1.do
  writeList r {xs = [1,2,3,4]} [1,2,3,4]
  [| MkPair (get r 0) (get r 1) |]

writeVct : WithMBuffer 4 (Bits8,Bits8)
writeVct r = T1.do
  writeVect r [1,2,3,4]
  [| MkPair (get r 0) (get r 1) |]

writeVctUr : WithMBuffer 4 (IBuffer 4)
writeVctUr r t =
  let _ # t := writeVect r [1,2,3,4] t
   in unsafeFreeze r t

export
props : Group
props =
  MkGroup "buffer-manual"
    [ ("getOnly", test1 (alloc 10 getOnly) 0)
    , ("setget",  test1 (alloc 10 setget) (127,0))
    , ("setgetSyntax",  test1 (alloc 10 setgetSyntax) (155,0))
    , ("writeLst",  test1 (alloc 4 writeLst) (1,2))
    , ("writeVct",  test1 (alloc 4 writeVct) (1,2))
    , ("writeVctUr",  test1 (alloc 4 writeVctUr) (buffer [1,2,3,4]))
    ]
