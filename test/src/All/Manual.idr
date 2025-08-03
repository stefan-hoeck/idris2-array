module All.Manual

import Data.Array.All as A
import Hedgehog

import Syntax.T1

%default total

0 Types : List Type
Types = [Bool, String, List Nat, Maybe Bits8, String]

vals : HList Types
vals = [True,"foo",[1,2],Nothing,"quux"]

test1 : Eq a => Show a => a -> a -> Property
test1 x y = property1 (x === y)

getOnly : (0 a : Type) -> Elem a Types => a
getOnly a =
  run1 $ T1.do
    m <- mall1 vals
    getElem m a

getAt : (x : Fin (length Types)) -> A.Index Types x
getAt x =
  run1 $ T1.do
    m <- mall1 vals
    All.get m x

setget : (0 a : Type) -> Elem a Types => a -> a
setget a v =
  run1 $ T1.do
    m <- mall1 vals
    setElem m v
    getElem m a

setgetIx : (x : Fin (length Types)) -> (v : A.Index Types x) -> A.Index Types x
setgetIx x v =
  run1 $ T1.do
    m <- mall1 vals
    All.set m x v
    All.get m x

export
props : Group
props =
  MkGroup "all-manual"
    [ ("setget_bool",   test1 (setget Bool False) False)
    , ("setget_maybe",  test1 (setget (Maybe Bits8) (Just 12)) (Just 12))
    , ("setget_maybe",  test1 (setget String "bar") "bar")
    , ("setgetIx_str1", test1 (setgetIx 1 "bar") "bar")
    , ("setgetIx_str4", test1 (setgetIx 4 "bar") "bar")
    , ("setgetIx_list", test1 (setgetIx 2 [12,13]) [12,13])
    , ("getOnly_bool",  test1 (getOnly Bool) True)
    , ("getOnly_list",  test1 (getOnly (List Nat)) [1,2])
    , ("getOnly_list",  test1 (getOnly (List Nat)) [1,2])
    , ("getAt_str1",    test1 (Manual.getAt 1) "foo")
    , ("getAt_str4",    test1 (Manual.getAt 4) "quux")
    ]

