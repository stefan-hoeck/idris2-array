module All.Manual

import Data.Array.All
import Hedgehog

import Syntax.T1

%default total

0 Types : List Type
Types = [Bool, String, List Nat, Maybe Bits8]

vals : HList Types
vals = [True,"foo",[1,2],Nothing]

test1 : Eq a => Show a => a -> a -> Property
test1 x y = property1 (x === y)

setget : (0 a : Type) -> Elem a Types => a -> a
setget a v =
  run1 $ T1.do
    m <- mall1 vals
    setElem m v
    getElem m a

export
props : Group
props =
  MkGroup "all-manual"
    [ ("setget_bool",  test1 (setget Bool False) False)
    , ("setget_maybe", test1 (setget (Maybe Bits8) (Just 12)) (Just 12))
    , ("setget_maybe", test1 (setget String "bar") "bar")
    ]

