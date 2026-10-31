module TArray

import Data.TArray
import Derive.Enum
import Hedgehog

%language ElabReflection
%default total

data MyTyp : Type -> Type where
  ABool   : MyTyp Bool
  ANat    : MyTyp Nat
  AString : MyTyp String
  AMaybe  : MyTyp (Maybe Integer)
  AList   : MyTyp (List Bool)

%runElab deriveIndexed "MyTyp" [TEnum]

arr : TArray MyTyp List
arr =
  tarray _ _ []
    [E ABool [True,False], E AList [[],[False]], E AMaybe [Just 12]]

prop : Property
prop =
  property $ do
    at arr ABool === [True,False]
    at arr ANat === []
    at arr AString === []
    at arr AMaybe === [Just 12]
    at arr AList === [[],[False]]

export
props : Group
props = MkGroup "Data.TArray" [ ("prop", prop) ]
