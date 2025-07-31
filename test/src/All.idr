module All

import Data.Array.All
import Data.List.Quantifiers
import Hedgehog

%default total

vals : Gen (HList [Maybe Bool, String, Either Nat (List Bits8)])
vals = hlist [maybe bool, str, either (nat $ linear 0 20) lst]
  where
    str  : Gen String
    str  = string (linear 0 10) printableAscii

    lst  : Gen (List Bits8)
    lst  = list (linear 0 10) anyBits8

harr : Gen (HArr [Maybe Bool, String, Either Nat (List Bits8)])
harr = (\xs => all xs) <$> vals

prop_at0 : Property
prop_at0 =
  property $ do
    hv <- forAll vals
    (all hv `at` 0) === index 0 hv

prop_at1 : Property
prop_at1 =
  property $ do
    hv <- forAll vals
    (all hv `at` 1) === index 1 hv

prop_at2 : Property
prop_at2 =
  property $ do
    hv <- forAll vals
    (all hv `at` 2) === index 2 hv

export
props : Group
props = MkGroup "All"
  [ ("prop_at0", prop_at0)
  , ("prop_at1", prop_at1)
  , ("prop_at2", prop_at2)
  ]
