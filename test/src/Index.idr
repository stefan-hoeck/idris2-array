||| The tests in this module *must* be run on large natural numbers
||| to make sure that convertions between indices and natural numbers
||| are optimized by Idris to the identity function and run in O(1).
module Index

import Data.Array.Index
import Hedgehog

%default total

largeNat : Gen Nat
largeNat = nat (exponential 0 0xffff_ffff_ffff_ffff)

forAllNats : PropertyT Nat
forAllNats = do
  n <- forAll largeNat
  classify "n in (0,2^16]"    (n <= 0xffff)
  classify "n in (2^16,2^32]" (n > 0xffff && n <= 0xffff_ffff)
  classify "n in (2^32,2^48]" (n > 0xffff_ffff && n <= 0xffff_ffff_ffff)
  classify "n in (2^48,2^64]" (n > 0xffff_ffff_ffff && n <= 0xffff_ffff_ffff_ffff)
  pure n

-- Verifies that `ixToNat`, `succIx`, and `natToIx` all run in O(1).
prop_ixToNatRoundTrip : Property
prop_ixToNatRoundTrip = property $ do
  n <- forAllNats
  ixToNat (natToIx n) === n

-- Verifies that `natToFin` and `finToNatLT` run in O(1)
prop_natToFinRoundTrip : Property
prop_natToFinRoundTrip = property $ do
  n <- forAllNats
  finToNat (natToFinLT n @{refl}) === n

-- Verifies that `ixToFin` runs in O(1)
prop_natToIxToFinRoundTrip : Property
prop_natToIxToFinRoundTrip = property $ do
  n <- forAllNats
  finToNat (ixToFin $ natToIx1 n) === n

-- Verifies that `weaken` runs in O(1)
prop_weakenRoundTrip : Property
prop_weakenRoundTrip = property $ do
  n <- forAllNats
  finToNat (weaken $ natToFinLT n @{refl}) === n

-- Verifies that `weakenN` runs in O(1)
prop_weakenNRoundTrip : Property
prop_weakenNRoundTrip = property $ do
  n <- forAllNats
  finToNat (weakenN 1000 $ natToFinLT n @{refl}) === n

export
props : Group
props = MkGroup "Index"
  [ ("prop_ixToNatRoundTrip", prop_ixToNatRoundTrip)
  , ("prop_natToFinRoundTrip", prop_natToFinRoundTrip)
  , ("prop_natToIxToFinRoundTrip", prop_natToIxToFinRoundTrip)
  , ("prop_weakenRoundTrip", prop_weakenRoundTrip)
  , ("prop_weakenNRoundTrip", prop_weakenNRoundTrip)
  ]
