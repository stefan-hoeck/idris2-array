module Main

import Data.Array
import Hedgehog

arrayOf : Gen a -> Gen (Array a)
arrayOf g = fromList <$> list (linear 0 10) g

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll (arrayOf anyBits32)
  vs === vs

main : IO ()
main = test . pure $ MkGroup "Array"
  [ ("prop_eq_refl", prop_eq_refl)
  ]
