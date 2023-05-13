module Main

import Data.Array
import Hedgehog

arrayOf : Gen a -> Gen (n ** Array n a)
arrayOf g = (\vs => (_ ** array vs)) <$> list (linear 0 10) g

prop_eq_refl : Property
prop_eq_refl = property $ do
  (_ ** vs) <- forAll (arrayOf anyBits32)
  vs === vs

main : IO ()
main = test . pure $ MkGroup "Array"
  [ ("prop_eq_refl", prop_eq_refl)
  ]
