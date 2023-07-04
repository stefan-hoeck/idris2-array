module Array

import Data.Array
import Data.SOP
import Data.SnocList
import Hedgehog

%default total

arrayOf : Gen a -> Gen (Array a)
arrayOf g = fromList <$> list (linear 0 20) g

arrBits : Gen (Array Bits8)
arrBits = arrayOf anyBits8

prop_eq_refl : Property
prop_eq_refl = property $ do
  vs <- forAll arrBits
  vs === vs

prop_eq_sym : Property
prop_eq_sym = property $ do
  [vs,ws] <- forAll $ np [arrBits,arrBits]
  (vs == ws) === (ws == vs)

prop_eq_trans : Property
prop_eq_trans = property $ do
  [us,vs,ws] <- forAll $ np [arrBits,arrBits,arrBits]
  when (us == vs && vs == ws) (us === ws)

prop_eq_eq : Property
prop_eq_eq = property $ do
  [vs,ws] <- forAll $ np [arrBits,arrBits]
  when (vs == ws) $ do
    assert (vs <= ws)
    assert (vs >= ws)
    assert (ws >= vs)
    assert (ws <= vs)
    (compare vs ws === EQ)

prop_eq_neq : Property
prop_eq_neq = property $ do
  [vs,ws] <- forAll $ np [arrBits,arrBits]
  when (vs /= ws) $ do
    assert (vs < ws || ws < vs)

prop_lt : Property
prop_lt = property $ do
  [vs,ws] <- forAll $ np [arrBits,arrBits]
  ((vs < ws) === (ws > vs))
  when (vs < ws) $ do
    assert (vs /= ws)
    assert (vs <= ws)
    assert (ws >= vs)

prop_lte : Property
prop_lte = property $ do
  [vs,ws] <- forAll $ np [arrBits,arrBits]
  ((vs <= ws) === (ws >= vs))

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll arrBits
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  toList (Array.fromList vs) === vs

prop_foldl : Property
prop_foldl = property $ do
  vs <- forAll arrBits
  foldl (:<) [<] vs === foldl (:<) [<] (toList vs)

prop_foldr : Property
prop_foldr = property $ do
  vs <- forAll arrBits
  foldr (::) [] vs === foldr (::) [] (toList vs)

prop_null : Property
prop_null = property $ do
  vs <- forAll arrBits
  null vs === null (toList vs)

prop_size : Property
prop_size = property $ do
  vs <- forAll arrBits
  size vs === length (toList vs)

prop_generate : Property
prop_generate = property1 $
  toList (Array.generate 5 $ \x => let n := finToNat x in n*n) === [0,1,4,9,16]

prop_iterate : Property
prop_iterate = property1 $
  toList (Array.iterate 5 (*3) (S Z)) === [1,3,9,27,81]

prop_filter : Property
prop_filter = property $ do
  vs <- forAll arrBits
  toList (filter (< 10) vs) === filter (< 10) (toList vs)

foo : Bits8 -> Maybe String
foo v = if v < 10 then Just (show v) else Nothing

prop_mapMaybe : Property
prop_mapMaybe = property $ do
  vs <- forAll arrBits
  toList (mapMaybe foo vs) === mapMaybe foo (toList vs)

export
props : Group
props = MkGroup "Array"
  [ ("prop_eq_refl", prop_eq_refl)
  , ("prop_eq_sym", prop_eq_sym)
  , ("prop_eq_trans", prop_eq_trans)
  , ("prop_eq_eq", prop_eq_eq)
  , ("prop_eq_neq", prop_eq_neq)
  , ("prop_lt", prop_lt)
  , ("prop_lte", prop_lte)
  , ("prop_map_id", prop_map_id)
  , ("prop_from_to_list", prop_from_to_list)
  , ("prop_foldl", prop_foldl)
  , ("prop_foldr", prop_foldr)
  , ("prop_null", prop_null)
  , ("prop_size", prop_size)
  , ("prop_generate", prop_generate)
  , ("prop_iterate", prop_iterate)
  , ("prop_filter", prop_filter)
  , ("prop_mapMaybe", prop_mapMaybe)
  ]

