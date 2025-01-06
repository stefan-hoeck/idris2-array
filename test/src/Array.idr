module Array

import Control.Monad.Identity
import Data.Array
import Data.Array.Mutable
import Data.List
import Data.List.Quantifiers
import Data.SnocList
import Data.Vect
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
  [vs,ws] <- forAll $ hlist [arrBits,arrBits]
  (vs == ws) === (ws == vs)

prop_eq_trans : Property
prop_eq_trans = property $ do
  [us,vs,ws] <- forAll $ hlist [arrBits,arrBits,arrBits]
  when (us == vs && vs == ws) (us === ws)

prop_eq_eq : Property
prop_eq_eq = property $ do
  [vs,ws] <- forAll $ hlist [arrBits,arrBits]
  when (vs == ws) $ do
    assert (vs <= ws)
    assert (vs >= ws)
    assert (ws >= vs)
    assert (ws <= vs)
    (compare vs ws === EQ)

prop_eq_neq : Property
prop_eq_neq = property $ do
  [vs,ws] <- forAll $ hlist [arrBits,arrBits]
  when (vs /= ws) $ do
    assert (vs < ws || ws < vs)

prop_lt : Property
prop_lt = property $ do
  [vs,ws] <- forAll $ hlist [arrBits,arrBits]
  ((vs < ws) === (ws > vs))
  when (vs < ws) $ do
    assert (vs /= ws)
    assert (vs <= ws)
    assert (ws >= vs)

prop_lte : Property
prop_lte = property $ do
  [vs,ws] <- forAll $ hlist [arrBits,arrBits]
  ((vs <= ws) === (ws >= vs))

prop_map_id : Property
prop_map_id = property $ do
  vs <- forAll arrBits
  vs === map id vs

prop_from_to_list : Property
prop_from_to_list = property $ do
  vs <- forAll (list (linear 0 10) anyBits8)
  toList (Array.fromList vs) === vs

prop_from_to_vect : Property
prop_from_to_vect = property $ do
  vs <- forAll (vect 20 anyBits8)
  toVect (array vs) === vs

prop_from_to_rev_vect : Property
prop_from_to_rev_vect = property $ do
  vs <- forAll (vect 20 anyBits8)
  toVect (revArray vs) === reverse vs

prop_foldl : Property
prop_foldl = property $ do
  vs <- forAll arrBits
  foldl (:<) [<] vs === foldl (:<) [<] (toList vs)

prop_foldr : Property
prop_foldr = property $ do
  vs <- forAll arrBits
  foldr (::) Prelude.Nil vs === foldr (::) [] (toList vs)

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

prop_foldrKV : Property
prop_foldrKV = property1 $
  foldrKV (\x,v,vs => (x,v) :: vs) [] (array ["a","b","c"]) ===
  (the (List (Fin 3, String)) [(0,"a"), (1,"b"), (2,"c")])

prop_foldlKV : Property
prop_foldlKV = property1 $
  foldlKV (\x,sv,v => sv :< (x,v)) [<] (array ["a","b","c"]) ===
  [<(0,"a"), (1,"b"), (2,"c")]

prop_traverse_id : Property
prop_traverse_id = property $ do
  x <- forAll arrBits
  traverse Id x === Id x

prop_append : Property
prop_append = property $ do
  [x,y] <- forAll $ hlist [arrBits,arrBits]
  toList (x <+> y) === (toList x ++ toList y)

prop_semigroup_assoc : Property
prop_semigroup_assoc = property $ do
  [x,y,z] <- forAll $ hlist [arrBits,arrBits,arrBits]
  (x <+> (y <+> z)) === ((x <+> y) <+> z)

prop_monoid_left_neutral : Property
prop_monoid_left_neutral = property $ do
  x <- forAll arrBits
  (empty <+> x) === x

prop_monoid_right_neutral : Property
prop_monoid_right_neutral = property $ do
  x <- forAll arrBits
  (x <+> empty) === x

casWriteGet :
     (r : MArray' t 3 a)
  -> (pre,new : a)
  -> F1 [r] (Bool,a)
casWriteGet r pre new t =
  let b # t := casset r 2 pre new t
      v # t := Core.get r 2 t
   in (b,v) # t

prop_casset : Property
prop_casset =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    (True,y) === alloc 3 x (\r => casWriteGet r x y)

prop_casset_diff : Property
prop_casset_diff =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    (False,x) === alloc 3 x (\r => casWriteGet r (x+1) y)

prop_casupdate : Property
prop_casupdate =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    x === alloc 3 x (\r => casupdate r 2 (\v => (v+y,v)))

prop_casmodify : Property
prop_casmodify =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    (x+y) === alloc 3 x (\r,t => let _ # t := casmodify r 2 (+y) t in get r 2 t)

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
  , ("prop_from_to_vect", prop_from_to_vect)
  , ("prop_from_to_rev_vect", prop_from_to_rev_vect)
  , ("prop_foldl", prop_foldl)
  , ("prop_foldr", prop_foldr)
  , ("prop_null", prop_null)
  , ("prop_size", prop_size)
  , ("prop_generate", prop_generate)
  , ("prop_iterate", prop_iterate)
  , ("prop_filter", prop_filter)
  , ("prop_mapMaybe", prop_mapMaybe)
  , ("prop_foldrKV", prop_foldrKV)
  , ("prop_foldlKV", prop_foldlKV)
  , ("prop_traverse_id", prop_traverse_id)
  , ("prop_append", prop_append)
  , ("prop_semigroup_assoc", prop_semigroup_assoc)
  , ("prop_monoid_left_neutral", prop_monoid_left_neutral)
  , ("prop_monoid_right_neutral", prop_monoid_right_neutral)
  , ("prop_casset", prop_casset)
  , ("prop_casset_diff", prop_casset_diff)
  , ("prop_casupdate", prop_casupdate)
  , ("prop_casmodify", prop_casmodify)
  ]

