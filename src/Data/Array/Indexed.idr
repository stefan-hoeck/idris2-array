module Data.Array.Indexed

import Data.Array.Mutable
import Data.List
import Data.Vect
import Data.Linear.Traverse1
import Syntax.PreorderReasoning
import Syntax.T1

%default total

||| An immutable array paired with its size (= number of values).
|||
||| This is the dependent pair version of `IArray size a`.
public export
record Array a where
  constructor A
  size : Nat
  arr  : IArray size a

--------------------------------------------------------------------------------
--          Accessing Data
--------------------------------------------------------------------------------

||| Safely access a value in an immutable array at position `n - m`.
export %inline
ix : IArray n a -> (0 m : Nat) -> {auto x: Ix (S m) n} -> a
ix arr _ = at arr (ixToFin x)

||| Safely access a value in an array at the given position.
export %inline
atNat : IArray n a -> (m : Nat) -> {auto 0 lt : LT m n} -> a
atNat arr x = at arr (natToFinLT x)

--------------------------------------------------------------------------------
--          Initializing Arrays
--------------------------------------------------------------------------------

||| The empty array.
export %inline
empty : IArray 0 a
empty = unsafeAlloc 0 unsafeFreeze

||| Copy the values in a list to an immutable array of the same length.
export %inline
arrayL : (ls : List a) -> IArray (length ls) a
arrayL xs = allocList xs unsafeFreeze

||| Copy the values in a vector to an immutable array of the same length.
export %inline
array : {n : _} -> Vect n a -> IArray n a
array xs = allocVect xs unsafeFreeze

||| Copy the values in a vector to an immutable array of the same length
||| in reverse order.
|||
||| This is useful if the values in the array have been collected
||| from tail to head for instance when parsing some data.
export %inline
revArray : {n : _} -> Vect n a -> IArray n a
revArray xs = allocVectRev xs unsafeFreeze

||| Fill an immutable array of the given size with the given value.
export %inline
fill : (n : Nat) -> a -> IArray n a
fill n v = alloc n v unsafeFreeze

||| Generate an immutable array of the given size using
||| the given iteration function.
export %inline
generate : (n : Nat) -> (Fin n -> a) -> IArray n a
generate n f = allocGen n f unsafeFreeze

||| Generate an immutable array of the given size by filling it with the
||| results of repeatedly applying `f` to the initial value.
export %inline
iterate : (n : Nat) -> (f : a -> a) -> a -> IArray n a
iterate n f v = allocIter n f v unsafeFreeze

||| Copy the content of an array to a new immutable array.
|||
||| This is mainly useful for reducing memory consumption, in case the
||| original array is actually backed by a much larger array, for
||| instance after taking a smaller prefix of a large array with `take`.
export
force : {n : _} -> IArray n a -> IArray n a
force arr = generate n (at arr)

||| Allocate an immutable array, fill it with the given default value, and use a list
||| of pairs to replace specific positions.
export
fromPairs : (n : Nat) -> a -> List (Nat,a) -> IArray n a
fromPairs n v ps = alloc n v (go ps)
  where
    go : List (Nat,a) -> WithMArray n a (IArray n a)
    go []            r = unsafeFreeze r
    go ((x,v) :: xs) r =
      case tryNatToFin x of
        Just y  => T1.do set r y v; go xs r
        Nothing => go xs r

--------------------------------------------------------------------------------
--          Eq and Ord
--------------------------------------------------------------------------------

||| Lexicographic comparison of immutable arrays of distinct length.
export
hcomp : {m,n : Nat} -> Ord a => IArray m a -> IArray n a -> Ordering
hcomp a1 a2 = go m n

  where
    go : (k,l : Nat) -> {auto _ : Ix k m} -> {auto _ : Ix l n} -> Ordering
    go 0     0     = EQ
    go 0     (S _) = LT
    go (S _) 0     = GT
    go (S k) (S j) = case compare (ix a1 k) (ix a2 j) of
      EQ => go k j
      r  => r

||| Heterogeneous equality for immutable arrays.
export
heq : {m,n : Nat} -> Eq a => IArray m a -> IArray n a -> Bool
heq a1 a2 = go m n

  where
    go : (k,l : Nat) -> {auto _ : Ix k m} -> {auto _ : Ix l n} -> Bool
    go 0     0     = True
    go (S k) (S j) = if ix a1 k == ix a2 j then go k j else False
    go _     _     = False

export
{n : Nat} -> Eq a => Eq (IArray n a) where
  a1 == a2 = go n

    where
      go : (k : Nat) -> {auto 0 _ : LTE k n} -> Bool
      go 0     = True
      go (S k) = if atNat a1 k == atNat a2 k then go k else False

export
{n : Nat} -> Ord a => Ord (IArray n a) where
  compare a1 a2 = go n

    where
      go : (k : Nat) -> {auto _ : Ix k n} -> Ordering
      go 0     = EQ
      go (S k) = case compare (ix a1 k) (ix a2 k) of
        EQ => go k
        c  => c

--------------------------------------------------------------------------------
--          Maps and Folds
--------------------------------------------------------------------------------

ontoList : List a -> (m : Nat) -> (0 lte : LTE m n) => IArray n a -> List a
ontoList xs 0     arr = xs
ontoList xs (S k) arr = ontoList (atNat arr k :: xs) k arr

ontoVect :
     Vect k a
  -> (m : Nat)
  -> {auto 0 lte : LTE m n}
  -> IArray n a
  -> Vect (k + m) a
ontoVect xs 0     arr = rewrite plusZeroRightNeutral k in xs
ontoVect xs (S v) arr =
  rewrite sym (plusSuccRightSucc k v) in ontoVect (atNat arr v :: xs) v arr

ontoVectWithIndex :
     Vect k (Fin n, a)
  -> (m : Nat)
  -> {auto 0 lte : LTE m n}
  -> IArray n a
  -> Vect (k + m) (Fin n, a)
ontoVectWithIndex xs 0     arr = rewrite plusZeroRightNeutral k in xs
ontoVectWithIndex xs (S v) arr =
  rewrite sym (plusSuccRightSucc k v)
  in let x := natToFinLT v in ontoVectWithIndex ((x, at arr x) :: xs) v arr

||| Convert an immutable array to a vector of the same length.
export %inline
toVect : {n : _} -> IArray n a -> Vect n a
toVect = ontoVect [] n

||| Convert an immutable array to a vector of the same length
||| pairing all values with their index.
export %inline
toVectWithIndex : {n : _} -> IArray n a -> Vect n (Fin n, a)
toVectWithIndex = ontoVectWithIndex [] n

foldrI : (m : Nat) -> (0 _ : LTE m n) => (e -> a -> a) -> a -> IArray n e -> a
foldrI 0     _ x arr = x
foldrI (S k) f x arr = foldrI k f (f (atNat arr k) x) arr

foldrKV_ :
     (m : Nat)
  -> {auto 0 prf : LTE m n}
  -> (Fin n -> e -> a -> a)
  -> a
  -> IArray n e -> a
foldrKV_ 0     _ x arr = x
foldrKV_ (S k) f x arr =
  let fin := natToFinLT k @{prf} in foldrKV_ k f (f fin (at arr fin) x) arr

foldlI : (m : Nat) -> (x : Ix m n) => (a -> e -> a) -> a -> IArray n e -> a
foldlI 0     _ v arr = v
foldlI (S k) f v arr = foldlI k f (f v (ix arr k)) arr

foldlKV_ :
     (m : Nat)
  -> {auto x : Ix m n}
  -> (Fin n -> a -> e -> a)
  -> a
  -> IArray n e
  -> a
foldlKV_ 0     _ v arr = v
foldlKV_ (S k) f v arr =
  let fin := ixToFin x in foldlKV_ k f (f fin v (at arr fin)) arr

||| Right fold over the values of an immutable array plus their indices.
export %inline
foldrKV : {n : _} -> (Fin n -> e -> a -> a) -> a -> IArray n e -> a
foldrKV = foldrKV_ n

||| Left fold over the values of an immutable array plus their indices.
export %inline
foldlKV : {n : _} -> (Fin n -> a -> e -> a) -> a -> IArray n e -> a
foldlKV = foldlKV_ n

export %inline
{n : Nat} -> Foldable (IArray n) where
  foldr = foldrI n
  foldl = foldlI n
  toList = ontoList [] n
  null _ = n == Z

export %inline
{n : Nat} -> Functor (IArray n) where
  map f arr = generate n (f . at arr)

export
{n : Nat} -> Applicative (IArray n) where
  pure = fill n
  af <*> av = generate n (\x => at af x (at av x))

export
{n : Nat} -> Monad (IArray n) where
  arr >>= f = generate n (\x => at (f $ at arr x) x)

export
{n : Nat} -> Show a => Show (IArray n a) where
  showPrec p arr = showCon p "array" (showArg $ ontoList [] n arr)

||| Mapping over the values of an immutable array together with their indices.
export
mapWithIndex : {n : _} -> (Fin n -> a -> b) -> IArray n a -> IArray n b
mapWithIndex f arr = generate n (\x => f x (at arr x))

||| Update a single position in an immutable array by applying the given
||| function.
|||
||| This will have to copy the whole array, so it runs in O(n).
export
updateAt : {n : _} -> Fin n -> (a -> a) -> IArray n a -> IArray n a
updateAt x f = mapWithIndex (\k,v => if x == k then f v else v)

||| Set a single position in an immutable array.
|||
||| This will have to copy the whole array, so it runs in O(n).
export
setAt : {n : _} -> Fin n -> a -> IArray n a -> IArray n a
setAt x y = mapWithIndex (\k,v => if x == k then y else v)

--------------------------------------------------------------------------------
--          Traversals
--------------------------------------------------------------------------------

||| Effectful traversal of the values in an immutable array together with
||| their corresponding indices.
export
traverseWithIndex :
     {n : _}
  -> {auto app : Applicative f}
  -> (Fin n -> a -> f b)
  -> IArray n a
  -> f (IArray n b)
traverseWithIndex f arr =
  array <$> traverse (\(x,v) => f x v) (toVectWithIndex arr)

export
{n : _} -> Traversable (IArray n) where
  traverse = traverseWithIndex . const

--------------------------------------------------------------------------------
--          Sub-Arrays
--------------------------------------------------------------------------------

0 curLTE : (s : Ix m n) -> LTE c (ixToNat s) -> LTE c n
curLTE s lte = transitive lte $ ixLTE s

0 curLT : (s : Ix (S m) n) -> LTE c (ixToNat s) -> LT c n
curLT s lte = let LTESucc p := ixLT s in LTESucc $ transitive lte p

||| Drop n elements from a immutable array. O(n)
export
drop : {n : _} -> (m : Nat) -> IArray n a -> IArray (n `minus` m) a
drop m arr = generate (n `minus` m) (\f => at arr (inc f))

||| Filter the values in an immutable array together with their corresponding
||| indices according to the given predicate.
export
filterWithKey :
     {n : Nat}
  -> (Fin n -> a -> Bool)
  -> IArray n a
  -> Array a
filterWithKey f arr = run1 $ T1.do
  (n ** m) <- mfilterWithKey (unsafeThaw arr) f
  res      <- unsafeFreeze m
  pure (A n res)

||| Filters the values in an immutable array according to the given predicate.
export %inline
filter : {n : Nat} -> (a -> Bool) -> IArray n a -> Array a
filter = filterWithKey . const

||| Map the values in an immutable array together with their corresponding indices
||| over a function that might not return a result for all values.
export
mapMaybeWithKey :
     {n : Nat}
  -> (Fin n -> a -> Maybe b)
  -> IArray n a
  -> Array b
mapMaybeWithKey f arr = run1 $ T1.do
  (n ** m) <- mmapMaybeWithKey (unsafeThaw arr) f
  res      <- unsafeFreeze m
  pure (A n res)

||| Map the values in an immutable array together with their corresponding indices
||| over a function that might not return a result for all values.
export %inline
mapMaybe : {n : Nat} -> (a -> Maybe b) -> IArray n a -> Array b
mapMaybe = mapMaybeWithKey . const

--------------------------------------------------------------------------------
--          Concatenating Arrays
--------------------------------------------------------------------------------

||| Size of an array after concatenating a SnocList of arrays.
|||
||| It is easier to implement this and keep the indices correct,
||| therefore, this is the default for concatenating arrays.
public export
SnocSize : SnocList (Array a) -> Nat
SnocSize [<]           = 0
SnocSize (xs :< A s _) = SnocSize xs + s

||| Size of an immutable array after concatenating a List of arrays.
public export
ListSize : List (Array a) -> Nat
ListSize = SnocSize . ([<] <><)

-- snocConcat implementation
sconc :
     (pos         : Nat)
  -> (cur         : Nat)
  -> (x           : IArray m a)
  -> (arrs        : SnocList (Array a))
  -> {auto 0 lte1 : LTE pos n}
  -> {auto 0 lte2 : LTE cur m}
  -> WithMArray n a (IArray n a)
sconc pos   0     _   (sx :< A s x) r t = sconc pos s x   sx r t
sconc (S j) (S k) x   sx            r t =
  let _ # t := setNat r j (atNat x k) t
   in sconc j k x sx r t
sconc _     _     _   _             r t = unsafeFreeze r t

||| Concatenate a SnocList of arrays.
|||
||| This allocates a large enough array in advance, and therefore runs in
||| O(SnocSize sa).
export
snocConcat : (sa : SnocList (Array a)) -> IArray (SnocSize sa) a
snocConcat [<]                 = empty
snocConcat (sa :< A 0 _)       =
  rewrite plusZeroRightNeutral (SnocSize sa) in snocConcat sa
snocConcat (sa :< A (S k) arr) with (SnocSize sa + S k)
  _ | n = alloc n (at arr 0) (sconc n (S k) arr sa)

||| Concatenate a List of arrays.
|||
||| This allocates a large enough array in advance, and therefore runs in
||| O(ListSize as).
export
listConcat : (as : List (Array a)) -> IArray (ListSize as) a
listConcat as = snocConcat ([<] <>< as)

||| Concatenate two immutable arrays in O(m+n) runtime.
export
append : {m,n : Nat} -> IArray m a -> IArray n a -> IArray (m + n) a
append src1 src2 =
  unsafeAlloc (m+n) $ \r,t =>
    let _ # t := icopy {n = m+n} src1 0 0 m @{reflexive} @{lteAddRight _} r t
        _ # t := icopy src2 0 m n @{reflexive} @{reflexive} r t
     in unsafeFreeze r t

--------------------------------------------------------------------------------
--          Linear Folds and Traversals
--------------------------------------------------------------------------------

parameters (arr : IArray n e)

  foldl1A : (k : Nat) -> Ix k n => (a -> e -> F1 s a) -> a -> F1 s a
  foldl1A 0     f x t = x # t
  foldl1A (S k) f x t = let y # t := f x (arr `ix` k) t in foldl1A k f y t

  foldr1A : (k : Nat) -> (0 p : LTE k n) => (e -> a -> F1 s a) -> a -> F1 s a
  foldr1A 0     f x t = x # t
  foldr1A (S k) f x t = let y # t := f (arr `atNat` k) x t in foldr1A k f y t

  fm1A : Semigroup a => (k : Nat) -> (0 p : LTE k n) => (e -> F1 s a) -> a -> F1 s a
  fm1A 0     f x t = x # t
  fm1A (S k) f x t = let y # t := f (arr `atNat` k) t in fm1A k f (y<+>x) t

  tr1A_ : (k : Nat) -> Ix k n => (e -> F1' s) -> F1' s
  tr1A_ 0     f t = () # t
  tr1A_ (S k) f t = let _ # t := f (arr `ix` k) t in tr1A_ k f t

  tr1A : (k : Nat) -> Ix k n => (e -> F1 s b) -> MArray s n b -> F1 s (IArray n b)
  tr1A 0     f m t = unsafeFreeze m t
  tr1A (S k) f m t =
   let y # t := f (arr `ix` k) t
       _ # t := setIx m k y t
    in tr1A k f m t

||| Runs a linear effect over the values plus their indices in an array.
export
traverseKV1_ : {n : _} -> (Fin n -> a -> F1' q) -> IArray n a -> F1' q
traverseKV1_ f arr = go n
  where
    go : (k : Nat) -> (x : Ix k n) => F1' q
    go 0     t = () # t
    go (S k) t = let _ # t := f (ixToFin x) (arr `ix` k) t in go k t

export %inline
{n : _} -> Foldable1 (IArray n) where
  foldl1     f x arr = foldl1A arr n f x
  foldr1     f x arr = foldr1A arr n f x
  foldMap1   f   arr = fm1A arr n f neutral
  traverse1_ f   arr = tr1A_ arr n f

export %inline
{n : _} -> Traversable1 (IArray n) where
  traverse1 f arr = unsafeMArray1 n >>= tr1A arr n f

export %inline
Foldable1 Array where
  foldl1     f x (A n arr) = foldl1A arr n f x
  foldr1     f x (A n arr) = foldr1A arr n f x
  foldMap1   f   (A n arr) = fm1A arr n f neutral
  traverse1_ f   (A n arr) = tr1A_ arr n f

export %inline
Traversable1 Array where
  traverse1 f (A n arr) t = let a # t := traverse1 f arr t in A n a # t
