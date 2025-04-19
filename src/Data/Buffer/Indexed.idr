module Data.Buffer.Indexed

import public Data.Array.Index
import public Data.Array.Indexed
import Data.Buffer.Mutable
import Data.List
import Data.Vect
import Syntax.PreorderReasoning

%default total

--------------------------------------------------------------------------------
--          Accessing Data
--------------------------------------------------------------------------------

||| Safely access a value in an array at position `n - m`.
export %inline
ix : IBuffer n -> (0 m : Nat) -> {auto x: Ix (S m) n} -> Bits8
ix arr _ = at arr (ixToFin x)

||| Safely access a value in an array at the given position.
export %inline
atNat : IBuffer n -> (m : Nat) -> {auto 0 lt : LT m n} -> Bits8
atNat arr x = at arr (natToFinLT x)

||| Safely access a value at the given byte position.
export %inline
atByte : IBuffer 256 -> Bits8 -> Bits8
atByte arr x = at arr (bits8ToFin x)

--------------------------------------------------------------------------------
--          Initializing Arrays
--------------------------------------------------------------------------------

||| The empty array.
export
empty : IBuffer 0
empty = alloc 0 unsafeFreeze

||| Copy the values in a list to an array of the same length.
export %inline
bufferL : (ls : List Bits8) -> IBuffer (length ls)
bufferL xs =
  alloc (length xs) $ \r,t =>
    let _ # t := writeList {xs} r xs t
     in unsafeFreeze r t

||| Copy the values in a vector to an array of the same length.
export %inline
buffer : {n : _} -> Vect n Bits8 -> IBuffer n
buffer xs =
  alloc n $ \r,t =>
    let _ # t := writeVect r xs t
     in unsafeFreeze r t

||| Copy the values in a vector to an array of the same length
||| in reverse order.
|||
||| This is useful the values in the array have been collected
||| from tail to head for instance when parsing some data.
export %inline
revBuffer : {n : _} -> Vect n Bits8 -> IBuffer n
revBuffer xs =
  alloc n $ \r,t =>
    let _ # t := writeVectRev r n xs t
     in unsafeFreeze r t

||| Generate an immutable array of the given size using
||| the given iteration function.
export %inline
generate : (n : Nat) -> (Fin n -> Bits8) -> IBuffer n
generate n f =
  alloc n $ \r,t =>
    let _ # t := genFrom r n f t
     in unsafeFreeze r t

||| Fill an immutable array of the given size with the given value
export %inline
fill : (n : Nat) -> Bits8 -> IBuffer n
fill n = generate n . const

||| Generate an array of the given size by filling it with the
||| results of repeatedly applying `f` to the initial value.
export %inline
iterate : (n : Nat) -> (f : Bits8 -> Bits8) -> Bits8 -> IBuffer n
iterate n f v =
  alloc n $ \r,t =>
    let _ # t := iterateFrom r n f v t
     in unsafeFreeze r t

||| Copy the content of a byte array to a new array.
|||
||| This is mainly useful for reducing memory consumption, in case the
||| original array is actually backed by a much larger array, for
||| instance after taking a smalle prefix of a large array with `take`.
export
force : {n : _} -> IBuffer n -> IBuffer n
force buf = run1 $ \t => let r # t := thaw buf t in unsafeFreeze r t

--------------------------------------------------------------------------------
--          Eq and Ord
--------------------------------------------------------------------------------

||| Lexicographic comparison of Arrays of distinct length
export
hcomp : {m,n : Nat} -> IBuffer m -> IBuffer n -> Ordering
hcomp a1 a2 = go m n

  where
    go : (k,l : Nat) -> {auto _ : Ix k m} -> {auto _ : Ix l n} -> Ordering
    go 0     0     = EQ
    go 0     (S _) = LT
    go (S _) 0     = GT
    go (S k) (S j) = case compare (ix a1 k) (ix a2 j) of
      EQ => go k j
      r  => r

||| Heterogeneous equality for Arrays
export
heq : {m,n : Nat} -> IBuffer m -> IBuffer n -> Bool
heq a1 a2 = go m n

  where
    go : (k,l : Nat) -> {auto _ : Ix k m} -> {auto _ : Ix l n} -> Bool
    go 0     0     = True
    go (S k) (S j) = if ix a1 k == ix a2 j then go k j else False
    go _     _     = False

export
{n : Nat} -> Eq (IBuffer n) where
  a1 == a2 = go n

    where
      go : (k : Nat) -> {auto 0 _ : LTE k n} -> Bool
      go 0     = True
      go (S k) = if atNat a1 k == atNat a2 k then go k else False

export
{n : Nat} -> Ord (IBuffer n) where
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

ontoList :
     List Bits8
  -> (m : Nat)
  -> {auto 0 lte : LTE m n}
  -> IBuffer n
  -> List Bits8
ontoList xs 0     arr = xs
ontoList xs (S k) arr = ontoList (atNat arr k :: xs) k arr

ontoVect :
     Vect k Bits8
  -> (m : Nat)
  -> {auto 0 lte : LTE m n}
  -> IBuffer n
  -> Vect (k + m) Bits8
ontoVect xs 0     arr = rewrite plusZeroRightNeutral k in xs
ontoVect xs (S v) arr =
  rewrite sym (plusSuccRightSucc k v) in ontoVect (atNat arr v :: xs) v arr

ontoVectWithIndex :
     Vect k (Fin n, Bits8)
  -> (m : Nat)
  -> {auto 0 lte : LTE m n}
  -> IBuffer n
  -> Vect (k + m) (Fin n, Bits8)
ontoVectWithIndex xs 0     arr = rewrite plusZeroRightNeutral k in xs
ontoVectWithIndex xs (S v) arr =
  rewrite sym (plusSuccRightSucc k v)
  in let x := natToFinLT v in ontoVectWithIndex ((x, at arr x) :: xs) v arr

||| Convert an array to a vector of the same length.
export %inline
toVect : {n : _} -> IBuffer n -> Vect n Bits8
toVect = ontoVect [] n

||| Convert an array to a vector of the same length
||| pairing all values with their index.
export %inline
toVectWithIndex : {n : _} -> IBuffer n -> Vect n (Fin n, Bits8)
toVectWithIndex = ontoVectWithIndex [] n

foldr_ :
     (m : Nat)
  -> {auto 0 _ : LTE m n}
  -> (Bits8 -> a -> a)
  -> a
  -> IBuffer n
  -> a
foldr_ 0     _ x arr = x
foldr_ (S k) f x arr = foldr_ k f (f (atNat arr k) x) arr

||| Right fold over the values of a byte array plus their indices.
export %inline
foldr : {n : _} -> (Bits8 -> a -> a) -> a -> IBuffer n -> a
foldr = foldr_ n

export %inline
toList : {n : _} -> IBuffer n -> List Bits8
toList = foldr (::) Nil

foldrKV_ :
     (m : Nat)
  -> {auto 0 prf : LTE m n}
  -> (Fin n -> Bits8 -> a -> a)
  -> a
  -> IBuffer n
  -> a
foldrKV_ 0     _ x arr = x
foldrKV_ (S k) f x arr =
  let fin := natToFinLT k @{prf} in foldrKV_ k f (f fin (at arr fin) x) arr

||| Right fold over the values of a byte array plus their indices.
export %inline
foldrKV : {n : _} -> (Fin n -> Bits8 -> a -> a) -> a -> IBuffer n -> a
foldrKV = foldrKV_ n

foldl_ :
     (m : Nat)
  -> {auto x : Ix m n}
  -> (a -> Bits8 -> a)
  -> a
  -> IBuffer n
  -> a
foldl_ 0     _ v arr = v
foldl_ (S k) f v arr = foldl_ k f (f v (ix arr k)) arr

||| Left fold over the values of a byte array.
export %inline
foldl : {n : _} -> (a -> Bits8 -> a) -> a -> IBuffer n -> a
foldl = foldl_ n

export %inline
toSnocList : {n : _} -> IBuffer n -> SnocList Bits8
toSnocList = foldl (:<) Lin

foldlKV_ :
     (m : Nat)
  -> {auto x : Ix m n}
  -> (Fin n -> a -> Bits8 -> a)
  -> a
  -> IBuffer n
  -> a
foldlKV_ 0     _ v arr = v
foldlKV_ (S k) f v arr =
  let fin := ixToFin x in foldlKV_ k f (f fin v (at arr fin)) arr

||| Left fold over the values of a byte array plus their indices.
export %inline
foldlKV : {n : _} -> (Fin n -> a -> Bits8 -> a) -> a -> IBuffer n -> a
foldlKV = foldlKV_ n

export
{n : Nat} -> Show (IBuffer n) where
  showPrec p arr = showCon p "buffer" (showArg $ ontoList [] n arr)

||| Mapping over the values of an array together with their indices.
export %inline
mapWithIndex : {n : _} -> (Fin n -> Bits8 -> Bits8) -> IBuffer n -> IBuffer n
mapWithIndex f arr = generate n (\x => f x (at arr x))

||| Mapping over the values of an array together with their indices.
export %inline
map : {n : _} -> (Bits8 -> Bits8) -> IBuffer n -> IBuffer n
map f arr = generate n (f . at arr)

||| Update a single position in an array by applying the given
||| function.
|||
||| This will have to copy the whol array, so it runs in O(n).
export
updateAt : {n : _} -> Fin n -> (Bits8 -> Bits8) -> IBuffer n -> IBuffer n
updateAt x f = mapWithIndex (\k,v => if x == k then f v else v)

||| Set a single position in an array.
|||
||| This will have to copy the whol array, so it runs in O(n).
export
setAt : {n : _} -> Fin n -> Bits8 -> IBuffer n -> IBuffer n
setAt x y = mapWithIndex (\k,v => if x == k then y else v)

--------------------------------------------------------------------------------
--          Traversals
--------------------------------------------------------------------------------

||| Effectful traversal of the values in a graph together with
||| their corresponding indices.
export
traverseWithIndex :
     {n : _}
  -> {auto app : Applicative f}
  -> (Fin n -> Bits8 -> f Bits8)
  -> IBuffer n
  -> f (IBuffer n)
traverseWithIndex f arr =
  buffer <$> traverse (\(x,v) => f x v) (toVectWithIndex arr)

export %inline
traverse :
     {n : _}
  -> {auto app : Applicative f}
  -> (Bits8 -> f Bits8)
  -> IBuffer n
  -> f (IBuffer n)
traverse = traverseWithIndex . const

--------------------------------------------------------------------------------
--          Concatenation
--------------------------------------------------------------------------------

||| Concatenate two byte arrays. TODO: Test this
export
append : {m,n : _} -> IBuffer m -> IBuffer n -> IBuffer (m + n)
append src1 src2 =
  alloc (m+n) $ \r,t =>
    let _ # t := icopy {n = m+n} src1 0 0 m @{reflexive} @{lteAddRight _} r t
        _ # t := icopy src2 0 m n @{reflexive} @{reflexive} r t
     in unsafeFreeze r t
