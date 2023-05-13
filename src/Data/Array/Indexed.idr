module Data.Array.Indexed

import public Data.Array.Mutable
import Data.List

%default total

--------------------------------------------------------------------------------
--          Accessing Data
--------------------------------------------------------------------------------

export %inline
ix : Array n a -> (0 m : Nat) -> {auto x: Ix (S m) n} -> a
ix arr _ = at arr (ixToNat x) @{ixLT x}

export %inline
atFin : Array n a -> Fin n -> a
atFin arr x = at arr (finToNat x) @{finLT x}

--------------------------------------------------------------------------------
--          Initializing Arrays
--------------------------------------------------------------------------------

export
empty : Array 0 a
empty = believe_me $ unrestricted $ alloc 0 () freeze

export
array : (ls : List a) -> Array (length ls) a
array []        = empty
array (x :: xs) = unrestricted $ allocList (x::xs) freeze

export
generate : (n : Nat) -> ((m : Nat) -> {auto 0 lt : LT m n} -> a) -> Array n a
generate 0     f = empty
generate (S k) f = unrestricted $ allocGen (S k) f freeze

export
iterate : (n : Nat) -> (a -> a) -> a -> Array n a
iterate 0     _ _ = empty
iterate (S k) f v = unrestricted $ allocIter (S k) f v freeze

--------------------------------------------------------------------------------
--          Eq and Ord
--------------------------------------------------------------------------------

||| Lexicographic comparison of Arrays of distinct length
export
hcomp : {m,n : Nat} -> Ord a => Array m a -> Array n a -> Ordering
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
heq : {m,n : Nat} -> Eq a => Array m a -> Array n a -> Bool
heq a1 a2 = go m n
  where
    go : (k,l : Nat) -> {auto _ : Ix k m} -> {auto _ : Ix l n} -> Bool
    go 0     0     = True
    go (S k) (S j) = if ix a1 k == ix a2 j then go k j else False
    go _     _     = False

export
{n : Nat} -> Eq a => Eq (Array n a) where
  a1 == a2 = go n
    where
      go : (k : Nat) -> {auto _ : Ix k n} -> Bool
      go 0     = True
      go (S k) = if ix a1 k == ix a2 k then go k else False

export
{n : Nat} -> Ord a => Ord (Array n a) where
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

ontoList : List a -> (m : Nat) -> {auto 0 lte : LTE m n} -> Array n a -> List a
ontoList xs 0     arr = xs
ontoList xs (S k) arr = ontoList (at arr k :: xs) k arr

foldrI : (m : Nat) -> (0 _ : LTE m n) => (e -> a -> a) -> a -> Array n e -> a
foldrI 0     _ x arr = x
foldrI (S k) f x arr = foldrI k f (f (at arr k) x) arr

foldlI : (m : Nat) -> (x : Ix m n) => (a -> e -> a) -> a -> Array n e -> a
foldlI 0     _ v arr = v
foldlI (S k) f v arr = foldlI k f (f v (ix arr k)) arr

export %inline
{n : Nat} -> Foldable (Array n) where
  foldr = foldrI n
  foldl = foldlI n
  toList = ontoList [] n
  null _ = n == Z

export %inline
{n : Nat} -> Functor (Array n) where
  map f arr = generate n (\x => f (at arr x))

export
{n : Nat} -> Show a => Show (Array n a) where
  showPrec p arr = showCon p "array" (showArg $ ontoList [] n arr)

main : IO ()
main = do
  putStrLn "Please enter a natural number:"
  n <- cast {to = Nat} <$> getLine
  printLn . count id $ generate n (\x => cast x `mod` 3 == 0)
