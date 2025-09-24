||| This module provides several ways to safely index into an
||| array of known size. All conversions between different index
||| types are optimized away by the compiler, because they are
||| all of the same structure during code generation: An encoding
||| of natural numbers which the Idris compiler converts to a
||| native integer representation.
|||
||| The main type for indexing into an array of size `n` is `Fin n`,
||| representing a natural number strictly smaller than `n`.
|||
||| As an alternative, we can use a natural number `k` directly, together
||| with a proof of type `LT k n`, showing that `k` is strictly smaller
||| than `n`. Such numbers can be converted directly to `Fin n` by means
||| of function `Data.Nat.natToFinLT`. This way of indexing is very
||| useful for iterating over the whole array from then end: We start
||| with `n` itself together with an erased proof of type `LTE n n`, which
||| can be generated automatically. By pattern matching on the current
||| position, we can safely access all positions in the array until
||| we arrive at 0. See the implementation of `foldr` (a private
||| function called `foldrI`) in module `Data.Array.Indexed` for an
||| example how this is used.
|||
||| It is only slightly harder to iterate over an array from the
||| front. This is where data type `Ix m n` comes into play: It's
||| another way of saying that `m <= n` holds, but it works in
||| the oposite direction than `LTE`: It's zero constructor `IZ` proofs
||| that `n <= n` for all `n`, while its successor constructor
||| proofs that from `S k <= n` follows `k <= n`. This means, that
||| for a given `k`, a values of type `Ix k n` corresponds to the
||| values `n - k`. This allows us to recurse over a natural number
||| while keeping an auto-implicit proof of type `Ix k n`, and use
||| this proof for indexing into the array.
||| See the implementation of `foldl` (a private
||| function called `foldlI`) in module `Data.Array.Indexed` for an
||| example how this is used.
module Data.Array.Index

import Data.So
import public Data.DPair
import public Data.Fin
import public Data.Maybe0
import public Data.Nat

%default total

export
0 ltLemma : (0 k,m,n : Nat) -> k + S m === n -> LT k n
ltLemma 0     m (S m) Refl = %search
ltLemma (S k) m (S n) prf  = LTESucc $ ltLemma k m n (injective prf)
ltLemma (S k) m 0     prf  = absurd prf

export
0 lteLemma : (0 k,m,n : Nat) -> k + m === n -> LTE k n
lteLemma 0     m m     Refl = %search
lteLemma (S k) m (S n) prf  = LTESucc $ lteLemma k m n (injective prf)
lteLemma (S k) m 0     prf  = absurd prf

export
0 lteSuccPlus : (k : Nat) -> LTE (S k) (k + S m)
lteSuccPlus 0     = LTESucc LTEZero
lteSuccPlus (S k) = LTESucc $ lteSuccPlus k

--------------------------------------------------------------------------------
--          Suffix
--------------------------------------------------------------------------------

public export
data Suffix : (xs,ys : List a) -> Type where
  Same   : Suffix xs xs
  Uncons : Suffix (x::xs) ys -> Suffix xs ys

public export
suffixToNat : Suffix xs ys -> Nat
suffixToNat Same       = 0
suffixToNat (Uncons x) = S $ suffixToNat x

export
0 suffixLemma : (s : Suffix xs ys) -> suffixToNat s + length xs === length ys
suffixLemma Same       = Refl
suffixLemma (Uncons x) = trans (plusSuccRightSucc _ _) $ suffixLemma x

export
0 suffixLT : (s : Suffix (x::xs) ys) -> LT (suffixToNat s) (length ys)
suffixLT s = ltLemma _ _ _ $ suffixLemma s

public export
suffixToFin : Suffix (x::xs) ys -> Fin (length ys)
suffixToFin x = natToFinLT (suffixToNat x) @{suffixLT x}

--------------------------------------------------------------------------------
--          Ix
--------------------------------------------------------------------------------

||| A data type for safely indexing into an array from the
||| front during in a fuction recursing on natural number `m`.
|||
||| This is another way to proof that `m <= n`.
public export
data Ix : (m,n : Nat) -> Type where
  IZ : Ix n n
  IS : Ix (S m) n -> Ix m n

||| O(1) conversion from `Ix m n` to `Nat`. The result equals `n - m`.
public export
ixToNat : Ix m n -> Nat
ixToNat IZ     = 0
ixToNat (IS n) = S $ ixToNat n

||| If `m <= n` then `S m <= S n`.
public export
succIx : Ix m n -> Ix (S m) (S n)
succIx IZ     = IZ
succIx (IS x) = IS (succIx x)

||| Convert a natural number to the corresponding `Ix 0 n`
||| so that `n === ixToNat (natToIx n)` as shown in
||| `ixLemma`.
public export
natToIx : (n : Nat) -> Ix 0 n
natToIx 0     = IZ
natToIx (S k) = IS $ succIx (natToIx k)

||| Convert a natural number to the corresponding `Ix 1 (S n)`,
||| the largest value strictly smaller than `S n`.
|||
||| This is similar to `Data.Fin.last`.
public export
natToIx1 : (n : Nat) -> Ix 1 (S n)
natToIx1 n = case natToIx (S n) of
  IS x => x

||| Proof that for an index `x` of type `Ix m n` `ixToNat x` equals `n - m`.
export
0 ixLemma : (x : Ix m n) -> ixToNat x + m === n
ixLemma IZ     = Refl
ixLemma (IS v) = trans (plusSuccRightSucc _ _) $ ixLemma v

||| Proof an `Ix (S m) n` corresponds to a natural number
||| strictly smaller than `n` and can therefore be used as an index
||| into an array of size `n`.
export
0 ixLT : (x : Ix (S m) n) -> LT (ixToNat x) n
ixLT s = ltLemma _ _ _ $ ixLemma s

||| Proof an `Ix m n` corresponds to a natural number
||| smaller than or equal to `n
export
0 ixLTE : (x : Ix m n) -> LTE (ixToNat x) n
ixLTE s = lteLemma _ _ _ $ ixLemma s

||| From lemma `ixLT` follows, that we can convert an `Ix (S m) n` to
||| a `Fin n` corresponding to the same natural numbers. All conversions
||| involved are optimized away by the identity optimizer during code
||| generation.
public export
ixToFin : Ix (S m) n -> Fin n
ixToFin x = natToFinLT (ixToNat x) @{ixLT x}

--------------------------------------------------------------------------------
--          Sublength
--------------------------------------------------------------------------------

export
0 finToNatLT : (x : Fin n) -> LT (finToNat x) n
finToNatLT FZ     = %search
finToNatLT (FS x) = LTESucc $ finToNatLT x

||| This type is used to cut off a portion of
||| a `ByteString`. It must be no larger than the number
||| of elements in the ByteString
public export
0 SubLength : Nat -> Type
SubLength n = Subset Nat (`LTE` n)

export %inline
sublength : (k : Nat) -> (0 lte : LTE k n) => SubLength n
sublength k = Element k lte

export %inline
fromFin : Fin n -> SubLength n
fromFin x = Element (finToNat x) (lteSuccLeft $ finToNatLT x)

export %inline
fromIx : Ix m n -> SubLength n
fromIx x = Element (ixToNat x) (ixLTE x)

--------------------------------------------------------------------------------
--          Hints
--------------------------------------------------------------------------------

export %hint
0 refl : LTE n n
refl = reflexive

export %hint
0 lsl : (p : LTE (S m) n) => LTE m n
lsl = lteSuccLeft p

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

export
0 lteOpReflectsLTE : (m,n : Nat) -> (m <= n) === True -> LTE m n
lteOpReflectsLTE 0     (S k) prf = LTEZero
lteOpReflectsLTE (S k) (S j) prf = LTESucc (lteOpReflectsLTE k j prf)
lteOpReflectsLTE 0 0         prf = LTEZero
lteOpReflectsLTE (S k) 0     prf impossible

export
0 ltOpReflectsLT : (m,n : Nat) -> (m < n) === True -> LT m n
ltOpReflectsLT 0     (S k) prf = LTESucc LTEZero
ltOpReflectsLT (S k) (S j) prf = LTESucc (ltOpReflectsLT k j prf)
ltOpReflectsLT 0 0         prf impossible
ltOpReflectsLT (S k) 0     prf impossible

export
0 eqOpReflectsEquals : (m,n : Nat) -> (m == n) === True -> m === n
eqOpReflectsEquals 0     0     prf = Refl
eqOpReflectsEquals (S k) (S j) prf = cong S $ eqOpReflectsEquals k j prf
eqOpReflectsEquals 0     (S k) prf impossible
eqOpReflectsEquals (S k) 0     prf impossible

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

export
tryLT : {n : _} -> (k : Nat) -> Maybe0 (LT k n)
tryLT k with (k < n) proof eq
  _ | True  = Just0 $ ltOpReflectsLT k n eq
  _ | False = Nothing0

export
tryLTE : {n : _} -> (k : Nat) -> Maybe0 (LTE k n)
tryLTE 0     = Just0 %search
tryLTE (S k) = tryLT k

||| Tries to convert a natural number to a `Fin k`.
export
tryNatToFin : {k : _} -> Nat -> Maybe (Fin k)
tryNatToFin n with (n < k) proof eq
  _ | True  = Just $ natToFinLT n @{ltOpReflectsLT n k eq}
  _ | False = Nothing

||| Tries to convert a `Fin n` to a `Fin k`.
export %inline
tryFinToFin : {k : _} -> Fin n -> Maybe (Fin k)
tryFinToFin = tryNatToFin . finToNat

export
0 minusLTE : (k,m : Nat) -> LTE (k `minus` m) k
minusLTE 0     m     = LTEZero
minusLTE (S k) 0     = reflexive
minusLTE (S k) (S j) = lteSuccRight $ minusLTE k j

export
0 minusFinLT : (n : Nat) -> (x : Fin n) -> LT (n `minus` S (finToNat x)) n
minusFinLT (S k) FZ = LTESucc (minusLTE k 0)
minusFinLT (S k) (FS x) = LTESucc (minusLTE k _)

export
0 minusLT : (x,m,n : Nat) -> LT x (n `minus` m) -> LT (x+m) n
minusLT x _     0     y = absurd y
minusLT x 0     (S k) y = rewrite plusZeroRightNeutral x in y
minusLT x (S k) (S j) y =
  let p1 := minusLT x k j y
   in LTESucc (rewrite sym (plusSuccRightSucc x k) in p1)

export
inc : {m : _} -> Fin (n `minus` m) -> Fin n
inc x =
  let 0 p1 := finToNatLT x
   in natToFinLT (finToNat x + m) @{minusLT _ _ _ p1}

export
0 ltAddLeft : LT k n -> LT k (m+n)
ltAddLeft {m = 0}   lt = lt
ltAddLeft {m = S x} lt = lteSuccRight $ ltAddLeft lt

export
0 lteAddLeft : (n : Nat) -> LTE n (m+n)
lteAddLeft n = rewrite plusCommutative m n in lteAddRight n

--------------------------------------------------------------------------------
--          Lemma (Drop)
--------------------------------------------------------------------------------

export
0 plusMinus : (m,n : Nat) -> LTE m n -> m + (n `minus` m) === n
plusMinus 0 0         _           = Refl
plusMinus 0 (S k)     x           = Refl
plusMinus (S k) (S j) (LTESucc p) = cong S $ plusMinus k j p
plusMinus (S k) 0     x impossible

export
0 eqLTE : (m,n : Nat) -> m === n -> LTE m n
eqLTE 0     0     Refl = LTEZero
eqLTE (S k) (S k) Refl = LTESucc $ eqLTE k k Refl

export
0 dropLemma : (k,n : Nat) -> LTE (plus (minus n (minus n k)) (minus n k)) n
dropLemma k n =
  let p1 := minusLTE n k
      p2 := plusMinus _ _ p1
      p3 := trans (plusCommutative _ _) p2
   in eqLTE _ _ p3

export
0 plusMinusLTE : (m,n : Nat) -> LTE m n -> LTE (m + (n `minus` m)) n
plusMinusLTE m n lte = eqLTE _ _ $ plusMinus m n lte

--------------------------------------------------------------------------------
--          Relations
--------------------------------------------------------------------------------

||| `Suffix` is a reflexive and transitive relation.
|||
||| Performance: This is integer addition at runtime.
public export
trans : Ix k m -> Ix m n -> Ix k n
trans IZ y     = y
trans (IS x) t = IS $ trans x t

%inline
transp : Ix k m -> Ix m n -> Ix k n
transp x y =  believe_me (ixToNat x + ixToNat y)

%transform "ixTransPlus" Index.trans = Index.transp

||| `Ix` is a reflexive relation on natural numbers.
public export %inline
Reflexive Nat Ix where
  reflexive = IZ

||| `Ix` is a transitive relation on natural numbers.
public export %inline
Transitive Nat Ix where
  transitive = trans

--------------------------------------------------------------------------------
--          Fixed-precision integers
--------------------------------------------------------------------------------

export
0 castBits8LT : (x : Bits8) -> LT (cast x) 256
castBits8LT x =
  case choose (cast {to = Nat} x < 256) of
    Left oh => Data.Nat.ltOpReflectsLT _ _ oh
    _       => assert_total $ idris_crash "Bits8 value >= 256"

||| Every `Bits8` value can be safely cast to a `Fin 256`.
export %inline
bits8ToFin : Bits8 -> Fin 256
bits8ToFin x = natToFinLT (cast x) @{castBits8LT x}
