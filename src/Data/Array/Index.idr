module Data.Array.Index

import public Data.Fin
import public Data.Nat

%default total

-- TODO: Use `Ord` on `Fin` once #3007 got accepted
public export %inline
compFin : Fin m -> Fin n -> Ordering
compFin x y = compare (finToNat x) (finToNat y)

-- TODO: Use `Eq` on `Fin` once #3007 got accepted
public export %inline
heqFin : Fin m -> Fin n -> Bool
heqFin x y = finToNat x == finToNat y

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

public export
data Ix : (m,n : Nat) -> Type where
  IZ : Ix n n
  IS : Ix (S m) n -> Ix m n

public export
ixToNat : Ix m n -> Nat
ixToNat IZ     = 0
ixToNat (IS n) = S $ ixToNat n

public export
succIx : Ix m n -> Ix (S m) (S n)
succIx IZ     = IZ
succIx (IS x) = IS (succIx x)

public export
natToIx : (n : Nat) -> Ix 0 n
natToIx 0     = IZ
natToIx (S k) = IS $ succIx (natToIx k)

public export
natToIx1 : (n : Nat) -> Ix 1 (S n)
natToIx1 n = case natToIx (S n) of
  IS x => x

export
0 ixLemma : (x : Ix m n) -> ixToNat x + m === n
ixLemma IZ     = Refl
ixLemma (IS v) = trans (plusSuccRightSucc _ _) $ ixLemma v

export
0 ixLT : (x : Ix (S m) n) -> LT (ixToNat x) n
ixLT s = ltLemma _ _ _ $ ixLemma s

export
0 ixLTE : (x : Ix m n) -> LTE (ixToNat x) n
ixLTE s = lteLemma _ _ _ $ ixLemma s

public export
ixToFin : Ix (S m) n -> Fin n
ixToFin x = natToFinLT (ixToNat x) @{ixLT x}

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
tryNatToFin : {k : _} -> Nat -> Maybe (Fin k)
tryNatToFin n with (n < k) proof eq
  _ | True  = Just $ natToFinLT n @{ltOpReflectsLT n k eq}
  _ | False = Nothing

export %inline
tryFinToFin : {k : _} -> Fin n -> Maybe (Fin k)
tryFinToFin = tryNatToFin . finToNat
