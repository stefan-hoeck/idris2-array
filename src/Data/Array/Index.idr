module Data.Array.Index

import public Data.Fin
import public Data.Nat

%default total

export
0 ltLemma : (0 k,m,n : Nat) -> k + S m === n -> LT k n
ltLemma 0     m (S m) Refl = %search
ltLemma (S k) m (S n) prf  = LTESucc $ ltLemma k m n (injective prf)
ltLemma (S k) m 0     prf  = absurd prf

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

export
0 ixLemma : (x : Ix m n) -> ixToNat x + m === n
ixLemma IZ     = Refl
ixLemma (IS v) = trans (plusSuccRightSucc _ _) $ ixLemma v

export
0 ixLT : (x : Ix (S m) n) -> LT (ixToNat x) n
ixLT s = ltLemma _ _ _ $ ixLemma s

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


public export
0 lteOpReflectsLTE : (m,n : Nat) -> (m <= n) === True -> LTE m n
lteOpReflectsLTE 0     (S k) prf = LTEZero
lteOpReflectsLTE (S k) (S j) prf = LTESucc (lteOpReflectsLTE k j prf)
lteOpReflectsLTE 0 0         prf = LTEZero
lteOpReflectsLTE (S k) 0     prf impossible
