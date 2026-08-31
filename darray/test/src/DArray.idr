module DArray

import Data.DArray
import Data.Finite
import Data.List.Elem
import Data.List.Quantifiers
import Data.Vect
import Derive.Finite
import Derive.HDecEq
import Derive.Prelude
import Hedgehog

%language ElabReflection
%default total

data MyTyp : Type where
  ABool   : MyTyp
  ANat    : MyTyp
  AString : MyTyp
  AMaybe  : MyTyp
  AList   : MyTyp

%runElab derive "MyTyp" [Show,Eq,Ord,Finite,HDecEq]

public export
0 Typ : MyTyp -> Type
Typ ABool   = Bool
Typ ANat    = Nat
Typ AString = String
Typ AMaybe  = Maybe Bits8
Typ AList   = List Integer

export
0 allInValues : (v : MyTyp) -> Elem v Finite.values

export
0 allLT : (v : MyTyp) -> lt (cast $ conIndexMyTyp v) 5 === True

export %inline
Enum MyTyp 5 where
  toFin x = natToFinLT (cast $ conIndexMyTyp x) @{ltReflectsLT _ _ $ allLT x}

eqs : DArray MyTyp (Eq . Typ)
eqs =
  darray _ _ values allInValues $ \case
    ABool   => %search
    ANat    => %search
    AString => %search
    AMaybe  => %search
    AList   => %search

ords : DArray MyTyp (Ord . Typ)
ords =
  darray _ _ values allInValues $ \case
    ABool   => %search
    ANat    => %search
    AString => %search
    AMaybe  => %search
    AList   => %search

shows : DArray MyTyp (Show . Typ)
shows =
  darray _ _ values allInValues $ \case
    ABool   => %search
    ANat    => %search
    AString => %search
    AMaybe  => %search
    AList   => %search

myTyps : Gen MyTyp
myTyps = element (fromList values)

gens : DArray MyTyp (Gen . Typ)
gens =
  darray _ _ values allInValues $ \case
    ABool   => bool
    ANat    => nat (linear 0 100)
    AString => string (linear 0 20) printableAscii
    AMaybe  => maybe anyBits8
    AList   => list (linear 0 20) (integer $ linear 0 100)

Eq (v ** Typ v) where
  (x ** vx) == (y ** vy) =
    case hdecEq x y of
      Nothing0 => False
      Just0 p  => let i := at eqs x in vx == (rewrite p in vy)

Show (v ** Typ v) where
  show (x ** vx) = "(\{show x} ** \{show @{at shows x} vx})"

dpairs : Gen (v ** Typ v)
dpairs = Prelude.do
  x <- myTyps
  MkDPair x <$> at gens x

prop_eq_refl : Property
prop_eq_refl =
  property $ Prelude.do
    dp <- forAll dpairs
    dp === dp

prop_eq_sym : Property
prop_eq_sym =
  property $ Prelude.do
    [x,y] <- forAll $ hlist [dpairs, dpairs]
    (x == y) === (y == x)

export
props : Group
props =
  MkGroup "Data.DArray"
    [ ("prop_eq_refl", prop_eq_refl)
    , ("prop_eq_sym", prop_eq_sym)
    ]

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

allInValues ABool   = %search
allInValues ANat    = %search
allInValues AString = %search
allInValues AMaybe  = %search
allInValues AList   = %search

allLT ABool   = Refl
allLT ANat    = Refl
allLT AString = Refl
allLT AMaybe  = Refl
allLT AList   = Refl
