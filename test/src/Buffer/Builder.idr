module Buffer.Builder

import Data.Bits
import Data.Buffer.Builder
import Data.Buffer.Indexed
import Data.List.Quantifiers
import Hedgehog
import Syntax.T1

%default total

anyBuffer : Gen AnyBuffer
anyBuffer = pack <$> list (linear 0 40) anyBits8

appAll : (forall q . Builder q => a -> F1' q) -> List a -> List Bits8
appAll app ls = withBuilder (go ls)
  where
    go : Builder q => List a -> F1 q (List Bits8)
    go []      t = let ab # t := getBytes t in unpack ab # t
    go (x::xs) t = let _ # t := app x t in go xs t

bits16le : Bits16 -> List Bits8
bits16le v = [cast v, cast $ shiftR v 8]

bits32le : Bits32 -> List Bits8
bits32le v = bits16le (cast v) ++ bits16le (cast $ shiftR v 16)

bits64le : Bits64 -> List Bits8
bits64le v = bits32le (cast v) ++ bits32le (cast $ shiftR v 32)

prop_fastConcat : Property
prop_fastConcat =
  property $ Prelude.do
    bs <- forAll (list (linear 0 20) anyBuffer)
    fastConcat bs === pack (bs >>= unpack)

prop_append : Property
prop_append =
  property $ Prelude.do
    [x,y] <- forAll $ hlist [anyBuffer,anyBuffer]
    fastConcat [x,y] === (x <+> y)

prop_bits16le : Property
prop_bits16le =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyBits16
    appAll putBits16LE bs === (bs >>= bits16le)

prop_bits16be : Property
prop_bits16be =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyBits16
    appAll putBits16BE bs === (bs >>= reverse . bits16le)

prop_bits32le : Property
prop_bits32le =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyBits32
    appAll putBits32LE bs === (bs >>= bits32le)

prop_bits32be : Property
prop_bits32be =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyBits32
    appAll putBits32BE bs === (bs >>= reverse . bits32le)

prop_bits64le : Property
prop_bits64le =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyBits64
    appAll putBits64LE bs === (bs >>= bits64le)

prop_bits64be : Property
prop_bits64be =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyBits64
    appAll putBits64BE bs === (bs >>= reverse . bits64le)

prop_int16le : Property
prop_int16le =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyInt16
    appAll putInt16LE bs === (bs >>= bits16le . cast)

prop_int16be : Property
prop_int16be =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyInt16
    appAll putInt16BE bs === (bs >>= reverse . bits16le . cast)

prop_int32le : Property
prop_int32le =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyInt32
    appAll putInt32LE bs === (bs >>= bits32le . cast)

prop_int32be : Property
prop_int32be =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyInt32
    appAll putInt32BE bs === (bs >>= reverse . bits32le . cast)

prop_int64le : Property
prop_int64le =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyInt64
    appAll putInt64LE bs === (bs >>= bits64le . cast)

prop_int64be : Property
prop_int64be =
  property $ Prelude.do
    bs <- forAll $ list (linear 0 30) anyInt64
    appAll putInt64BE bs === (bs >>= reverse . bits64le . cast)

export
props : Group
props =
  MkGroup "buffer-builder"
    [ ("prop_fastConcat", prop_fastConcat)
    , ("prop_append", prop_append)
    , ("prop_bits16le", prop_bits16le)
    , ("prop_bits16be", prop_bits16be)
    , ("prop_bits32le", prop_bits32le)
    , ("prop_bits32be", prop_bits32be)
--    , ("prop_bits64le", prop_bits64le)
--    , ("prop_bits64be", prop_bits64be)
    , ("prop_int16le", prop_int16le)
    , ("prop_int16be", prop_int16be)
    , ("prop_int32le", prop_int32le)
    , ("prop_int32be", prop_int32be)
--    , ("prop_int64le", prop_int64le)
--    , ("prop_int64be", prop_int64be)
    ]
