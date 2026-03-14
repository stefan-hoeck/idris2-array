module Buffer.Builder

import Data.Buffer.Builder
import Data.Buffer.Indexed
import Data.List.Quantifiers
import Hedgehog
import Syntax.T1

%default total

anyBuffer : Gen AnyBuffer
anyBuffer = pack <$> list (linear 0 40) anyBits8

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

export
props : Group
props =
  MkGroup "buffer-builder"
    [ ("prop_fastConcat", prop_fastConcat)
    , ("prop_append", prop_append)
    ]
