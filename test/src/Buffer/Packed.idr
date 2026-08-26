module Buffer.Packed

import Data.Buffer.Packed
import Hedgehog
import Syntax.T1

%default total

test1 : Eq a => Show a => (a, a, a, a) -> (a, a, a, a) -> Property
test1 (x1, x2, x3, x4) (y1, y2, y3, y4) =
  property1 $ do
    x1 === y1
    x2 === y2
    x3 === y3
    x4 === y4

setgetInt8 : WithPackedBuffer 4 Int8 (Int8, Int8, Int8, Int8)
setgetInt8 r = T1.do
  set r 0 (the Int8 1)
  set r 1 (the Int8 (-2))
  set r 2 (the Int8 127)
  set r 3 (the Int8 (-128))
  s1 <- get r 0
  s2 <- get r 1
  s3 <- get r 2
  s4 <- get r 3
  pure (s1, s2, s3, s4)

setgetInt16 : WithPackedBuffer 4 Int16 (Int16, Int16, Int16, Int16)
setgetInt16 r = T1.do
  set r 0 (the Int16 1)
  set r 1 (the Int16 (-2))
  set r 2 (the Int16 32767)
  set r 3 (the Int16 (-32768))
  s1 <- get r 0
  s2 <- get r 1
  s3 <- get r 2
  s4 <- get r 3
  pure (s1, s2, s3, s4)

setgetInt32 : WithPackedBuffer 4 Int32 (Int32, Int32, Int32, Int32)
setgetInt32 r = T1.do
  set r 0 (the Int32 1)
  set r 1 (the Int32 (-2))
  set r 2 (the Int32 2147483647)
  set r 3 (the Int32 (-2147483648))
  s1 <- get r 0
  s2 <- get r 1
  s3 <- get r 2
  s4 <- get r 3
  pure (s1, s2, s3, s4)

setgetInt64 : WithPackedBuffer 4 Int64 (Int64, Int64, Int64, Int64)
setgetInt64 r = T1.do
  set r 0 (the Int64 1)
  set r 1 (the Int64 (-2))
  set r 2 (the Int64 9223372036854775807)
  set r 3 (the Int64 (-9223372036854775808))
  s1 <- get r 0
  s2 <- get r 1
  s3 <- get r 2
  s4 <- get r 3
  pure (s1, s2, s3, s4)

testInt64Isolation : WithPackedBuffer 4 Int64 (Int64, Int64, Int64, Int64)
testInt64Isolation r = T1.do
  set r 0 (the Int64 111)
  set r 1 (the Int64 222)
  set r 2 (the Int64 333)
  set r 3 (the Int64 444)
  set r 1 (the Int64 999)
  s1 <- get r 0
  s2 <- get r 1
  s3 <- get r 2
  s4 <- get r 3
  pure (s1, s2, s3, s4)

export
props : Group
props =
  MkGroup "buffer-packed"
    [ ("int8", test1 (alloc 4 setgetInt8) (1, -2, 127, -128))
    , ("int16", test1 (alloc 4 setgetInt16) (1,-2, 32767, -32768))
    , ("int32", test1 (alloc 4 setgetInt32) (1,-2, 2147483647, -2147483648))
    , ("int64", test1 (alloc 4 setgetInt64) (1, -2, 9223372036854775807, -9223372036854775808))
    , ("int64Isolation", test1 (alloc 4 testInt64Isolation) (111, 999, 333, 444))
    ]
