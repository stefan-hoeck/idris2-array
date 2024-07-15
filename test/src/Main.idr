module Main

import Array.Manual
import Array
import Buffer
import Index
import Hedgehog

%default total

main : IO ()
main = test
  [ Array.Manual.props
  , Array.props
  , Index.props
  , Buffer.props
  ]
