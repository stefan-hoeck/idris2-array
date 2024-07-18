module Main

import Array.Manual
import Array
import Buffer.Manual
import Buffer
import Index
import Hedgehog

%default total

main : IO ()
main = test
  [ Array.Manual.props
  , Array.props
  , Index.props
  , Buffer.Manual.props
  , Buffer.props
  ]
