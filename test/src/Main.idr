module Main

import All.Manual
import All
import Array.Manual
import Array
import Buffer.Manual
import Buffer
import Index
import Hedgehog

%default total

main : IO ()
main = test
  [ All.props
  , All.Manual.props
  , Array.Manual.props
  , Array.props
  , Index.props
  , Buffer.Manual.props
  , Buffer.props
  ]
