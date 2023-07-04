module Main

import Array
import Index
import Hedgehog

%default total

main : IO ()
main = test
  [ Array.props
  , Index.props
  ]
