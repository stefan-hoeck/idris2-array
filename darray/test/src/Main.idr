module Main

import DArray
import DArray.Large
import Hedgehog

%default total

main : IO ()
main = test [DArray.props]
