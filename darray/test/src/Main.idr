module Main

import DArray
import TArray
import DArray.Large
import Hedgehog

%default total

main : IO ()
main = test [DArray.props,TArray.props]
