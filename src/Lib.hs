module Lib
    ( someFunc
    ) where
import Kernel.Name
import Kernel.Level

someFunc :: IO ()
someFunc = print $ mk_name ["eq","rec"]
