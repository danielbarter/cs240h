module Lib
    ( someFunc
    ) where
import Kernel.Name
import Kernel.Level

someFunc :: IO ()
someFunc = print $ mkName ["eq","rec"]
