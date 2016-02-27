module Lib
    ( someFunc
    ) where
import Kernel.Name

someFunc :: IO ()
someFunc = print $ mk_name ["rec","eq"]
