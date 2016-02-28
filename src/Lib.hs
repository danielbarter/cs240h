module Lib
    ( someFunc
    ) where
import Kernel.Name
import Kernel.Level
import Kernel.Expr

someFunc :: IO ()
someFunc = do
  print $ mkName ["eq","rec"]
  print $ mkSucc mkZero
  print $ mkConstant (mkName ["foo"]) [mkZero, mkSucc mkZero]
