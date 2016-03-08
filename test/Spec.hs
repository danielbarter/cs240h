module Main (main) where

import Test.Hspec
import LevelSpec (spec)
import ExprSpec (spec)

main :: IO ()
main = hspec $ do
  LevelSpec.spec
  ExprSpec.spec
