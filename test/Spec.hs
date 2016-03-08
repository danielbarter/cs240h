module Main (main) where

import Test.Hspec
import LevelSpec (spec)

main :: IO ()
main = hspec $ LevelSpec.spec
