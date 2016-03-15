module Main (main) where

import Test.Hspec
import qualified LevelSpec
import qualified ExprSpec
import qualified TypeCheckerSpec
import qualified Integration

main :: IO ()
main = hspec $ do
  LevelSpec.spec
  ExprSpec.spec
  TypeCheckerSpec.spec
  Integration.test
