module Main where

import Frontend.Parser

import System.Environment

printUsage = putStrLn "usage: leantc <filename>"

main = do
  args <- getArgs
  case args of
    [] -> printUsage
    (_:_:_) -> printUsage
    [filename] -> do
      fileContents <- readFile filename
      case typeCheckExportFile filename fileContents of
        Left err -> putStrLn err
        Right _ -> putStrLn "Congratulations!"
