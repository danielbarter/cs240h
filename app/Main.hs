{-# LANGUAGE TemplateHaskell #-}
module Main where

import System.Environment
import Text.Parsec

import Kernel.Name
import Kernel.Level
import Kernel.Expr

import Kernel.TypeChecker
import Kernel.Inductive

import Control.Monad
import qualified Control.Monad.State as S
import Control.Monad.Reader
import Control.Monad.Trans.Except

import Lens.Simple (makeLenses, view, over, use, (%=), (.=), (<~))

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

data ExportRepeatError = RepeatedName | RepeatedLevel | RepeatedExpr | RepeatedUNI deriving (Show)

data KernelError = ExportError ExportRepeatError
                 | KernelTypeError TypeError
                 | KernelIndDeclError IndDeclError deriving (Show)

data Context = Context {
  _ctxNameMap :: Map Integer Name,
  _ctxLevelMap :: Map Integer Level,
  _ctxExprMap :: Map Integer Expr,
  _ctxEnv :: Env,
  _ctxDefId :: Integer,
  _ctxIndId :: Integer
  }

makeLenses ''Context

blank = char ' '

mkContext = Context (Map.insert 0 noName Map.empty) (Map.insert 0 mkZero Map.empty) Map.empty mkStdEnv 0 0

type Result = ExceptT KernelError (State Context) Env
type Parser = Parsec String ()

parseExportFile :: Parser [Result]
parseExportFile = sepBy parseStatement newline

parseInteger :: Parser Integer
parseInteger = liftM read (many1 digit)

parseStatement :: Parser Result
parseStatement = parseDefinition <|> parseValue

parseDefinition = char '#' >> (parseIND <|> parseUNI <|> parseDEF <|> parseAX)
parseValue = (parseInteger <* string " #") >>= parseValueCore
  where
    parseValueCore = parseN <|> parseU <|> parseE <|> parseB
    parseN = char 'N' *> (parseNI <|> parseNS)
    parseU = char 'U' *> (parseUS <|> parseUM <|> parseUIM <|> parseUP <|> parseUG)
    parseE = char 'E' *> (parseEV <|> parseES <|> parseEC <|> parseEA <|> parseEL <|> parseEP)
    parseB = char 'B' *> (parseBD <|> parseBI <|> parseBS <|> parseBC)

    parseNI new_idx = do
      old_idx <- string "I " *> parseInteger
      i <- blank *> parseInteger
      return $ do
        m <- use ctxNameMap
        assertUndefined new_idx m RepeatedName
        ctxNameMap %= Map.insert new_idx (nameRConsI (m Map.! old_idx) i)

assertUndefined n_idx m err = if Map.member n_idx m then throwE (ExportError err) else return ()

main :: IO ()
main = someFunc
