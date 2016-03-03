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

import Lens.Simple (makeLenses, view, over, use, uses, (%=), (.=), (<~), (+=))

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Debug.Trace
data IdxType = IdxName | IdxLevel | IdxExpr | IdxUni deriving (Show)

data ExportError = RepeatedIdx IdxType
                 | UnknownIdx IdxType
                 | TError TypeError -- TODO(dhs): import qualified
                 | IDeclError IndDeclError deriving (Show)

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

type ParserMethod = ParsecT String () (ExceptT ExportError (S.State Context))

parseInteger :: ParserMethod Integer
parseInteger = liftM read (many1 digit)

parseInt :: ParserMethod Int
parseInt = liftM read (many1 digit)

parseExportFile :: ParserMethod ()
parseExportFile = liftM mconcat (sepBy parseStatement newline)
  where
    parseStatement :: ParserMethod ()
    parseStatement = try parseDefinition <|> try parseValue

    parseDefinition :: ParserMethod ()
    parseDefinition = try parseUNI <|> try parseDEF <|> try parseAX <|> try parseIND

    parseUNI :: ParserMethod ()
    parseUNI = do
      string "#UNI" >> blank
      nameIdx <- parseInteger
      lift $ do
        name <- uses ctxNameMap (Map.! nameIdx)
        alreadyPresent <- uses ctxEnv (envHasGlobalLevel name)
        if alreadyPresent
        then throwE $ RepeatedIdx IdxUni
        else ctxEnv %= envAddGlobalLevel name

    parseDEF :: ParserMethod ()
    parseDEF = do
      string "#DEF" >> blank
      nameIdx <- parseInteger <* blank
      lpNameIdxs <- (sepBy parseInteger blank) <* char '|'
      typeIdx <- parseInteger <* blank
      valueIdx <- parseInteger
      lift $ do
        name <- uses ctxNameMap (Map.! nameIdx)
        lpNames <- uses ctxNameMap (\m -> map (m Map.!) lpNameIdxs)
        ty <- uses ctxExprMap (Map.! typeIdx)
        val <- uses ctxExprMap (Map.! valueIdx)
        ctxDefId += 1
        env <- use ctxEnv
        use ctxDefId >>= (\did -> trace ("DEF(" ++ show did ++ "): " ++ show name) (return ()))
        case envAddDefinition name lpNames ty val env of
          Left err -> throwE $ TError err
          Right env -> ctxEnv .= env

    parseAX :: ParserMethod ()
    parseAX = do
      string "#AX" >> blank
      nameIdx <- parseInteger <* blank
      lpNameIdxs <- (sepBy parseInteger blank) <* char '|'
      typeIdx <- parseInteger <* blank
      lift $ do
        name <- uses ctxNameMap (Map.! nameIdx)
        lpNames <- uses ctxNameMap (\m -> map (m Map.!) lpNameIdxs)
        ty <- uses ctxExprMap (Map.! typeIdx)
        ctxDefId += 1
        use ctxDefId >>= (\did -> trace ("AX(" ++ show did ++ "): " ++ show name) (return ()))
        env <- use ctxEnv
        case envAddAxiom name lpNames ty env of
          Left err -> throwE $ TError err
          Right env -> ctxEnv .= env

    parseIND :: ParserMethod ()
    parseIND = do
      string "#IND" >> blank
      indNameIdx <- parseInteger <* blank
      numParams <- parseInt <* blank
      lpNameIdxs <- (sepBy parseInteger blank) <* char '|'
      indTypeIdx <- parseInteger <* blank
      numIntroRules <- parseInt <* newline
      introRules <- count numIntroRules parseIntroRule
      lift $ do
        indName <- uses ctxNameMap (Map.! indNameIdx)
        lpNames <- uses ctxNameMap (\m -> map (m Map.!) lpNameIdxs)
        indType <- uses ctxExprMap (Map.! indTypeIdx)
        ctxIndId += 1
        use ctxIndId >>= (\did -> trace ("Ind(" ++ show did ++ "): " ++ show indName) (return ()))
        env <- use ctxEnv
        case addInductive env (IndDecl numParams lpNames indName indType introRules) of
          Left err -> throwE $ IDeclError err
          Right env -> ctxEnv .= env

    parseIntroRule :: ParserMethod IntroRule
    parseIntroRule = do
      string "#INTRO" >> blank
      irNameIdx <- parseInteger <* blank
      irTypeIdx <- parseInteger <* newline
      lift $ do
        irName <- uses ctxNameMap (Map.! irNameIdx)
        irType <- uses ctxExprMap (Map.! irTypeIdx)
        return $ IntroRule irName irType

    parseValue :: ParserMethod ()
    parseValue = try parseN <|> try parseU <|> try parseE <|> try parseB
    parseN = try parseNI <|> parseNS
    parseU = try parseUS <|> try parseUM <|> try parseUIM <|> try parseUP <|> try parseUG
    parseE = try parseEV <|> try parseES <|> try parseEC <|> try parseEA <|> try parseEL <|> try parseEP
    parseB = try parseBD <|> try parseBI <|> try parseBS <|> try parseBC

    parseNI = return ()
    parseNS = return ()

    parseUS = return ()
    parseUM = return ()
    parseUIM = return ()
    parseUP = return ()
    parseUG = return ()

    parseEV = return ()
    parseES = return ()
    parseEC = return ()
    parseEA = return ()
    parseEL = return ()
    parseEP = return ()

    parseBD = return ()
    parseBI = return ()
    parseBS = return ()
    parseBC = return ()

              {-
    parseValueCore :: Int -> ParserMethod ()
    parseValueCore n = parseN n <|> parseU n <|> parseE n <|> parseB n
    parseN n = char 'N' *> (parseNI n <|> parseNS n)
    parseU n = char 'U' *> (parseUS n <|> parseUM <|> parseUIM <|> parseUP <|> parseUG)
    parseE = char 'E' *> (parseEV <|> parseES <|> parseEC <|> parseEA <|> parseEL <|> parseEP)
    parseB = char 'B' *> (parseBD <|> parseBI <|> parseBS <|> parseBC)

    parseNI new_idx = do
      old_idx <- string "I " *> parseInteger
      i <- blank *> parseInteger
      return $ do
        m <- use ctxNameMap
        assertUndefined new_idx m RepeatedName
        ctxNameMap %= Map.insert new_idx (nameRConsI (m Map.! old_idx) i)

{-

    parseDefinition = parseDEF <|> parseAX <|> parseIND

    parseValue n1 = parseNS n1

parseInt :: Parsec String () Int
parseInt = liftM read (many1 digit)

parseNS :: Int -> Parsec String () Result
parseNS n1 = do
  string "#NS" >> blank
  n2 <- parseInt
  return $ Result NS n1 n2

parseDEF :: Parsec String () Result
parseDEF = do
  string "DEF" >> blank
  n1 <- parseInt <* blank
  n2 <- parseInt
  return $ Result DEF n1 n2

parseIND :: Parsec String () Result
parseIND = do
  string "BIND" >> blank
  n1 <- parseInt <* blank
  n2 <- parseInt <* blank
  levels <- (sepBy parseInt blank) <* newline
  indtypes <- count n2 parseIndType
  string "#EIND"
  return $ ResInd n1 n2 levels indtypes
  where
    parseIndType = (,) <$> (parseInd <* newline) <*> manyTill (parseIntro <* newline)
                   (lookAhead (try (string "#IND") <|> try (string "#EIND")))
    parseInd = (,) <$> (string "#IND" *> blank *> parseInt <* blank) <*> parseInt
    parseIntro = (,) <$> (string "#INTRO" *> blank *> parseInt <* blank) <*> parseInt

{-

parseStatement :: Parsec String () Result
parseStatement = (char '#' *> parseDefinition) <|> ((parseInt <* blank) >>= parseValue)

parseDefinition = parseDEF <|> parseIND
parseValue n1 = parseNS n1

parseInt :: Parsec String () Int
parseInt = liftM read (many1 digit)

parseNS :: Int -> Parsec String () Result
parseNS n1 = do
  string "#NS" >> blank
  n2 <- parseInt
  return $ Result NS n1 n2

parseDEF :: Parsec String () Result
parseDEF = do
  string "DEF" >> blank
  n1 <- parseInt <* blank
  n2 <- parseInt
  return $ Result DEF n1 n2

parseIND :: Parsec String () Result
parseIND = do
  string "BIND" >> blank
  n1 <- parseInt <* blank
  n2 <- parseInt <* blank
  levels <- (sepBy parseInt blank) <* newline
  indtypes <- count n2 parseIndType
  string "#EIND"
  return $ ResInd n1 n2 levels indtypes
  where
    parseIndType = (,) <$> (parseInd <* newline) <*> manyTill (parseIntro <* newline)
                   (lookAhead (try (string "#IND") <|> try (string "#EIND")))
    parseInd = (,) <$> (string "#IND" *> blank *> parseInt <* blank) <*> parseInt
    parseIntro = (,) <$> (string "#INTRO" *> blank *> parseInt <* blank) <*> parseInt

{-
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
-}
-}
-}
-}

main :: IO ()
main = putStrLn "Hello World!"
