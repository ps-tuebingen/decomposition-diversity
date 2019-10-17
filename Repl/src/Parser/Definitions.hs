module Parser.Definitions
  (
    QNameParse(..)
  , SNameParse(..)
  , FNameParse(..)
  , VarNameParse(..)
  , TypeNameParse(..)
  , ExprParse(..)
  , ErrorType
  , Parser
  , parseInput
  ) where

import Data.Bifunctor (first)
import Text.Megaparsec
import Data.Void (Void)

import Names (QName)

--------------------------------------------------------------------------------
-- Parser specific Datastructures
--------------------------------------------------------------------------------

data QNameParse
  = QNameExpl String String
  | QNameImpl String
  deriving (Show, Eq)

data SNameParse
  = Local QNameParse
  | Global QNameParse
  deriving (Show, Eq)

newtype FNameParse = FNameParse String deriving (Show, Eq)
newtype VarNameParse = VarNameParse String deriving (Show, Eq)
newtype TypeNameParse = TypeNameParse String deriving (Show, Eq)

-- | Specialized Version of Expr for first stage of parsing.
-- This is used before disambiguating generator functions and constructors,
-- consumer functions and destructors.
data ExprParse
  = VarP VarNameParse
  | NatLit Int
  | GeneratorP SNameParse [ExprParse]
  | ConsumerP SNameParse ExprParse [ExprParse]
  | FunCallP FNameParse [ExprParse]
  | MatchP QName ExprParse [(VarNameParse, ExprParse, TypeNameParse)] [(SNameParse, [VarNameParse], ExprParse)] TypeNameParse
  | CoMatchP QName [(VarNameParse, ExprParse, TypeNameParse)] [(SNameParse, [VarNameParse], ExprParse)]
  | LetP VarNameParse ExprParse ExprParse
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Custom Error Handling
--------------------------------------------------------------------------------

type ErrorType = Void

--------------------------------------------------------------------------------
-- Definition of Parser
--------------------------------------------------------------------------------

type Parser = Parsec ErrorType String

--------------------------------------------------------------------------------
-- Parse function
--------------------------------------------------------------------------------

parseInput :: Parser a -> String -> Either String a
parseInput parser input =
  first errorBundlePretty (parse parser "" input)
