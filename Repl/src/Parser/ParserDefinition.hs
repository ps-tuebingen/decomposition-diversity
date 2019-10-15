module Parser.ParserDefinition
  (
    QNameParse(..)
  , SNameParse(..)
  , FNameParse(..)
  , VarNameParse(..)
  , TypeNameParse(..)
  , ExprParse(..)
  , ErrorType
--  , UroboroError(..)
--  , annotateError
  , Parser
  , parseInput
  ) where

import Text.Megaparsec
import Data.Void(Void)
import Data.Bifunctor(first)
import qualified Data.Set as S

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

type ErrorType = Void --UroboroError

-- data UroboroError = UroboroError
--   (Maybe (ErrorItem Char)) -- unexpected part
--   (S.Set (ErrorItem Char)) -- expected part
--   String                 -- Custom part
--   deriving (Eq, Ord, Show)

-- instance ShowErrorComponent UroboroError where
--   showErrorComponent (UroboroError us es str) =
--     parseErrorTextPretty (TrivialError undefined us es :: ParseError Char Void)
--     ++ str

-- appendError :: String -> ErrorFancy UroboroError -> ErrorFancy UroboroError
-- appendError str (ErrorFail str') = ErrorFail (str ++ "    " ++  str')
-- appendError _ (ErrorIndentation ord pos1 pos2) = ErrorIndentation ord pos1 pos2
-- appendError str (ErrorCustom (UroboroError us es str')) = ErrorCustom (UroboroError us es (str ++ str'))

-- annotateError :: String -> Parser a -> Parser a
-- annotateError str p = region handler p
--   where
--     handler :: (ParseError (Token String) UroboroError) -> (ParseError (Token String) UroboroError)
--     handler (TrivialError pos us es) = FancyError pos (S.singleton $ ErrorCustom (UroboroError us es str))
--     handler (FancyError pos efs) = FancyError pos (S.map (appendError str) efs)

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
