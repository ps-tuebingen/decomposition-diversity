module Parser.Lexer
  (
    sc
  , scn
  , lexeme
  , uppercaseIdentP
  , underscoreUppercaseIdentP
  , symbol
  , parens
  , rword
  , typeNameP
  , qnameP
  , snameP
  , fnameP
  , varP
  ) where

import Text.Megaparsec
import Text.Megaparsec.Char (alphaNumChar, char, string, space1, lowerChar, upperChar)
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad(void)
import Parser.ParserDefinition

--------------------------------------------------------------------------------
-- Lexer -----------------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Line Comments start with "//".
lineComment :: Parser ()
lineComment = L.skipLineComment "//"

-- | (Non-nested) Block Comments are enclosed by "/*" "*/".
blockComment :: Parser ()
blockComment = L.skipBlockComment "/*" "*/"

-- | Space consumer which consumes newlines.
scn :: Parser ()
scn = L.space space1 lineComment blockComment

-- | Space consumer which does not consume newlines.
sc :: Parser ()
sc = L.space (void $ takeWhile1P Nothing f) lineComment empty
  where
    f x = x == ' ' || x == '\t'

-- | Wrap a parser in lexeme to consume trailing whitespace.
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Parse a given string
symbol :: String -> Parser String
symbol = L.symbol sc

-- | Wrap a parser to also consume enclosing parenthesis.
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | A list of reserved keywords
rws :: [String]
rws = ["data", "codata", "where", "in", "let", "match", "comatch", "function",
       "case", "cocase", "generator", "consumer", "using", "with", "returning"]

-- | Parse a reserved keyword.
-- The parsed keyword mustn't be the prefix of an identifier.
rword :: String -> Parser ()
rword w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

-- | Identifier type 1.
-- [A-Z][a-z,A-Z,0-9]* \ rws
uppercaseIdentP :: Parser String
uppercaseIdentP =  (:) <$> upperChar <*> many alphaNumChar
    

-- | Identifier type 2. Does not return the leading underscore.
-- '_'[a-z][a-z,A-Z,0-9]* \ rws
underscoreUppercaseIdentP :: Parser String
underscoreUppercaseIdentP = char '_' >> ((:) <$> upperChar <*> many alphaNumChar)


-- | Identifier type 1.
-- [a-z][a-z,A-Z,0-9]* \ rws
lowercaseIdentP :: Parser String
lowercaseIdentP =  (:) <$> lowerChar <*> many alphaNumChar

--------------------------------------------------------------------------------
-- Name Parsers ----------------------------------------------------------------
--------------------------------------------------------------------------------

checkKeyword :: String -> String -> Parser String
checkKeyword w1 w2 = if w2 `elem` rws
                     then fail $ "The keyword \"" ++ w2 ++ "\" cannot be used as " ++ w1
                     else return w2

-- | Parse a TypeName, e.g. "Bool"                          
typeNameP :: Parser TypeNameParse
typeNameP = do
  tn <- lexeme uppercaseIdentP
  return (TypeNameParse tn)

-- Qualified Names

-- | Parse an explicitly given QName, e.g. "Bool:true"
qnameExplP :: Parser QNameParse
qnameExplP = lexeme $ do
  tn <- uppercaseIdentP
  _ <- symbol ":"
  n <- uppercaseIdentP
  return (QNameExpl tn n)

-- | Parse an implicitly given QName, e.g. "true"
qnameImplP :: Parser QNameParse
qnameImplP = lexeme $ do
  n <- uppercaseIdentP
  return (QNameImpl n)

-- | Parse a QName, i.e. either "Bool:true" or "true"
qnameP :: Parser QNameParse
qnameP = try qnameExplP <|> qnameImplP

-- Scoped Names

snameLocalExplP :: Parser SNameParse
snameLocalExplP = lexeme $ do
  tn <- uppercaseIdentP
  _ <- symbol ":"
  n <- underscoreUppercaseIdentP
  return (Local (QNameExpl tn n))

snameGlobalExplP :: Parser SNameParse
snameGlobalExplP = lexeme $ do
  tn <- uppercaseIdentP
  _ <- symbol ":"
  n <- uppercaseIdentP
  return (Global (QNameExpl tn n))

snameLocalImplP :: Parser SNameParse
snameLocalImplP = lexeme $ do
  n <- underscoreUppercaseIdentP
  return (Local (QNameImpl n))

snameGlobalImplP :: Parser SNameParse
snameGlobalImplP = lexeme $ do
  n <- uppercaseIdentP
  return (Global (QNameImpl n))
  
snameP :: Parser SNameParse
snameP = try snameLocalExplP <|> try snameGlobalExplP <|> try snameLocalImplP <|> snameGlobalImplP

-- Function Names

fnameP :: Parser FNameParse
fnameP = lexeme $ do
  n <- lowercaseIdentP
  return (FNameParse n)

-- | Parse a variable.
varP :: Parser VarNameParse
varP = do
  vn <- (lexeme . try) (lowercaseIdentP >>= (checkKeyword "variable"))
  return (VarNameParse vn)


