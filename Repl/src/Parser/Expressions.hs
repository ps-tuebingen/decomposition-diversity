module Parser.Expressions
  (
    exprP
  , exprNoVarP
  ) where

import Text.Megaparsec ((<|>), try, sepBy, some)
import qualified Text.Megaparsec.Char.Lexer as L

import Parser.Definitions
import Parser.Lexer
import Names (QName)

--------------------------------------------------------------------------------
-- Coq_expression Parsers ----------------------------------------------------------
--------------------------------------------------------------------------------

usingListP :: Parser [(VarNameParse, ExprParse, TypeNameParse)]
usingListP = (try (rword "using") >> (usingDeclP `sepBy` symbol ",")) <|> return []
  where
    usingDeclP = do
      var <- varP
      _ <- symbol ":="
      ex <- exprP
      _ <- symbol ":"
      tn <- typeNameP
      return (var, ex, tn)

--------------------------------------------------------------------------------
-- Local Match Parser
--------------------------------------------------------------------------------

matchP :: Parser ExprParse
matchP = L.indentBlock scn parse
  where parse = do
          (matchname, matchexp, usinglist, rtype) <- parseHeaderWithUsing
          return (L.IndentMany
                 Nothing
                 (\cases -> return $ MatchP matchname matchexp usinglist cases rtype)
                 parseCase)

parseHeaderWithUsing :: Parser (QName, ExprParse, [(VarNameParse, ExprParse, TypeNameParse)], TypeNameParse)
parseHeaderWithUsing = do
  try (rword "match")
  matchname <- lexeme $ do
    tn <- uppercaseIdentP
    _ <- symbol ":"
    n <- lowercaseIdentP
    return (tn,n)
  ex <- exprP
  usinglist <- usingListP
  rword "returning"
  rtype <- typeNameP
  rword "with"
  return (matchname, ex, usinglist, rtype)

parseCase :: Parser (SNameParse,[VarNameParse], ExprParse)
parseCase = do
  rword "case"
  fname <- snameP
  fargs <- parens (varP `sepBy` symbol ",")
  _ <- symbol "=>"
  ex <- exprP
  return (fname,fargs,ex)

--------------------------------------------------------------------------------
-- Local Comatch Parser
--------------------------------------------------------------------------------

comatchP :: Parser ExprParse
comatchP = L.indentBlock scn parse
  where parse = do
          (matchname, usinglist) <- parseCoHeaderWithUsing
          return (L.IndentMany
                 Nothing
                 (\cocases -> return $ CoMatchP matchname usinglist cocases)
                 parseCoCase)

parseCoHeaderWithUsing :: Parser (QName, [(VarNameParse, ExprParse, TypeNameParse)])
parseCoHeaderWithUsing = do
  try (rword "comatch")
  matchname <- lexeme $ do
    tn <- uppercaseIdentP
    _ <- symbol ":"
    n <- uppercaseIdentP
    return (tn,n)
  usinglist <- usingListP
  rword "with"
  return (matchname, usinglist)

parseCoCase :: Parser (SNameParse,[VarNameParse], ExprParse)
parseCoCase = do
  rword "cocase"
  fname <- snamePLC
  fargs <- parens (varP `sepBy` symbol ",")
  _ <- symbol "=>"
  ex <- exprP
  return (fname,fargs, ex)

--------------------------------------------------------------------------------
-- Parse Consumers
--------------------------------------------------------------------------------

type ConsumerCall = (SNameParse, [ExprParse])

consumerCallP :: Parser ExprParse
consumerCallP = do
  e1 <- exprP' -- Use exprP' since destructor / consumer function calls are left recursive!
  list <- some $ consumerP
  return (destructorChain e1 (reverse list))

consumerP :: Parser ConsumerCall
consumerP = do
  _ <- symbol "."
  dname <- snamePLC
  args <- parens $ exprP `sepBy` symbol ","
  return (dname,args)

-- | Function which helps in the parsing of expressions of the form "e.f(x).g(y).h(z)"
--  in the parser consumerCallP.
destructorChain :: ExprParse -> [ConsumerCall] -> ExprParse
destructorChain e [] = e
destructorChain e ((str, args) : xs) = ConsumerP str (destructorChain e xs) args

--------------------------------------------------------------------------------
-- Other expression Parsers
--------------------------------------------------------------------------------

-- | Parse a variable.
varExprParseP :: Parser ExprParse
varExprParseP = do
  varname <- varP
  return (VarP varname)

-- | Parse a nat literal.
natP :: Parser ExprParse
natP = do
  i <- L.decimal
  return (NatLit i)

-- | Parse a generator
generatorP :: Parser ExprParse
generatorP = do
  cname <- snameP
  args <- parens $ exprP `sepBy` symbol ","
  return (GeneratorP cname args)

-- | Parse a (normal) function call.
funcallP :: Parser ExprParse
funcallP = do
  fname <- fnameP
  args <- parens $ exprP `sepBy` symbol ","
  return $ FunCallP fname args

-- | Parse a let expression.
letP :: Parser ExprParse
letP = do
  pos <- L.indentLevel
  rword "let"
  varname <- varP
  _ <- symbol ":="
  exp1 <- exprP
  scn
  _ <- L.indentGuard sc EQ pos
  rword "in"
  exp2 <- exprP
  return (LetP varname exp1 exp2)

-- | Parse an arbitrary expression.
exprP :: Parser ExprParse
exprP =
  (try consumerCallP) <|>
  (try generatorP) <|>
  (try funcallP) <|>
  (try letP) <|>
  (try natP) <|>
  (try matchP) <|>
  (try comatchP) <|>
  (try varExprParseP)

-- | Parse an expression. Does not parse destructor calls or consumer function calls.
-- (Since these are left recursive).
exprP' :: Parser ExprParse
exprP' =
  (try generatorP) <|>
  (try funcallP) <|>
  (try letP) <|>
  (try natP) <|>
  (try matchP) <|>
  (try comatchP) <|>
  (try varExprParseP)

-- | Parse an expression which is not a Variable.
exprNoVarP :: Parser ExprParse
exprNoVarP =
  (try consumerCallP) <|>
  (try generatorP) <|>
  (try funcallP) <|>
  (try letP) <|>
  (try natP) <|>
  (try matchP) <|>
  (try comatchP)

