module ParseExpression
  (
    ParseExpression.parseExpression
  , parseProgram
  ) where

import Skeleton
import AST
import ProgramDef
import Renamer.ParsedToNamed
import Renamer.NamedToDeBruijn
import Renamer.DeBruijnToCoq (deBruijnToCoq)
import Parser.ParserDefinition
import Parser.ExpressionParser
import Parser.DeclarationParser
import AssembleProgram

parseExpression :: Coq_skeleton -> String -> Either String Coq_expr
parseExpression sk str = do
  let parsedStr = Parser.ExpressionParser.parseExpression str
  case parsedStr of
    Left err -> Left err
    Right expr -> do
      renamedExpr <- rename sk expr
      namelessExpr <- exprNamed2exprDB renamedExpr
      Right (deBruijnToCoq namelessExpr)

parseProgram :: String -> Either String Coq_program
parseProgram str = do
  let parsedDecls = parseInput declarationsP str
  case parsedDecls of
    Left err -> Left err
    Right decls -> assembleProgram decls
