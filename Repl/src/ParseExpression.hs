module ParseExpression
  (
    ParseExpression.parseExpression
  , parseProgram
  ) where

import Skeleton
import AST
import ProgramDef
import Renamer.ParsedToNamed (parsedToNamed)
import Renamer.NamedToDeBruijn (namedToDeBruijn)
import Renamer.DeBruijnToCoq (deBruijnToCoq)
import Parser.Definitions
import Parser.Expressions
import Parser.Declarations
import AssembleProgram

parseExpression :: Coq_skeleton -> String -> Either String Coq_expr
parseExpression sk str = do
  let parsedStr = Parser.Expressions.parseExpression str
  case parsedStr of
    Left err -> Left err
    Right expr -> do
      renamedExpr <- parsedToNamed sk expr
      namelessExpr <- namedToDeBruijn renamedExpr
      Right (deBruijnToCoq namelessExpr)

parseProgram :: String -> Either String Coq_program
parseProgram str = do
  let parsedDecls = parseInput declarationsP str
  case parsedDecls of
    Left err -> Left err
    Right decls -> assembleProgram decls
