module Parser.Declarations
  (
    Declaration(..)
  , declarationsP
  , declarationP
  ) where

import Text.Megaparsec ((<|>), sepBy, try)
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as C

import Names (TypeName, ScopedName(..), QName)
import Parser.Definitions
import Parser.Expressions
import Parser.Lexer

--------------------------------------------------------------------------------
-- Different kinds of declarations
--------------------------------------------------------------------------------

data Declaration
  = DataTypeD TypeNameParse [(ScopedName, [TypeNameParse])]
  | CoDataTypeD TypeNameParse [(ScopedName, [TypeNameParse], TypeNameParse)]
  | FunctionD FNameParse [(VarNameParse, TypeNameParse)] TypeNameParse ExprParse 
  | GenFunD QName [(VarNameParse, TypeNameParse)]               [(ScopedName,[VarNameParse], ExprParse)]
  | ConFunD QName [(VarNameParse, TypeNameParse)] TypeNameParse [(ScopedName,[VarNameParse], ExprParse)]

--------------------------------------------------------------------------------
-- Parser Helper functions
--------------------------------------------------------------------------------

-- | Parse an argument of the Form "x : Type".
parseArg :: Parser (VarNameParse, TypeNameParse)
parseArg = do
  varname <- varP
  _ <- symbol ":"
  tn <- typeNameP
  return (varname, tn)

-- | Parse a list of arguments of the form " x : Type1 , y : Type 2" etc.
parseArgs :: Parser [(VarNameParse, TypeNameParse)]
parseArgs = parseArg `sepBy` symbol ","

scopedNameHelperP :: TypeName -> Parser ScopedName
scopedNameHelperP tn = try local <|> global
  where
    local :: Parser ScopedName
    local = do
      n <- underscoreUppercaseIdentP
      return (Coq_local (tn,n))
    global :: Parser ScopedName
    global = do
      n <- uppercaseIdentP
      return (Coq_global (tn,n))
      
--------------------------------------------------------------------------------
-- DataType Parsers ------------------------------------------------------------
--------------------------------------------------------------------------------
-- Datatypes must be toplevel and cannot be indented.
-- Arguments of constructors are in square brackets.
--
-- Example:
-- data Nat where
--   Zero()
--   Succ(Nat)
--------------------------------------------------------------------------------

-- | Parse the header of a datatype declaration.
dataTypeHeaderP :: Parser TypeNameParse
dataTypeHeaderP = do
  try (rword "data")
  typename <- typeNameP
  rword "where"
  return typename

-- | Parse one constructor of a datatype declaration.
dataTypeCtorP :: TypeNameParse -> Parser (ScopedName, [TypeNameParse])
dataTypeCtorP (TypeNameParse tn) = do
  sname <- scopedNameHelperP tn
  args <- parens $ typeNameP `sepBy` symbol ","
  _ <- C.eol
  return (sname, args)
    
-- | Parse a datatype declaration.
-- On a correct parse the datatype is added to the parser state.
dataTypeP :: Parser Declaration
dataTypeP = L.nonIndented scn (L.indentBlock scn parse)
  where
    parse = do
      typename <- dataTypeHeaderP
      return (L.IndentMany
              Nothing --First indented constructor sets indent level
              (\ctors -> return $ DataTypeD typename ctors)
              (dataTypeCtorP typename))

--------------------------------------------------------------------------------
-- CoDataType Parsers ----------------------------------------------------------
--------------------------------------------------------------------------------
-- CoDatatypes must be toplevel and cannot be indented.
--
-- Example:
-- codata Fun where
--   apply(Nat) : Nat
--------------------------------------------------------------------------------

-- | Parse the header of a codatatype declaration.
coDataTypeHeaderP :: Parser TypeNameParse
coDataTypeHeaderP = do
  try (rword "codata")
  typename <- typeNameP
  rword "where"
  return typename

-- | Parse one destructor of a codatatype declaration.
coDataTypeDtorP :: TypeNameParse -> Parser (ScopedName, [TypeNameParse], TypeNameParse)
coDataTypeDtorP (TypeNameParse tn) = do
  sname <- scopedNameHelperP tn
  args <- parens $ typeNameP `sepBy` symbol ","
  _ <- symbol ":"
  returntype <- typeNameP
  _ <- C.eol
  return (sname, args, returntype)
  
-- | Parse a codatatype declaration.
-- On a correct parse the codatatype is added to the parser state.
coDataTypeP :: Parser Declaration
coDataTypeP =  L.nonIndented scn (L.indentBlock scn parse)
  where
    parse = do
      typename <- coDataTypeHeaderP
      return (L.IndentMany
              Nothing --First indented destructor sets indent level
              (\dtors -> return $ CoDataTypeD typename dtors)
              (coDataTypeDtorP typename))

--------------------------------------------------------------------------------
-- Function Parsers
--------------------------------------------------------------------------------
-- Function declarations must be toplevel and cannot be indented.
--
-- Example:
-- function scopedNameHelperP (x : Nat, y : Bool) : Bool :=
--   y
--------------------------------------------------------------------------------

functionDeclP :: Parser Declaration
functionDeclP = L.nonIndented scn (L.indentBlock scn parse)
  where
    parse = do
      (fname, fargs, rtype) <- functionDeclSigP
      return (L.IndentSome
              Nothing
              (\ex -> return (FunctionD fname fargs rtype (head ex)))
              exprP)

-- | Parse the declaration of a function.
functionDeclSigP :: Parser (FNameParse, [(VarNameParse, TypeNameParse)], TypeNameParse) 
functionDeclSigP = do
  try (rword "fun")
  fname <- fnameP
  fargs <- parens parseArgs
  _ <- symbol ":"
  rtype <- typeNameP
  _ <- symbol ":="
  return (fname, fargs, rtype)

--------------------------------------------------------------------------------
-- Generator Function Parsers
--------------------------------------------------------------------------------

cocaseP :: TypeName -> Parser (ScopedName,[VarNameParse],  ExprParse)
cocaseP tn = do
  rword "cocase"
  sn <- scopedNameHelperP tn    
  fargs <- parens (varP `sepBy` symbol ",")
  _ <- symbol "=>"
  ex <- exprP
  --  _ <- C.eol
  return (sn, fargs, ex)

generatorFunctionDeclP :: Parser Declaration
generatorFunctionDeclP = L.nonIndented scn (L.indentBlock scn parse)
  where
    parse = do
          (qn, fargs) <- generatorFunctionDeclSigP
          return (L.IndentSome
                 Nothing
                 (\cocases -> return (GenFunD qn fargs cocases))
                 (cocaseP (fst qn)))

-- | Parse the declaration of a generator function.
generatorFunctionDeclSigP :: Parser (QName, [(VarNameParse, TypeNameParse)])
generatorFunctionDeclSigP = do
  try (rword "gfun")
  fname <- uppercaseIdentP
  fargs <- parens parseArgs
  _ <- symbol ":"
  (TypeNameParse rtype) <- typeNameP
  _ <- symbol ":="
  return ((rtype, fname),fargs)
  
--------------------------------------------------------------------------------
-- Consumer Function Parsers
--------------------------------------------------------------------------------

caseP :: TypeName -> Parser (ScopedName,[VarNameParse], ExprParse)
caseP tn = do
  rword "case"
  sn <- scopedNameHelperP tn
  fargs <- parens (varP `sepBy` symbol ",")
  _ <- symbol "=>"
  ex <- exprP
  --  _ <- C.eol
  return (sn, fargs, ex)

consumerFunctionDeclP :: Parser Declaration
consumerFunctionDeclP = L.nonIndented scn (L.indentBlock scn parse)
  where
    parse = do
      (qn, fargs, rtype) <- consumerFunctionDeclSigP
      return (L.IndentSome
             Nothing
             (\cases -> return (ConFunD qn fargs rtype cases))
             (caseP (fst qn)))

-- | Parse the declaration of a consumer function.
-- Returns the Signature of the consumer function and a list of the names of the bound variables.
consumerFunctionDeclSigP :: Parser (QName, [(VarNameParse, TypeNameParse)], TypeNameParse)
consumerFunctionDeclSigP = do
  try (rword "cfun")
  qn <- do
    tn <- uppercaseIdentP
    _ <- symbol ":"
    n <- uppercaseIdentP
    return (tn,n)
  fargs <- parens  parseArgs
  _ <- symbol ":"
  (TypeNameParse rtype) <- typeNameP
  _ <- symbol ":="
  return (qn, fargs, TypeNameParse rtype)

--------------------------------------------------------------------------------
-- Declaration Parsers ---------------------------------------------------------
--------------------------------------------------------------------------------

-- | Parse a single top-level declaration.
declarationP :: Parser Declaration
declarationP = dataTypeP <|> coDataTypeP <|> functionDeclP <|>
  generatorFunctionDeclP <|> consumerFunctionDeclP

-- | Parse a list of top-level declarations.
declarationsP :: Parser [Declaration]
declarationsP = declarationP `sepBy` scn


