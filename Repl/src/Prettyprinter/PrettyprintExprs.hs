module Prettyprinter.PrettyprintExprs
  (
    exprToDoc
  , scopedNameToDoc
  , qNameToDoc
  , caseToDoc
  , cocaseToDoc
  ) where

import Data.List (intersperse)
import Data.Text.Prettyprint.Doc
import Control.Monad.Reader (asks)

import Names (TypeName, ScopedName(..), QName, Name)
import HaskellAST
import Prettyprinter.PrettyprinterDefs

-- | Prettyprint a qualified name
qNameToDoc :: (String, String) -> PrettyPrinter
qNameToDoc (tn, n) = do
  printQualified <- asks printQualifiedNames
  if printQualified
    then return $ typename tn <> colon <> pretty n
    else return $ pretty n
    
-- | Prettyprint a scoped name
scopedNameToDoc :: ScopedName -> PrettyPrinter
scopedNameToDoc (Coq_local (tn, n)) = do
  printQualified <- asks printQualifiedNames
  if printQualified
    then return $ typename tn <> colon <> pretty "_" <> pretty n
    else return $ pretty "_" <> pretty n
scopedNameToDoc (Coq_global (tn, n)) = do
  printQualified <- asks printQualifiedNames
  if printQualified
    then return $ typename tn <> colon <> pretty n
    else return $ pretty n

-- | Check whether given expression is a Nat value, i.e. is of form
--  "zero[]" or "succ[n]", where "n" is a Nat value.
isNatValue :: ExprNamed -> Bool
isNatValue (Constr (Coq_global ("Nat", "zero")) []) = True
isNatValue (Constr (Coq_global ("Nat", "succ")) [n]) = isNatValue n
isNatValue _ = False

-- | Renders an expression which is a Nat value as corresponding MyDoc.
-- E.g. succ[succ[zero[]]] => "2"
natValueToDoc :: ExprNamed -> MyDoc
natValueToDoc e =
  let
    natValueToInt :: ExprNamed -> Int
    natValueToInt (Constr (Coq_global ("Nat", "zero")) []) = 0
    natValueToInt (Constr (Coq_global ("Nat", "succ")) [n]) = 1 + (natValueToInt n)
    natValueToInt _ = error "natValueToDoc: Applied function to expression which is not a value of type nat"
  in
    pretty (show (natValueToInt e))
    
exprToDoc :: ExprNamed -> PrettyPrinter
exprToDoc (Var str)                   = return $ pretty str
exprToDoc (Constr sn args)            = generatorToDoc sn args
exprToDoc (DestrCall sn e args)       = consumerToDoc sn e args
exprToDoc (FunCall n args)            = funcallToDoc n args
exprToDoc (GenFunCall sn args)        = generatorToDoc sn args
exprToDoc (ConsFunCall sn e args)     = consumerToDoc sn e args
exprToDoc (Match qn e bl cases rtype) = matchToDoc qn e bl cases rtype
exprToDoc (CoMatch qn bl cases)       = comatchToDoc qn bl cases
exprToDoc (Let bind e1 e2)            = letToDoc bind e1 e2

-- | Prettyprint a list of expressions as "(e1,e2,..,en)"
argumentsToDoc :: [ExprNamed] -> PrettyPrinter
argumentsToDoc exprs = do
  ppexprs <- sequence (exprToDoc <$> exprs)
  return $ (parens . hsep) (intersperse comma ppexprs)

-- | Prettyprinting constructors and generator function calls.
generatorToDoc :: ScopedName -> [ExprNamed] -> PrettyPrinter
generatorToDoc sn args = do
  sname <- scopedNameToDoc sn
  ppargs <- argumentsToDoc args
  return (sname <> ppargs)

-- | Prettyprinting destructor and consumer function calls.
consumerToDoc :: ScopedName -> ExprNamed -> [ExprNamed] -> PrettyPrinter
consumerToDoc sn e args = do
  sname <- scopedNameToDoc sn
  ppe <- exprToDoc e
  ppargs <- argumentsToDoc args
  return (ppe <> pretty "." <> sname <> ppargs)

-- | Prettyprint function calls
funcallToDoc :: Name -> [ExprNamed] -> PrettyPrinter
funcallToDoc n args = do
  ppn <- return $ pretty n
  ppargs <- argumentsToDoc args
  return (ppn <> ppargs)

-- | Prettyprint a binding list.
bindingListToDoc :: [(String, ExprNamed, TypeName)] -> PrettyPrinter
bindingListToDoc bl = do
  tmp <- sequence (bindingToDoc <$> bl)
  return (hsep (intersperse comma tmp))
  where
    bindingToDoc :: (String, ExprNamed, TypeName) -> PrettyPrinter
    bindingToDoc (str, e, tn) = do
      ppe <- exprToDoc e
      return (pretty str <+> pretty ":=" <+> ppe <+> colon <+> pretty tn)

caseToDoc :: (ScopedName, [String], ExprNamed) -> PrettyPrinter
caseToDoc (sn, args, e) = do
  ppsn <- scopedNameToDoc sn
  let ppargs = (parens . hsep) (intersperse comma (pretty <$> args))
  ppe <- exprToDoc e
  return (pretty "case" <+> ppsn <> ppargs <+> pretty "=>" <+> ppe)

-- | Prettyprint local matches.
matchToDoc :: QName -> ExprNamed -> [(String, ExprNamed, TypeName)] -> [(ScopedName, [String], ExprNamed)] -> TypeName -> PrettyPrinter
matchToDoc qn e bl cases rtype = do
  ppqn <- qNameToDoc qn
  ppe <- exprToDoc e
  ppbl <- bindingListToDoc bl
  ppcases <- sequence (caseToDoc <$> cases)
  return $
    keyword "match" <+> ppqn <+> ppe <+>
    (if not (null bl) then keyword "using" <+> ppbl else mempty) <+>
    keyword "returning" <+> pretty rtype <+> keyword "with" <>
    (nest 3 (line <> (vcat ppcases)))

cocaseToDoc :: (ScopedName, [String], ExprNamed) -> PrettyPrinter
cocaseToDoc (sn, args, e) = do
  ppsn <- scopedNameToDoc sn
  let ppargs = (parens . hsep) (intersperse comma (pretty <$> args))
  ppe <- exprToDoc e
  return (pretty "case" <+> ppsn <> ppargs <+> pretty "=>" <+> ppe)
  
-- | Prettyprint local comatches.
comatchToDoc :: QName -> [(String, ExprNamed, TypeName)] -> [(ScopedName, [String], ExprNamed)] -> PrettyPrinter
comatchToDoc qn bl cocases = do
  ppqn <- qNameToDoc qn
  ppbl <- bindingListToDoc bl
  ppcocases <- sequence (cocaseToDoc <$> cocases)
  return $
    keyword "comatch" <+> ppqn <+>
    (if not (null bl) then keyword "using" <+> ppbl else mempty) <+> keyword "with" <>
    (nest 3 (line <> (vcat ppcocases)))

letToDoc :: String -> ExprNamed -> ExprNamed -> PrettyPrinter
letToDoc bind e1 e2 = do
  ppe1 <- exprToDoc e1
  ppe2 <- exprToDoc e2
  return $
    keyword "let" <+>
    pretty bind <+>
    pretty ":=" <+>
    ppe1 <+>
    line <>
    keyword "in" <+>
    (nest 3 ppe2)
