{-# LANGUAGE ScopedTypeVariables #-}
module Renamer.NamedToDeBruijn where

import HaskellAST


lookupName :: Eq a
           => [a] -- ^ Context
           -> a   -- ^ Named Variable to look up
           -> Either String Int -- ^ deBruijn Variable or Error
lookupName ls y = lookupName' ls y 0
  where
    lookupName' [] _ _ = Left "Used free variable"
    lookupName' (x:xs) z i =
      if x == z
      then Right i
      else lookupName' xs z (i + 1)

-- | Replace named Variables by de Bruijn Variables
exprNamed2exprDB :: ExprNamed -> Either String ExprDB
exprNamed2exprDB e = exprNamed2exprDB' [] e

exprNamed2exprDB' :: forall a. Eq a
                  => [a] -- ^ List of variables in scope. e.g. ["x", "y", "z"]
                  -> Expr a a -- ^ Named expression
                  -> Either String ExprDB -- ^ Nameless expression or error.
exprNamed2exprDB' ctxt (Var y) = do
  i <- lookupName ctxt y
  Right $ Var (toInteger $ i)
exprNamed2exprDB' ctxt (Constr n args) = do
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ Constr n args'
exprNamed2exprDB' ctxt (DestrCall n e args) = do
  e' <- exprNamed2exprDB' ctxt e
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ DestrCall n e' args'
exprNamed2exprDB' ctxt (FunCall n args) = do
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ FunCall n args'
exprNamed2exprDB' ctxt (GenFunCall n args) = do
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ GenFunCall n args'
exprNamed2exprDB' ctxt (ConsFunCall n e args) = do
  e' <- exprNamed2exprDB' ctxt e
  args' <- sequence (exprNamed2exprDB' ctxt <$> args)
  Right $ ConsFunCall n e' args'
exprNamed2exprDB' ctxt (Match n e bl cases rtype) = do
  e' <- exprNamed2exprDB' ctxt e
  let bindingNames = (\(n,_,_) -> n) <$> bl
  let blTrans :: (a, Expr a a, String) -> Either String ((), ExprDB, String)
      blTrans (_n,e,t) = do
        e' <- exprNamed2exprDB' ctxt e
        Right $ ((),e',t)
  bl' <- sequence (blTrans <$> bl)
  let caseTrans :: (b ,[a],Expr a a) -> Either String (b, [()], ExprDB)
      caseTrans (n, args, e) = do
        e' <- exprNamed2exprDB' (args ++ bindingNames) e -- Bug territory! args should be closer
        Right (n, const () <$> args, e')
  cases' <- sequence (caseTrans <$> cases)
  Right (Match n e' bl' cases' rtype)
exprNamed2exprDB' ctxt (CoMatch n bl cocases) = do
  let bindingNames = (\(n,_,_) -> n) <$> bl
  let blTrans :: (a, Expr a a, String) -> Either String ((), ExprDB, String)
      blTrans (_n,e,t) = do
        e' <- exprNamed2exprDB' ctxt e
        Right $ ((),e',t)
  bl' <- sequence (blTrans <$> bl)
  let cocaseTrans :: (b ,[a],Expr a a) -> Either String (b, [()], ExprDB)
      cocaseTrans (n, args, e) = do
        e' <- exprNamed2exprDB' (args ++ bindingNames) e
        Right (n, const () <$> args, e')
  cocases' <- sequence (cocaseTrans <$> cocases)
  Right (CoMatch n bl' cocases')
exprNamed2exprDB' ctxt (Let x e1 e2) = do
  e1' <- exprNamed2exprDB' ctxt e1
  e2' <- exprNamed2exprDB' (x:ctxt) e2
  Right $ Let () e1' e2'
