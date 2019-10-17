{-# LANGUAGE ScopedTypeVariables #-}
module Renamer.NamedToDeBruijn
  (
    namedToDeBruijn
  , namedToDeBruijn'
  ) where

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
namedToDeBruijn :: ExprNamed -> Either String ExprDB
namedToDeBruijn e = namedToDeBruijn' [] e

namedToDeBruijn' :: forall a. Eq a
                  => [a] -- ^ List of variables in scope. e.g. ["x", "y", "z"]
                  -> Expr a a -- ^ Named expression
                  -> Either String ExprDB -- ^ Nameless expression or error.
namedToDeBruijn' ctxt (Var y) = do
  i <- lookupName ctxt y
  Right $ Var (toInteger $ i)
namedToDeBruijn' ctxt (Constr n args) = do
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ Constr n args'
namedToDeBruijn' ctxt (DestrCall n e args) = do
  e' <- namedToDeBruijn' ctxt e
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ DestrCall n e' args'
namedToDeBruijn' ctxt (FunCall n args) = do
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ FunCall n args'
namedToDeBruijn' ctxt (GenFunCall n args) = do
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ GenFunCall n args'
namedToDeBruijn' ctxt (ConsFunCall n e args) = do
  e' <- namedToDeBruijn' ctxt e
  args' <- sequence (namedToDeBruijn' ctxt <$> args)
  Right $ ConsFunCall n e' args'
namedToDeBruijn' ctxt (Match n e bl cases rtype) = do
  e' <- namedToDeBruijn' ctxt e
  let bindingNames = (\(n,_,_) -> n) <$> bl
  let blTrans :: (a, Expr a a, String) -> Either String ((), ExprDB, String)
      blTrans (_n,e,t) = do
        e' <- namedToDeBruijn' ctxt e
        Right $ ((),e',t)
  bl' <- sequence (blTrans <$> bl)
  let caseTrans :: (b ,[a],Expr a a) -> Either String (b, [()], ExprDB)
      caseTrans (n, args, e) = do
        e' <- namedToDeBruijn' (args ++ bindingNames) e -- Bug territory! args should be closer
        Right (n, const () <$> args, e')
  cases' <- sequence (caseTrans <$> cases)
  Right (Match n e' bl' cases' rtype)
namedToDeBruijn' ctxt (CoMatch n bl cocases) = do
  let bindingNames = (\(n,_,_) -> n) <$> bl
  let blTrans :: (a, Expr a a, String) -> Either String ((), ExprDB, String)
      blTrans (_n,e,t) = do
        e' <- namedToDeBruijn' ctxt e
        Right $ ((),e',t)
  bl' <- sequence (blTrans <$> bl)
  let cocaseTrans :: (b ,[a],Expr a a) -> Either String (b, [()], ExprDB)
      cocaseTrans (n, args, e) = do
        e' <- namedToDeBruijn' (args ++ bindingNames) e
        Right (n, const () <$> args, e')
  cocases' <- sequence (cocaseTrans <$> cocases)
  Right (CoMatch n bl' cocases')
namedToDeBruijn' ctxt (Let x e1 e2) = do
  e1' <- namedToDeBruijn' ctxt e1
  e2' <- namedToDeBruijn' (x:ctxt) e2
  Right $ Let () e1' e2'
