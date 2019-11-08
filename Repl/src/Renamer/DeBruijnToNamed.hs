module Renamer.DeBruijnToNamed
  (
    deBruijnToNamed'
  , deBruijnToNamed
  ) where

import Names (ScopedName, TypeName, ScopedName(..))
import HaskellAST

import Control.Monad.Reader
-- | Replace de Bruijn Variables by named Variables
deBruijnToNamed :: ExprDB -> Either String ExprNamed
deBruijnToNamed e = flip runReaderT 0 $ deBruijnToNamed' [] e

deBruijnToNamed' :: [String] -> ExprDB -> ReaderT Int (Either String) ExprNamed
deBruijnToNamed' ctxt (Var n) =
  return . Var $ (ctxt !! fromInteger n)-- ++ "{" ++ show n ++ "}"
deBruijnToNamed' ctxt (Constr n args) = do
  args' <- sequence (deBruijnToNamed' ctxt <$> args)
  return $ Constr n args'
deBruijnToNamed' ctxt (DestrCall n e args) = do
  e' <- deBruijnToNamed' ctxt e
  args' <- mapM (deBruijnToNamed' ctxt) args
  return $ DestrCall n e' args'
deBruijnToNamed' ctxt (FunCall n args) = do
  args' <- mapM (deBruijnToNamed' ctxt) args
  return $ FunCall n args'
deBruijnToNamed' ctxt (GenFunCall n args) = do
  args' <- mapM (deBruijnToNamed' ctxt) args
  return $ GenFunCall n args'
deBruijnToNamed' ctxt (ConsFunCall n e args) = do
  e' <- deBruijnToNamed' ctxt e
  args' <- mapM (deBruijnToNamed' ctxt) args
  return $ ConsFunCall n e' args'
deBruijnToNamed' ctxt (Match n e bindingList cases rtype) = do
  bindingListNames <- genBindingListNames bindingList
  bindingList' <- transBL ctxt bindingList
  e' <- deBruijnToNamed' ctxt e
  cases' <- local (+1) $ sequence (deBruijnToNamedCase (length bindingList) bindingListNames <$> cases)
  return $ Match n e' bindingList' cases' rtype
deBruijnToNamed' ctxt (CoMatch n bindingList cocases) = do
  bindingListNames <- genBindingListNames bindingList
  bindingList' <- transBL ctxt bindingList
  cocases' <- local (+1) $ sequence (deBruijnToNamedCase (length bindingList) bindingListNames <$> cocases)
  return $ CoMatch n bindingList' cocases'
deBruijnToNamed' ctxt (Let _ e1 e2) = do
  newName <- generateNameR (length ctxt)
  e1' <- deBruijnToNamed' ctxt e1
  e2' <- local (+1) $ deBruijnToNamed' (newName : ctxt) e2
  return $ Let newName e1' e2'

genBindingListNames :: Monad m => [a] -> ReaderT Int m [String]
genBindingListNames bl = sequence $ generateNameR <$> [0.. length bl - 1]

generateNameR :: Monad m => Int -> ReaderT Int m String
generateNameR i = do
  l <- ask
  return $ generateName l i
 

transBL :: [String]
        -> [((), ExprDB, TypeName)]
        -> ReaderT Int (Either String) [(String, ExprNamed, TypeName)]
transBL ctxt bl = do
  blNames <- genBindingListNames bl
  zipWithM foo bl blNames
    where
      foo (_, e, typename) name = do
        e' <- local (+1) $ deBruijnToNamed' ctxt e
        return (name, e', typename)


--  sequence (foo <$> zip bl (genBindingListNames bl))
  --  where
    --  foo ((_, e, typename), name) = do
      --  e' <- deBruijnToNamed' ctxt e
      --  return (name, e', typename)

deBruijnToNamedCase :: Int -- ^ Length of bindingList
                    -> [String]
                    -> (ScopedName, [()], ExprDB)
                    -> ReaderT Int (Either String) (ScopedName, [String], ExprNamed)
deBruijnToNamedCase i bindingListNames (sn,ls,e) = do
  caseNames <- mapM generateNameR  [ i .. i + length ls - 1]
  e' <- deBruijnToNamed' (caseNames ++ bindingListNames) e
  return (sn, caseNames, e')

