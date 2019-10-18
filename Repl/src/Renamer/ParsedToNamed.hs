module Renamer.ParsedToNamed
  (
    parsedToNamed
  ) where

import Data.List (find)
import Control.Monad.Except
import Control.Monad.Reader

import Parser.Definitions
import Names (ScopedName, TypeName, unscope, ScopedName(..))
import Skeleton
import HaskellAST

--------------------------------------------------------------------------------
-- The Renamer Monad
--------------------------------------------------------------------------------

type RenamerM a = ReaderT Coq_skeleton (Except String) a

parsedToNamed :: Coq_skeleton -> ExprParse -> Either String ExprNamed
parsedToNamed sk expr = runExcept (runReaderT (rename' expr) sk)

--------------------------------------------------------------------------------
-- Helper functions in the Renamer Monad
--------------------------------------------------------------------------------

getDts :: RenamerM [TypeName]
getDts = do
  skeleton <- ask
  return (skeleton_dts skeleton)

getCtors :: RenamerM [Coq_ctor]
getCtors = do
  skeleton <- ask
  return (skeleton_ctors skeleton)

getGfunSigs :: RenamerM [Coq_gfun_sig]
getGfunSigs = do
  skeleton <- ask
  return (skeleton_gfun_sigs_g skeleton)

getCdts :: RenamerM [TypeName]
getCdts = do
  skeleton <- ask
  return (skeleton_cdts skeleton)

getDtors :: RenamerM [Coq_dtor]
getDtors = do
  skeleton <- ask
  return (skeleton_dtors skeleton)

getCfunSigsG :: RenamerM [Coq_cfun_sig]
getCfunSigsG = do
  skeleton <- ask
  return (skeleton_cfun_sigs_g skeleton)

getCfunSigsL :: RenamerM [Coq_cfun_sig]
getCfunSigsL = do
  skeleton <- ask
  return (skeleton_cfun_sigs_l skeleton)

natToExprNamed :: Int -> ExprNamed
natToExprNamed 0 = Constr (Coq_global ("Nat", "Zero")) []
natToExprNamed n = Constr (Coq_global ("Nat", "Succ")) [(natToExprNamed (n - 1))]

--------------------------------------------------------------------------------
-- Renaming functions
--------------------------------------------------------------------------------

-- | Rename' the Strings into QNames and ScopedNames. (Requires Skeleton)
rename' :: ExprParse -> RenamerM ExprNamed
rename' (VarP (VarNameParse str)) = return (Var str)
rename' (NatLit n) = return (natToExprNamed n)
rename' (FunCallP (FNameParse f) args) = do
  args' <- sequence (rename' <$> args)
  return (FunCall f args')
rename' (GeneratorP sn args) = do
  args' <- sequence (rename' <$> args)
  renameDec <- renameGenerator sn
  case renameDec of
    Xtor sn  -> return $ Constr sn args'
    FCall sn -> return $ GenFunCall sn args'
rename' (ConsumerP str e args) = do
  e' <- rename' e
  args' <- sequence (rename' <$> args)
  renameDec <- renameConsumer str
  case renameDec of
    Xtor sn  -> return $ DestrCall sn e' args'
    FCall sn -> return $ ConsFunCall sn e' args'
rename' (MatchP qn e bl cases (TypeNameParse rtype)) = do
  e' <- rename' e
  bl' <- sequence (bindingListTrans <$> bl)
  cases' <- sequence (caseTrans (fst qn) <$> cases)
  return (Match qn e' bl' cases' rtype)
rename' (CoMatchP qn bl cocases) = do
  bl' <- sequence (bindingListTrans <$> bl)
  cocases' <- sequence (caseTrans (fst qn) <$> cocases)
  return (CoMatch qn bl' cocases')
rename' (LetP (VarNameParse str) e1 e2) = do
  e1' <- rename' e1
  e2' <- rename' e2
  return (Let str e1' e2')

-- | Rename one case of a PatternMatch/CoPatternMatch
caseTrans :: TypeName
          -> (SNameParse, [VarNameParse], ExprParse)
          -> RenamerM (ScopedName, [String], ExprNamed)
caseTrans tn (sn, cargs, expr) = do
  expr' <- rename' expr
  return (renameXtorName tn sn, unVarNameParse <$> cargs, expr')

-- | Rename one element of a bindingList
bindingListTrans :: (VarNameParse, ExprParse, TypeNameParse)
        -> RenamerM (String, ExprNamed, String)
bindingListTrans (varName, expr, typeName) = do
  expr' <- rename' expr
  return (unVarNameParse varName, expr', unTypeNameParse typeName)

-- Renaming decision
data RenameDec = Xtor ScopedName | FCall ScopedName

renameXtorName :: TypeName -> SNameParse -> ScopedName
renameXtorName _ (Local  (QNameExpl tn n)) = Coq_local  (tn, n)
renameXtorName _ (Global (QNameExpl tn n)) = Coq_global (tn, n)
renameXtorName tn (Local (QNameImpl n)) = Coq_local (tn,n)
renameXtorName tn (Global (QNameImpl n)) = Coq_global (tn,n)

renameGenerator :: SNameParse -> RenamerM RenameDec
renameGenerator (Local  (QNameExpl tn n)) =
  return $ Xtor (Coq_local (tn, n)) -- Local can only be xtor
renameGenerator (Global (QNameExpl tn n)) = do
  dts <- getDts
  if tn `elem` dts
  then return $ Xtor (Coq_global (tn,n))
  else return $ FCall (Coq_global (tn,n))
renameGenerator (Local  (QNameImpl str)) = do
  ctors <- getCtors
  case find (\(sn,_) -> snd (unscope sn) == str) ctors of
    Just (sn,_) -> return $ Xtor sn
    Nothing -> throwError $ "RenameGenerator: Cannot resolve the name " ++ str
renameGenerator (Global (QNameImpl str)) = do
  ctors <- getCtors
  g_gfun <- getGfunSigs
  case find (\(sn,_) -> snd (unscope sn) == str) ctors of
    Just (sn,_) -> return $ Xtor sn
    Nothing -> case find (\(qn,_) -> snd qn == str) g_gfun of
      Just (qn,_) -> return $ FCall (Coq_global qn)
      Nothing -> throwError $ "RenameGenerator: Cannot resolve the name " ++ str

renameConsumer :: SNameParse -> RenamerM RenameDec
renameConsumer (Local (QNameExpl tn n)) = return $ Xtor (Coq_local (tn, n)) -- Local can only be xtor
renameConsumer (Global (QNameExpl tn n)) = do
  cdts <- getCdts
  if tn `elem` cdts
  then return $ Xtor  (Coq_global (tn,n))
  else return $ FCall (Coq_global (tn,n))
renameConsumer (Local  (QNameImpl str)) =
  throwError $ "RenameGenerator: Cannot resolve the name " ++ str
renameConsumer (Global (QNameImpl str)) = do
  dtors <- getDtors
  g_cfun <- getCfunSigsG
  l_cfun <- getCfunSigsL
  case find (\((sn,_),_) -> snd (unscope sn) == str) dtors of
    Just ((sn,_),_) -> return  $ Xtor sn
    Nothing -> case find (\((qn,_),_) -> snd qn == str) g_cfun of
      Just ((qn,_),_) -> return $ FCall (Coq_global qn)
      Nothing -> case find (\((qn,_),_) -> snd qn == str) l_cfun of
        Just ((qn,_),_) -> return $ FCall (Coq_local qn)
        Nothing -> throwError $ "RenameConsumer: Cannot resolve the name " ++ str

