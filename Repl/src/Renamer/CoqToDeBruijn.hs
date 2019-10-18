module Renamer.CoqToDeBruijn
  (
    coqToDeBruijn
  , lookupArgs
  ) where

import HaskellAST
import AST
import Skeleton
import Names (ScopedName, TypeName, ScopedName(..))



lookupArgs :: ScopedName -> Coq_skeleton -> Either String [TypeName]
lookupArgs sn sk = case lookup sn (lookupScopedNamesSkeleton sk) of
  Just args -> Right args
  Nothing -> Left $ "lookupArgs: ScopedName " ++ show sn ++ " not in skeleton"

lookupNumArgs :: ScopedName -> Coq_skeleton -> Either String Int
lookupNumArgs sn sk =
  let scopedNames = (lookupScopedNamesSkeleton sk) in
  case (lookup sn scopedNames) of
    Just args -> Right $ length args
    Nothing -> Left $ "lookupNumArgs: ScopedName " ++ show sn ++ " not in skeleton"

lookupScopedNamesSkeleton :: Coq_skeleton -> [(ScopedName, [TypeName])]
lookupScopedNamesSkeleton sk =
  let
    ctors = (skeleton_ctors sk)
    dtors = (\((sn,args),_) -> (sn, args)) <$> (skeleton_dtors sk)
  in
    ctors ++ dtors

coqToDeBruijnBindingList :: Coq_skeleton -> [(Coq_expr, a)] -> Either String [((), ExprDB, a)]
coqToDeBruijnBindingList sk bl = sequence $ foo <$> bl
  where
    foo (e,tn) = do
      e' <- coqToDeBruijn sk e
      return ((), e',tn)

coqToDeBruijnCase :: Coq_skeleton -> (ScopedName, Coq_expr) -> Either String (ScopedName, [()], ExprDB)
coqToDeBruijnCase sk (sn,e) = do
  numArgs <- lookupNumArgs sn sk
  e' <- coqToDeBruijn sk e
  return $ (sn, replicate numArgs (), e')

-- | Convert a Coq_expr into a ExprDB.
-- An ExprDB contains more information than a Coq_expr, since the locations of
-- binding occurrances are explicitly marked with "()" in matches and comatches.
coqToDeBruijn :: Coq_skeleton -> Coq_expr -> Either String ExprDB
coqToDeBruijn _  (E_Var n) =
  return $ Var n
coqToDeBruijn sk (E_Constr n args) = do
  args' <- sequence (coqToDeBruijn sk <$> args)
  return $ Constr n args'
coqToDeBruijn sk (E_DestrCall n e args) = do
  e' <- coqToDeBruijn sk e
  args' <- sequence (coqToDeBruijn sk <$> args)
  return $ DestrCall n e' args'
coqToDeBruijn sk (E_FunCall n args) = do
  args' <- sequence (coqToDeBruijn sk <$> args)
  return $ FunCall n args'
coqToDeBruijn sk (E_GenFunCall n args) = do
  args' <- sequence (coqToDeBruijn sk <$> args)
  return $ GenFunCall n args'
coqToDeBruijn sk (E_ConsFunCall n e args) = do
  e' <- coqToDeBruijn sk e
  args' <- sequence (coqToDeBruijn sk <$> args)
  return $ ConsFunCall n e' args'
coqToDeBruijn sk (E_Match n e bl cases rtype) = do
  bl' <- coqToDeBruijnBindingList sk bl
  e'  <- coqToDeBruijn sk e
  newCases <- sequence (coqToDeBruijnCase sk <$> cases)
  return $ Match n e' bl' newCases rtype
coqToDeBruijn sk (E_CoMatch n bl cocases) = do
  bl' <- coqToDeBruijnBindingList sk bl
  newCocases <- sequence (coqToDeBruijnCase sk <$> cocases)
  return $ CoMatch n bl' newCocases
coqToDeBruijn sk (E_Let e1 e2) = do
  e1' <- coqToDeBruijn sk e1
  e2' <- coqToDeBruijn sk e2
  return $ Let () e1' e2'
