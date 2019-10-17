module Renamer.CoqToDeBruijn
  (
    coqToDeBruijn
  , lookupArgs
  ) where

import HaskellAST
import AST
import Skeleton
import Names (ScopedName, TypeName, ScopedName(..))



lookupArgs :: ScopedName -> Coq_skeleton -> [TypeName]
lookupArgs sn sk = case lookup sn (lookupScopedNamesSkeleton sk) of
  Just args -> args
  Nothing -> error "lookupNumArgs: ScopedName not in skeleton"

lookupNumArgs :: ScopedName -> Coq_skeleton -> Int
lookupNumArgs sn sk =
  let scopedNames = (lookupScopedNamesSkeleton sk) in
  case (lookup sn scopedNames) of
    Just args -> length args
    Nothing -> error $ "lookupNumArgs: ScopedName " ++ show sn ++ " not in skeleton"

lookupScopedNamesSkeleton :: Coq_skeleton -> [(ScopedName, [TypeName])]
lookupScopedNamesSkeleton sk =
  let
    ctors = (skeleton_ctors sk)
    dtors = (\((sn,args),_) -> (sn, args)) <$> (skeleton_dtors sk)
  in
    ctors ++ dtors


-- | Convert a Coq_expr into a ExprDB.
-- An ExprDB contains more information than a Coq_expr, since the locations of
-- binding occurrances are explicitly marked with "()" in matches and comatches.
coqToDeBruijn :: Coq_skeleton -> Coq_expr -> ExprDB
coqToDeBruijn _  (E_Var n) =
  Var n
coqToDeBruijn sk (E_Constr n args) =
  Constr n (coqToDeBruijn sk <$> args)
coqToDeBruijn sk (E_DestrCall n e args) =
  DestrCall n (coqToDeBruijn sk e) (coqToDeBruijn sk <$> args)
coqToDeBruijn sk (E_FunCall n args) =
  FunCall n (coqToDeBruijn sk <$> args)
coqToDeBruijn sk (E_GenFunCall n args) =
  GenFunCall n (coqToDeBruijn sk <$> args)
coqToDeBruijn sk (E_ConsFunCall n e args) =
  ConsFunCall n (coqToDeBruijn sk e) (coqToDeBruijn sk <$> args)
coqToDeBruijn sk (E_Match n e bl cases rtype) =
  let
    newBindingList :: [((),ExprDB, TypeName)]
    newBindingList = (\(e,tn) -> ((),coqToDeBruijn sk e,tn)) <$> bl
    newCases :: [(ScopedName, [()], ExprDB)]
    newCases = (\(sn,e) -> (sn,replicate (lookupNumArgs sn sk) (),coqToDeBruijn sk e)) <$> cases
  in
  Match n (coqToDeBruijn sk e) newBindingList newCases rtype
coqToDeBruijn sk (E_CoMatch n bl cocases) =
  let
    newBindingList :: [((),ExprDB, TypeName)]
    newBindingList = (\(e,tn) -> ((),coqToDeBruijn sk e,tn)) <$> bl
    newCocases :: [(ScopedName, [()], ExprDB)]
    newCocases = (\(sn,e) -> (sn,replicate (lookupNumArgs sn sk) (),coqToDeBruijn sk e)) <$> cocases
  in
  CoMatch n newBindingList newCocases
coqToDeBruijn sk (E_Let e1 e2) =
  Let () (coqToDeBruijn sk e1) (coqToDeBruijn sk e2)
