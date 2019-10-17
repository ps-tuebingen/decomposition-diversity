module Renamer.CoqToDeBruijn where

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
coqExpr2exprDB :: Coq_skeleton -> Coq_expr -> ExprDB
coqExpr2exprDB _  (E_Var n) =
  Var n
coqExpr2exprDB sk (E_Constr n args) =
  Constr n (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_DestrCall n e args) =
  DestrCall n (coqExpr2exprDB sk e) (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_FunCall n args) =
  FunCall n (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_GenFunCall n args) =
  GenFunCall n (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_ConsFunCall n e args) =
  ConsFunCall n (coqExpr2exprDB sk e) (coqExpr2exprDB sk <$> args)
coqExpr2exprDB sk (E_Match n e bl cases rtype) =
  let
    newBindingList :: [((),ExprDB, TypeName)]
    newBindingList = (\(e,tn) -> ((),coqExpr2exprDB sk e,tn)) <$> bl
    newCases :: [(ScopedName, [()], ExprDB)]
    newCases = (\(sn,e) -> (sn,replicate (lookupNumArgs sn sk) (),coqExpr2exprDB sk e)) <$> cases
  in
  Match n (coqExpr2exprDB sk e) newBindingList newCases rtype
coqExpr2exprDB sk (E_CoMatch n bl cocases) =
  let
    newBindingList :: [((),ExprDB, TypeName)]
    newBindingList = (\(e,tn) -> ((),coqExpr2exprDB sk e,tn)) <$> bl
    newCocases :: [(ScopedName, [()], ExprDB)]
    newCocases = (\(sn,e) -> (sn,replicate (lookupNumArgs sn sk) (),coqExpr2exprDB sk e)) <$> cocases
  in
  CoMatch n newBindingList newCocases
coqExpr2exprDB sk (E_Let e1 e2) =
  Let () (coqExpr2exprDB sk e1) (coqExpr2exprDB sk e2)
