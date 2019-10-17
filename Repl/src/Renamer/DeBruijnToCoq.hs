module Renamer.DeBruijnToCoq where

import HaskellAST
import AST

-- | Convert a ExprDB into a Coq_expr.
exprDB2CoqExpr :: ExprDB -> Coq_expr
exprDB2CoqExpr (Var n) = E_Var n
exprDB2CoqExpr (Constr n args) = E_Constr n (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (DestrCall n e args) = E_DestrCall n (exprDB2CoqExpr e) (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (FunCall n args) = E_FunCall n (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (GenFunCall n args) = E_GenFunCall n (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (ConsFunCall n e args) = E_ConsFunCall n (exprDB2CoqExpr e) (exprDB2CoqExpr <$> args)
exprDB2CoqExpr (Match n e bl cases rtype) =
  E_Match n (exprDB2CoqExpr e)
  ((\(_,e,n) -> (exprDB2CoqExpr e, n)) <$> bl) -- Binding List
  ((\(n,_,e) -> (n, exprDB2CoqExpr e)) <$> cases) -- Cases
  rtype
exprDB2CoqExpr (CoMatch n bl cocases) =
  E_CoMatch n
  ((\(_,e,n) -> (exprDB2CoqExpr e, n)) <$> bl) -- Binding List
  ((\(n,_,e) -> (n, exprDB2CoqExpr e)) <$> cocases) -- Cocases
exprDB2CoqExpr (Let _ e1 e2) = E_Let (exprDB2CoqExpr e1) (exprDB2CoqExpr e2)
