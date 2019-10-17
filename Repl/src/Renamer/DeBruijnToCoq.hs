module Renamer.DeBruijnToCoq
  (
    deBruijnToCoq
  ) where

import HaskellAST
import AST

-- | Convert a ExprDB into a Coq_expr.
deBruijnToCoq :: ExprDB -> Coq_expr
deBruijnToCoq (Var n) = E_Var n
deBruijnToCoq (Constr n args) = E_Constr n (deBruijnToCoq <$> args)
deBruijnToCoq (DestrCall n e args) = E_DestrCall n (deBruijnToCoq e) (deBruijnToCoq <$> args)
deBruijnToCoq (FunCall n args) = E_FunCall n (deBruijnToCoq <$> args)
deBruijnToCoq (GenFunCall n args) = E_GenFunCall n (deBruijnToCoq <$> args)
deBruijnToCoq (ConsFunCall n e args) = E_ConsFunCall n (deBruijnToCoq e) (deBruijnToCoq <$> args)
deBruijnToCoq (Match n e bl cases rtype) =
  E_Match n (deBruijnToCoq e)
  ((\(_,e,n) -> (deBruijnToCoq e, n)) <$> bl) -- Binding List
  ((\(n,_,e) -> (n, deBruijnToCoq e)) <$> cases) -- Cases
  rtype
deBruijnToCoq (CoMatch n bl cocases) =
  E_CoMatch n
  ((\(_,e,n) -> (deBruijnToCoq e, n)) <$> bl) -- Binding List
  ((\(n,_,e) -> (n, deBruijnToCoq e)) <$> cocases) -- Cocases
deBruijnToCoq (Let _ e1 e2) = E_Let (deBruijnToCoq e1) (deBruijnToCoq e2)
