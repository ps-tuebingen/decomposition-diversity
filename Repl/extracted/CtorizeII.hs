module CtorizeII where

import qualified Prelude
import qualified AST
import qualified Datatypes
import qualified List
import qualified Names

constructorize_expr :: Names.TypeName -> AST.Coq_expr -> AST.Coq_expr
constructorize_expr tn e =
  case e of {
   AST.E_Var n -> AST.E_Var n;
   AST.E_Constr sn es -> AST.E_Constr sn
    (List.map (constructorize_expr tn) es);
   AST.E_DestrCall sn e0 es ->
    case Names.eq_TypeName tn (Datatypes.fst (Names.unscope sn)) of {
     Prelude.True -> AST.E_ConsFunCall sn (constructorize_expr tn e0)
      (List.map (constructorize_expr tn) es);
     Prelude.False -> AST.E_DestrCall sn (constructorize_expr tn e0)
      (List.map (constructorize_expr tn) es)};
   AST.E_FunCall n es -> AST.E_FunCall n
    (List.map (constructorize_expr tn) es);
   AST.E_GenFunCall sn es ->
    case Names.eq_TypeName tn (Datatypes.fst (Names.unscope sn)) of {
     Prelude.True -> AST.E_Constr sn (List.map (constructorize_expr tn) es);
     Prelude.False -> AST.E_GenFunCall sn
      (List.map (constructorize_expr tn) es)};
   AST.E_ConsFunCall sn e0 es -> AST.E_ConsFunCall sn
    (constructorize_expr tn e0) (List.map (constructorize_expr tn) es);
   AST.E_Match qn e0 bs cases t -> AST.E_Match qn (constructorize_expr tn e0)
    (List.map (\x -> (,) (constructorize_expr tn (Datatypes.fst x))
      (Datatypes.snd x)) bs)
    (List.map (\x -> (,) (Datatypes.fst x)
      (constructorize_expr tn (Datatypes.snd x))) cases) t;
   AST.E_CoMatch qn bs cocases -> AST.E_CoMatch qn
    (List.map (\x -> (,) (constructorize_expr tn (Datatypes.fst x))
      (Datatypes.snd x)) bs)
    (List.map (\x -> (,) (Datatypes.fst x)
      (constructorize_expr tn (Datatypes.snd x))) cocases);
   AST.E_Let e1 e2 -> AST.E_Let (constructorize_expr tn e1)
    (constructorize_expr tn e2)}

