module DtorizeII where

import qualified Prelude
import qualified AST
import qualified Datatypes
import qualified List
import qualified Names

destructorize_expr :: Names.TypeName -> AST.Coq_expr -> AST.Coq_expr
destructorize_expr tn e =
  case e of {
   AST.E_Var n -> AST.E_Var n;
   AST.E_Constr sn es ->
    case Names.eq_TypeName tn (Datatypes.fst (Names.unscope sn)) of {
     Prelude.True -> AST.E_GenFunCall sn
      (List.map (destructorize_expr tn) es);
     Prelude.False -> AST.E_Constr sn (List.map (destructorize_expr tn) es)};
   AST.E_DestrCall sn e0 es -> AST.E_DestrCall sn (destructorize_expr tn e0)
    (List.map (destructorize_expr tn) es);
   AST.E_FunCall n es -> AST.E_FunCall n
    (List.map (destructorize_expr tn) es);
   AST.E_GenFunCall sn es -> AST.E_GenFunCall sn
    (List.map (destructorize_expr tn) es);
   AST.E_ConsFunCall sn e0 es ->
    case Names.eq_TypeName tn (Datatypes.fst (Names.unscope sn)) of {
     Prelude.True -> AST.E_DestrCall sn (destructorize_expr tn e0)
      (List.map (destructorize_expr tn) es);
     Prelude.False -> AST.E_ConsFunCall sn (destructorize_expr tn e0)
      (List.map (destructorize_expr tn) es)};
   AST.E_Match qn e0 bs cases t -> AST.E_Match qn (destructorize_expr tn e0)
    (List.map (\x -> (,) (destructorize_expr tn (Datatypes.fst x))
      (Datatypes.snd x)) bs)
    (List.map (\x -> (,) (Datatypes.fst x)
      (destructorize_expr tn (Datatypes.snd x))) cases) t;
   AST.E_CoMatch qn bs cocases -> AST.E_CoMatch qn
    (List.map (\x -> (,) (destructorize_expr tn (Datatypes.fst x))
      (Datatypes.snd x)) bs)
    (List.map (\x -> (,) (Datatypes.fst x)
      (destructorize_expr tn (Datatypes.snd x))) cocases);
   AST.E_Let e1 e2 -> AST.E_Let (destructorize_expr tn e1)
    (destructorize_expr tn e2)}

