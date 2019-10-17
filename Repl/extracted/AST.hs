module AST where

import qualified Prelude
import qualified List
import qualified Names
import qualified Nat

data Coq_expr =
   E_Var Names.VarName
 | E_Constr Names.ScopedName ([] Coq_expr)
 | E_DestrCall Names.ScopedName Coq_expr ([] Coq_expr)
 | E_FunCall Names.Name ([] Coq_expr)
 | E_GenFunCall Names.ScopedName ([] Coq_expr)
 | E_ConsFunCall Names.ScopedName Coq_expr ([] Coq_expr)
 | E_Match Names.QName Coq_expr ([] ((,) Coq_expr Names.TypeName)) ([]
                                                                   ((,)
                                                                   Names.ScopedName
                                                                   Coq_expr)) 
 Names.TypeName
 | E_CoMatch Names.QName ([] ((,) Coq_expr Names.TypeName)) ([]
                                                            ((,)
                                                            Names.ScopedName
                                                            Coq_expr))
 | E_Let Coq_expr Coq_expr

substitute' :: Prelude.Integer -> Coq_expr -> Coq_expr -> Coq_expr
substitute' n v e =
  let {curriedSubst = substitute' n v} in
  let {mapSubst = List.map curriedSubst} in
  let {
   mapBindingsSubst = List.map (\et ->
                        case et of {
                         (,) e0 t -> (,) (substitute' n v e0) t})}
  in
  case e of {
   E_Var n' ->
    case Nat.eqb n n' of {
     Prelude.True -> v;
     Prelude.False ->
      case Nat.ltb n n' of {
       Prelude.True -> E_Var
        (Nat.sub n' ((Prelude.+ 1) (0 :: Prelude.Integer)));
       Prelude.False -> E_Var n'}};
   E_Constr name cargs -> E_Constr name (mapSubst cargs);
   E_DestrCall name ex dargs -> E_DestrCall name (substitute' n v ex)
    (mapSubst dargs);
   E_FunCall name args -> E_FunCall name (mapSubst args);
   E_GenFunCall name args -> E_GenFunCall name (mapSubst args);
   E_ConsFunCall name ex args -> E_ConsFunCall name (substitute' n v ex)
    (mapSubst args);
   E_Match name ex bindings cases tn -> E_Match name (substitute' n v ex)
    (mapBindingsSubst bindings) cases tn;
   E_CoMatch name bindings cocases -> E_CoMatch name
    (mapBindingsSubst bindings) cocases;
   E_Let e1 e2 -> E_Let (substitute' n v e1)
    (substitute' (Nat.add n ((Prelude.+ 1) (0 :: Prelude.Integer))) v e2)}

substitute :: Coq_expr -> Coq_expr -> Coq_expr
substitute v e =
  substitute' (0 :: Prelude.Integer) v e

multi_subst :: ([] Coq_expr) -> Coq_expr -> Coq_expr
multi_subst vs e =
  case vs of {
   [] -> e;
   (:) v vs0 -> multi_subst vs0 (substitute v e)}

