module SwitchIndices where

import qualified Prelude
import qualified AST
import qualified Datatypes
import qualified List
import qualified Names
import qualified Nat
import qualified PeanoNat
import qualified Skeleton
import qualified UtilsSkeleton

switch_indices_helper :: AST.Coq_expr -> Skeleton.Coq_skeleton ->
                         Prelude.Integer -> Prelude.Integer ->
                         Prelude.Integer -> AST.Coq_expr
switch_indices_helper e p m n b =
  case e of {
   AST.E_Var v ->
    let {b0 = PeanoNat._Nat__ltb v b} in
    case b0 of {
     Prelude.True -> AST.E_Var v;
     Prelude.False ->
      let {b1 = PeanoNat._Nat__ltb v (Nat.add b n)} in
      case b1 of {
       Prelude.True -> AST.E_Var (Nat.add v m);
       Prelude.False -> AST.E_Var (Nat.sub v n)}};
   AST.E_Constr s l -> AST.E_Constr s
    (List.map (\e0 -> switch_indices_helper e0 p m n b) l);
   AST.E_DestrCall s e0 l -> AST.E_DestrCall s
    (switch_indices_helper e0 p m n b)
    (List.map (\e1 -> switch_indices_helper e1 p m n b) l);
   AST.E_FunCall n0 l -> AST.E_FunCall n0
    (List.map (\e0 -> switch_indices_helper e0 p m n b) l);
   AST.E_GenFunCall s l -> AST.E_GenFunCall s
    (List.map (\e0 -> switch_indices_helper e0 p m n b) l);
   AST.E_ConsFunCall s e0 l -> AST.E_ConsFunCall s
    (switch_indices_helper e0 p m n b)
    (List.map (\e1 -> switch_indices_helper e1 p m n b) l);
   AST.E_Match q e0 l l0 t -> AST.E_Match q
    (switch_indices_helper e0 p m n b)
    (List.map (\x -> (,) (switch_indices_helper (Datatypes.fst x) p m n b)
      (Datatypes.snd x)) l) l0 t;
   AST.E_CoMatch q l l0 -> AST.E_CoMatch q
    (List.map (\x -> (,) (switch_indices_helper (Datatypes.fst x) p m n b)
      (Datatypes.snd x)) l) l0;
   AST.E_Let e1 e2 -> AST.E_Let (switch_indices_helper e1 p m n b)
    (switch_indices_helper e2 p m n
      (Nat.add b ((Prelude.+ 1) (0 :: Prelude.Integer))))}

switch_indices :: AST.Coq_expr -> Skeleton.Coq_skeleton -> Names.ScopedName
                  -> Prelude.Integer -> AST.Coq_expr
switch_indices e p sn n =
  case UtilsSkeleton.lookup_gfun_sig_scoped p sn of {
   Prelude.Just g ->
    switch_indices_helper e p (Datatypes.length (Datatypes.snd g)) n
      (0 :: Prelude.Integer);
   Prelude.Nothing -> e}

switch_indices_cfun :: AST.Coq_expr -> Skeleton.Coq_skeleton ->
                       Names.ScopedName -> Prelude.Integer -> AST.Coq_expr
switch_indices_cfun e p sn n =
  case UtilsSkeleton.lookup_cfun_sig_scoped p sn of {
   Prelude.Just c ->
    switch_indices_helper e p
      (Datatypes.length (Datatypes.snd (Datatypes.fst c))) n
      (0 :: Prelude.Integer);
   Prelude.Nothing -> e}

