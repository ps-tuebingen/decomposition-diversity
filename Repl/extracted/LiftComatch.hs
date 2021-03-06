module LiftComatch where

import qualified Prelude
import qualified AST
import qualified BodyTypeDefs
import qualified Datatypes
import qualified List
import qualified Names
import qualified PeanoNat
import qualified ProgramDef
import qualified Skeleton
import qualified Specif

replace_comatches_by_gfun_calls :: Names.TypeName -> AST.Coq_expr ->
                                   AST.Coq_expr
replace_comatches_by_gfun_calls tn e =
  case e of {
   AST.E_Var x -> AST.E_Var x;
   AST.E_Constr sn args -> AST.E_Constr sn
    (List.map (replace_comatches_by_gfun_calls tn) args);
   AST.E_DestrCall sn e' args -> AST.E_DestrCall sn
    (replace_comatches_by_gfun_calls tn e')
    (List.map (replace_comatches_by_gfun_calls tn) args);
   AST.E_FunCall n args -> AST.E_FunCall n
    (List.map (replace_comatches_by_gfun_calls tn) args);
   AST.E_GenFunCall sn args -> AST.E_GenFunCall sn
    (List.map (replace_comatches_by_gfun_calls tn) args);
   AST.E_ConsFunCall sn e' args -> AST.E_ConsFunCall sn
    (replace_comatches_by_gfun_calls tn e')
    (List.map (replace_comatches_by_gfun_calls tn) args);
   AST.E_Match qn' e0 bs cases rtype -> AST.E_Match qn'
    (replace_comatches_by_gfun_calls tn e0)
    (List.map (\exp_typ -> (,)
      (replace_comatches_by_gfun_calls tn (Datatypes.fst exp_typ))
      (Datatypes.snd exp_typ)) bs)
    (List.map (\sn_exp -> (,) (Datatypes.fst sn_exp)
      (replace_comatches_by_gfun_calls tn (Datatypes.snd sn_exp))) cases)
    rtype;
   AST.E_CoMatch qn bs cocases ->
    case Names.eq_TypeName tn (Datatypes.fst qn) of {
     Prelude.True -> AST.E_GenFunCall (Names.Coq_local qn)
      (List.map (\b -> replace_comatches_by_gfun_calls tn (Datatypes.fst b))
        bs);
     Prelude.False -> AST.E_CoMatch qn
      (List.map (\exp_typ -> (,)
        (replace_comatches_by_gfun_calls tn (Datatypes.fst exp_typ))
        (Datatypes.snd exp_typ)) bs)
      (List.map (\sn_exp -> (,) (Datatypes.fst sn_exp)
        (replace_comatches_by_gfun_calls tn (Datatypes.snd sn_exp))) cocases)};
   AST.E_Let e1 e2 -> AST.E_Let (replace_comatches_by_gfun_calls tn e1)
    (replace_comatches_by_gfun_calls tn e2)}

generate_gfuns_from_expr :: Names.TypeName -> AST.Coq_expr -> []
                            ((,) Skeleton.Coq_gfun_sig
                            BodyTypeDefs.Coq_gfun_bod_named)
generate_gfuns_from_expr tn e =
  case e of {
   AST.E_Var _ -> [];
   AST.E_Constr _ args ->
    List.concat (List.map (generate_gfuns_from_expr tn) args);
   AST.E_DestrCall _ e0 args ->
    Datatypes.app (generate_gfuns_from_expr tn e0)
      (List.concat (List.map (generate_gfuns_from_expr tn) args));
   AST.E_FunCall _ args ->
    List.concat (List.map (generate_gfuns_from_expr tn) args);
   AST.E_GenFunCall _ args ->
    List.concat (List.map (generate_gfuns_from_expr tn) args);
   AST.E_ConsFunCall _ e0 args ->
    Datatypes.app (generate_gfuns_from_expr tn e0)
      (List.concat (List.map (generate_gfuns_from_expr tn) args));
   AST.E_Match _ e0 bs cases _ ->
    Datatypes.app (generate_gfuns_from_expr tn e0)
      (Datatypes.app
        (List.concat
          (List.map (\exp_typ ->
            generate_gfuns_from_expr tn (Datatypes.fst exp_typ)) bs))
        (List.concat
          (List.map (\sn_exp ->
            generate_gfuns_from_expr tn (Datatypes.snd sn_exp)) cases)));
   AST.E_CoMatch qn bs cocases ->
    Datatypes.app
      (case Names.eq_TypeName tn (Datatypes.fst qn) of {
        Prelude.True ->
         let {sig = (,) qn (List.map Datatypes.snd bs)} in
         let {
          bod = List.map (\sn_exp -> (,) (Datatypes.fst sn_exp)
                  (replace_comatches_by_gfun_calls tn (Datatypes.snd sn_exp)))
                  cocases}
         in
         (:) ((,) sig ((,) qn bod)) [];
        Prelude.False -> []})
      (Datatypes.app
        (List.concat
          (List.map (\exp_typ ->
            generate_gfuns_from_expr tn (Datatypes.fst exp_typ)) bs))
        (List.concat
          (List.map (\sn_exp ->
            generate_gfuns_from_expr tn (Datatypes.snd sn_exp)) cocases)));
   AST.E_Let e1 e2 ->
    Datatypes.app (generate_gfuns_from_expr tn e1)
      (generate_gfuns_from_expr tn e2)}

new_gfuns_from_funs :: ProgramDef.Coq_program -> Names.TypeName -> []
                       ((,) Skeleton.Coq_gfun_sig
                       BodyTypeDefs.Coq_gfun_bod_named)
new_gfuns_from_funs p tn =
  let {funbods = List.map Datatypes.snd (ProgramDef.program_fun_bods p)} in
  List.concat (List.map (generate_gfuns_from_expr tn) funbods)

new_gfuns_from_gfuns :: ProgramDef.Coq_program -> Names.TypeName -> []
                        ((,) Skeleton.Coq_gfun_sig
                        BodyTypeDefs.Coq_gfun_bod_named)
new_gfuns_from_gfuns p tn =
  let {
   gfuncases = List.concat
                 (List.map Datatypes.snd (ProgramDef.program_gfun_bods_g p))}
  in
  let {gfunbods = List.map Datatypes.snd gfuncases} in
  List.concat (List.map (generate_gfuns_from_expr tn) gfunbods)

new_gfuns_from_cfuns :: ProgramDef.Coq_program -> Names.TypeName -> []
                        ((,) Skeleton.Coq_gfun_sig
                        BodyTypeDefs.Coq_gfun_bod_named)
new_gfuns_from_cfuns p tn =
  let {
   cfuncases = List.concat
                 (List.map Datatypes.snd (ProgramDef.program_cfun_bods_g p))}
  in
  let {cfunbods = List.map Datatypes.snd cfuncases} in
  List.concat (List.map (generate_gfuns_from_expr tn) cfunbods)

new_gfuns :: ProgramDef.Coq_program -> Names.TypeName -> []
             ((,) Skeleton.Coq_gfun_sig BodyTypeDefs.Coq_gfun_bod_named)
new_gfuns p tn =
  Datatypes.app (new_gfuns_from_funs p tn)
    (Datatypes.app (new_gfuns_from_gfuns p tn) (new_gfuns_from_cfuns p tn))

new_gfun_sigs :: ProgramDef.Coq_program -> Names.TypeName -> []
                 Skeleton.Coq_gfun_sig
new_gfun_sigs p tn =
  Datatypes.app
    (Skeleton.skeleton_gfun_sigs_l (ProgramDef.program_skeleton p))
    (List.map Datatypes.fst (new_gfuns p tn))

lift_comatch_to_skeleton :: ProgramDef.Coq_program -> Names.TypeName ->
                            Skeleton.Coq_skeleton
lift_comatch_to_skeleton p tn =
  let {old_skeleton = ProgramDef.program_skeleton p} in
  Skeleton.Coq_mkSkeleton (Skeleton.skeleton_dts old_skeleton)
  (Skeleton.skeleton_ctors old_skeleton)
  (Skeleton.skeleton_cdts old_skeleton)
  (Skeleton.skeleton_dtors old_skeleton)
  (Skeleton.skeleton_fun_sigs old_skeleton)
  (Skeleton.skeleton_cfun_sigs_g old_skeleton)
  (Skeleton.skeleton_cfun_sigs_l old_skeleton)
  (Skeleton.skeleton_gfun_sigs_g old_skeleton) (new_gfun_sigs p tn)

new_gfun_bods_l :: ProgramDef.Coq_program -> Names.TypeName ->
                   BodyTypeDefs.Coq_gfun_bods
new_gfun_bods_l p tn =
  Datatypes.app
    (List.map Datatypes.snd
      (List.flat_map (generate_gfuns_from_expr tn)
        (List.map Datatypes.snd (ProgramDef.program_fun_bods p))))
    (Datatypes.app
      (List.map Datatypes.snd
        (List.flat_map (generate_gfuns_from_expr tn)
          (List.map Datatypes.snd
            (List.flat_map Datatypes.snd (ProgramDef.program_gfun_bods_g p)))))
      (List.map Datatypes.snd
        (List.flat_map (generate_gfuns_from_expr tn)
          (List.map Datatypes.snd
            (List.flat_map Datatypes.snd (ProgramDef.program_cfun_bods_g p))))))

lift_comatch_to_program :: ProgramDef.Coq_program -> Names.TypeName ->
                           ProgramDef.Coq_program
lift_comatch_to_program p tn =
  case PeanoNat._Nat__eq_dec
         (Datatypes.length
           (Skeleton.skeleton_gfun_sigs_l (ProgramDef.program_skeleton p)))
         (0 :: Prelude.Integer) of {
   Specif.Coq_left ->
    case PeanoNat._Nat__eq_dec
           (Datatypes.length
             (Skeleton.skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn)))
           (0 :: Prelude.Integer) of {
     Specif.Coq_left -> ProgramDef.Coq_mkProgram
      (lift_comatch_to_skeleton p tn)
      (List.map (\x -> (,) (Datatypes.fst x)
        (replace_comatches_by_gfun_calls tn (Datatypes.snd x)))
        (ProgramDef.program_fun_bods p))
      (List.map (\x -> (,) (Datatypes.fst x)
        (List.map (\y -> (,) (Datatypes.fst y)
          (replace_comatches_by_gfun_calls tn (Datatypes.snd y)))
          (Datatypes.snd x))) (ProgramDef.program_cfun_bods_g p)) []
      (List.map (\x -> (,) (Datatypes.fst x)
        (List.map (\y -> (,) (Datatypes.fst y)
          (replace_comatches_by_gfun_calls tn (Datatypes.snd y)))
          (Datatypes.snd x))) (ProgramDef.program_gfun_bods_g p))
      (new_gfun_bods_l p tn);
     Specif.Coq_right -> p};
   Specif.Coq_right -> p}

