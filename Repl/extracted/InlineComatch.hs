module InlineComatch where

import qualified Prelude
import qualified AST
import qualified BodyTypeDefs
import qualified Datatypes
import qualified List
import qualified Names
import qualified ProgramDef
import qualified Skeleton

replace_gfun_call_by_comatch :: Names.ScopedName -> ([]
                                ((,) Names.ScopedName AST.Coq_expr)) -> ([]
                                Names.TypeName) -> AST.Coq_expr ->
                                AST.Coq_expr
replace_gfun_call_by_comatch snr cocases bts e =
  case e of {
   AST.E_Var x -> AST.E_Var x;
   AST.E_Constr sn args -> AST.E_Constr sn
    (List.map (replace_gfun_call_by_comatch snr cocases bts) args);
   AST.E_DestrCall sn e' args -> AST.E_DestrCall sn
    (replace_gfun_call_by_comatch snr cocases bts e')
    (List.map (replace_gfun_call_by_comatch snr cocases bts) args);
   AST.E_FunCall n args -> AST.E_FunCall n
    (List.map (replace_gfun_call_by_comatch snr cocases bts) args);
   AST.E_GenFunCall sn args ->
    case Names.eq_ScopedName snr sn of {
     Prelude.True -> AST.E_CoMatch (Names.unscope sn) (List.combine args bts)
      cocases;
     Prelude.False -> AST.E_GenFunCall sn
      (List.map (replace_gfun_call_by_comatch snr cocases bts) args)};
   AST.E_ConsFunCall sn e' args -> AST.E_ConsFunCall sn
    (replace_gfun_call_by_comatch snr cocases bts e')
    (List.map (replace_gfun_call_by_comatch snr cocases bts) args);
   AST.E_Match qn e' bs cases rtype -> AST.E_Match qn
    (replace_gfun_call_by_comatch snr cocases bts e')
    (List.map (\exp_typ -> (,)
      (replace_gfun_call_by_comatch snr cocases bts (Datatypes.fst exp_typ))
      (Datatypes.snd exp_typ)) bs)
    (List.map (\sn_exp -> (,) (Datatypes.fst sn_exp)
      (replace_gfun_call_by_comatch snr cocases bts (Datatypes.snd sn_exp)))
      cases) rtype;
   AST.E_CoMatch qn bs cocases' -> AST.E_CoMatch qn
    (List.map (\exp_typ -> (,)
      (replace_gfun_call_by_comatch snr cocases bts (Datatypes.fst exp_typ))
      (Datatypes.snd exp_typ)) bs)
    (List.map (\sn_exp -> (,) (Datatypes.fst sn_exp)
      (replace_gfun_call_by_comatch snr cocases bts (Datatypes.snd sn_exp)))
      cocases');
   AST.E_Let e1 e2 -> AST.E_Let
    (replace_gfun_call_by_comatch snr cocases bts e1)
    (replace_gfun_call_by_comatch snr cocases bts e2)}

replace_local_gfun_calls :: BodyTypeDefs.Coq_gfun_bods ->
                            Skeleton.Coq_gfun_sigs -> AST.Coq_expr ->
                            AST.Coq_expr
replace_local_gfun_calls gfuns sigs e =
  case gfuns of {
   [] -> e;
   (:) bod bods ->
    case sigs of {
     [] -> e;
     (:) sig sigs0 ->
      replace_local_gfun_calls bods sigs0
        (replace_gfun_call_by_comatch (Names.Coq_local (Datatypes.fst bod))
          (Datatypes.snd bod) (Datatypes.snd sig) e)}}

contains_no_local_gfun_call_b :: Names.QName -> AST.Coq_expr -> Prelude.Bool
contains_no_local_gfun_call_b qn e =
  case e of {
   AST.E_Var _ -> Prelude.True;
   AST.E_Constr _ es -> List.forallb (contains_no_local_gfun_call_b qn) es;
   AST.E_DestrCall _ e' es ->
    Datatypes.andb (contains_no_local_gfun_call_b qn e')
      (List.forallb (contains_no_local_gfun_call_b qn) es);
   AST.E_FunCall _ es -> List.forallb (contains_no_local_gfun_call_b qn) es;
   AST.E_GenFunCall sn es ->
    Datatypes.andb
      (Datatypes.negb (Names.eq_ScopedName sn (Names.Coq_local qn)))
      (List.forallb (contains_no_local_gfun_call_b qn) es);
   AST.E_ConsFunCall _ e' es ->
    Datatypes.andb (contains_no_local_gfun_call_b qn e')
      (List.forallb (contains_no_local_gfun_call_b qn) es);
   AST.E_Match _ e' bs cs _ ->
    Datatypes.andb
      (Datatypes.andb (contains_no_local_gfun_call_b qn e')
        (List.forallb (\x ->
          contains_no_local_gfun_call_b qn (Datatypes.fst x)) bs))
      (List.forallb (\x ->
        contains_no_local_gfun_call_b qn (Datatypes.snd x)) cs);
   AST.E_CoMatch _ bs ccs ->
    Datatypes.andb
      (List.forallb (\x ->
        contains_no_local_gfun_call_b qn (Datatypes.fst x)) bs)
      (List.forallb (\x ->
        contains_no_local_gfun_call_b qn (Datatypes.snd x)) ccs);
   AST.E_Let e1 e2 ->
    Datatypes.andb (contains_no_local_gfun_call_b qn e1)
      (contains_no_local_gfun_call_b qn e2)}

inline_gfuns_to_skeleton_partial :: ProgramDef.Coq_program ->
                                    Skeleton.Coq_gfun_sigs ->
                                    Skeleton.Coq_skeleton
inline_gfuns_to_skeleton_partial p gfuns =
  let {old_skeleton = ProgramDef.program_skeleton p} in
  Skeleton.Coq_mkSkeleton (Skeleton.skeleton_dts old_skeleton)
  (Skeleton.skeleton_ctors old_skeleton)
  (Skeleton.skeleton_cdts old_skeleton)
  (Skeleton.skeleton_dtors old_skeleton)
  (Skeleton.skeleton_fun_sigs old_skeleton)
  (Skeleton.skeleton_cfun_sigs_g old_skeleton)
  (Skeleton.skeleton_cfun_sigs_l old_skeleton)
  (Skeleton.skeleton_gfun_sigs_g old_skeleton) gfuns

inline_gfuns_to_skeleton :: ProgramDef.Coq_program -> Skeleton.Coq_skeleton
inline_gfuns_to_skeleton p =
  inline_gfuns_to_skeleton_partial p []

replace_local_gfun_calls_prog :: ProgramDef.Coq_program -> AST.Coq_expr ->
                                 AST.Coq_expr
replace_local_gfun_calls_prog p =
  replace_local_gfun_calls (ProgramDef.program_gfun_bods_l p)
    (Skeleton.skeleton_gfun_sigs_l (ProgramDef.program_skeleton p))

new_skeleton :: ProgramDef.Coq_program -> Skeleton.Coq_skeleton
new_skeleton =
  inline_gfuns_to_skeleton

new_fun_bods :: ProgramDef.Coq_program -> BodyTypeDefs.Coq_fun_bods
new_fun_bods p =
  List.map (\x -> (,) (Datatypes.fst x)
    (replace_local_gfun_calls_prog p (Datatypes.snd x)))
    (ProgramDef.program_fun_bods p)

new_cfun_bods_g :: ProgramDef.Coq_program -> BodyTypeDefs.Coq_cfun_bods
new_cfun_bods_g p =
  List.map (\x -> (,) (Datatypes.fst x)
    (List.map (\y -> (,) (Datatypes.fst y)
      (replace_local_gfun_calls_prog p (Datatypes.snd y))) (Datatypes.snd x)))
    (ProgramDef.program_cfun_bods_g p)

new_cfun_bods_l :: ProgramDef.Coq_program -> BodyTypeDefs.Coq_cfun_bods
new_cfun_bods_l p =
  List.map (\x -> (,) (Datatypes.fst x)
    (List.map (\y -> (,) (Datatypes.fst y)
      (replace_local_gfun_calls_prog p (Datatypes.snd y))) (Datatypes.snd x)))
    (ProgramDef.program_cfun_bods_l p)

new_gfun_bods_g :: ProgramDef.Coq_program -> BodyTypeDefs.Coq_gfun_bods
new_gfun_bods_g p =
  List.map (\x -> (,) (Datatypes.fst x)
    (List.map (\y -> (,) (Datatypes.fst y)
      (replace_local_gfun_calls_prog p (Datatypes.snd y))) (Datatypes.snd x)))
    (ProgramDef.program_gfun_bods_g p)

new_gfun_bods_l :: ProgramDef.Coq_program -> BodyTypeDefs.Coq_gfun_bods
new_gfun_bods_l _ =
  []

inline_gfuns_to_program :: ProgramDef.Coq_program -> ProgramDef.Coq_program
inline_gfuns_to_program p =
  ProgramDef.Coq_mkProgram (new_skeleton p) (new_fun_bods p)
    (new_cfun_bods_g p) (new_cfun_bods_l p) (new_gfun_bods_g p)
    (new_gfun_bods_l p)

