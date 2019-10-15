
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Sorting.Permutation.

Require Import GenericTactics.
Require Import GenericLemmas.
Require Import Names.
Require Import AST.
Require Import BodyTypeDefs.
Require Import Skeleton.
Require Import ProgramDef.
Require Import Unique.
Require Import Sublist.
Require Import Subterm.
Require Import Typechecker.
Require Import Permutations.

Require Import InlineComatch.
Require Import LiftComatch.

Fixpoint extract_local_gfuns_expr (e : expr) : list QName :=
  match e with
  | E_Var x => []
  | E_Constr _ args => concat (map extract_local_gfuns_expr args)
  | E_DestrCall _ e args => (extract_local_gfuns_expr e) ++ (concat (map extract_local_gfuns_expr args))
  | E_FunCall _ args => concat (map extract_local_gfuns_expr args)
  | E_GenFunCall _ args => concat (map extract_local_gfuns_expr args)
  | E_ConsFunCall _ e args => (extract_local_gfuns_expr e) ++ (concat (map extract_local_gfuns_expr args))
  | E_Match qn e bs cases rtype =>
    (extract_local_gfuns_expr e)
      ++ (concat (map (fun exp_typ => extract_local_gfuns_expr (fst exp_typ)) bs))
      ++ (concat (map (fun sn_exp => extract_local_gfuns_expr (snd sn_exp)) cases))
  | E_CoMatch qn bs cocases =>
    (concat (map (fun exp_typ => extract_local_gfuns_expr (fst exp_typ)) bs))
      ++ (concat (map (fun sn_exp => extract_local_gfuns_expr (snd sn_exp)) cocases))
  | E_Let e1 e2 => (extract_local_gfuns_expr e1) ++ (extract_local_gfuns_expr e2)
  end.

Definition extract_local_gfuns_program (p : program) : list QName :=
  (flat_map extract_local_gfuns_expr (map snd (program_fun_bods p)))
  ++ (flat_map extract_local_gfuns_expr (map snd (flat_map snd (program_gfun_bods_g p))))
  ++ (flat_map extract_local_gfuns_expr (map snd (flat_map snd (program_gfun_bods_g p)))).
  
Definition sort_gfuns_for_inline (p : program) (cs: gfun_bods) : gfun_bods :=
  let qns := extract_local_gfuns_program p in
  let fuel := length cs in
  let fix extract_new cs qn :=
      match cs with
      | [] => []
      | (c::cs') =>
        if eq_QName qn (fst c)
        then flat_map (fun x => extract_local_gfuns_expr (snd x)) (snd c)
        else extract_new cs' qn
      end in
  let fix worker n qns :=
      match n with
      | 0 => []
      | S n => let new_qns := map (extract_new cs) qns in
              let new_rec := map (worker n) new_qns in
              concat (zipWith cons qns new_rec)
      end in
  sort_by_index_list (fun qn bod => eq_QName qn (fst bod))  (worker fuel qns) cs.

Lemma sort_gfuns_for_inline_permutes: forall (p : program),
    Permutation (program_gfun_bods_l p) (sort_gfuns_for_inline p (program_gfun_bods_l p)).
Proof.
Admitted. (* check Results.v for details on missing proofs *)

Definition new_gfun_sigs_l (s : skeleton) (qns: list QName) :=
  sort_by_index_list (fun qn sig => eq_QName qn (fst sig)) qns (skeleton_gfun_sigs_l s).

Lemma new_gfun_sigs_in_cdts_l: forall (s : skeleton) (qns : list QName)
                                (H: Permutation qns (map fst (skeleton_gfun_sigs_l s))),
    gfun_sigs_in_cdts (skeleton_cdts s) (new_gfun_sigs_l s qns).
Proof.
  intros s qns H.
  unfold gfun_sigs_in_cdts.
  unfold new_gfun_sigs_l.
  eapply Permutation_Forall;
  [ | pose proof (skeleton_gfun_sigs_in_cdts_l s); unfold gfun_sigs_in_cdts in H0; eauto].
  apply sort_by_index_list_permutes.
  exists fst; split; auto.
  clear; intros a b.
  split; apply eq_QName_eq; auto.
Qed.

Lemma new_gfun_sigs_names_unique_l: forall (s : skeleton) (qns : list QName)
                                (H: Permutation qns (map fst (skeleton_gfun_sigs_l s))),
    gfun_sigs_names_unique (new_gfun_sigs_l s qns).
Proof.
  intros s qns H.
  pose proof (skeleton_gfun_sigs_names_unique_l s).
  unfold gfun_sigs_names_unique in *.
  unfold new_gfun_sigs_l.
  eapply Permutation_unique; [| eassumption].
  apply Permutation_map.
  apply sort_by_index_list_permutes.
  exists fst; split; auto.
  clear; intros a b.
  split; apply eq_QName_eq.
Qed.

Definition sort_gfuns_for_inline_skeleton (s : skeleton) (qns: list QName)
           (H: Permutation qns (map fst (skeleton_gfun_sigs_l s)))
            : skeleton :=
  let gfun_sigs := new_gfun_sigs_l s qns in
  {|
    skeleton_dts := skeleton_dts s;
    skeleton_ctors := skeleton_ctors s;
    skeleton_dts_ctors_in_dts := skeleton_dts_ctors_in_dts s;
    skeleton_dts_ctor_names_unique := skeleton_dts_ctor_names_unique s;
    skeleton_cdts := skeleton_cdts s;
    skeleton_dtors := skeleton_dtors s;
    skeleton_cdts_dtors_in_cdts := skeleton_cdts_dtors_in_cdts s;
    skeleton_cdts_dtor_names_unique := skeleton_cdts_dtor_names_unique s;
    skeleton_dts_cdts_disjoint := skeleton_dts_cdts_disjoint s;
    skeleton_fun_sigs := skeleton_fun_sigs s;
    skeleton_fun_sigs_names_unique := skeleton_fun_sigs_names_unique s;
    skeleton_cfun_sigs_g := skeleton_cfun_sigs_g s;
    skeleton_cfun_sigs_in_dts_g := skeleton_cfun_sigs_in_dts_g s;
    skeleton_cfun_sigs_names_unique_g := skeleton_cfun_sigs_names_unique_g s;
    skeleton_cfun_sigs_l := skeleton_cfun_sigs_l s;
    skeleton_cfun_sigs_in_dts_l := skeleton_cfun_sigs_in_dts_l s;
    skeleton_cfun_sigs_names_unique_l := skeleton_cfun_sigs_names_unique_l s;
    skeleton_gfun_sigs_g := skeleton_gfun_sigs_g s;
    skeleton_gfun_sigs_in_cdts_g := skeleton_gfun_sigs_in_cdts_g s;
    skeleton_gfun_sigs_names_unique_g := skeleton_gfun_sigs_names_unique_g s;
    skeleton_gfun_sigs_l := gfun_sigs;
    skeleton_gfun_sigs_in_cdts_l := new_gfun_sigs_in_cdts_l s qns H;
    skeleton_gfun_sigs_names_unique_l := new_gfun_sigs_names_unique_l s qns H;
  |}.

Definition sort_gfuns_for_inline_bods (p : program) : gfun_bods :=
  sort_gfuns_for_inline p (program_gfun_bods_l p).

Lemma sorted_gfuns_permutation_of_original_sigs: forall (p : program),
    Permutation (map fst (sort_gfuns_for_inline_bods p))
                (map fst (skeleton_gfun_sigs_l (program_skeleton p))).
Proof.
  intros p.
  unfold sort_gfuns_for_inline_bods.
  pose proof (sort_gfuns_for_inline_permutes p).
  apply (Permutation_map fst) in H.
  apply Permutation_sym in H.
  eapply (perm_trans); [ eassumption | ].
  pose proof (program_has_all_gfun_bods_l p).
  unfold has_all_gfun_bods in H0; rewrite H0; auto.
Qed.

Lemma sort_gfuns_for_inline_bods_Permutation_with_gfun_bods: forall (p : program),
    Permutation (program_gfun_bods_l p) (sort_gfuns_for_inline_bods p).
Proof.
  intros p.
  unfold sort_gfuns_for_inline_bods.
  apply sort_gfuns_for_inline_permutes.
Qed.

Definition new_skeleton (p : program) :=
  let sorted := sort_gfuns_for_inline_bods p in
  sort_gfuns_for_inline_skeleton (program_skeleton p) (map fst sorted) (sorted_gfuns_permutation_of_original_sigs p).

Lemma new_skeleton_tc:
  forall (p : program) (e : expr) (ctxt : list TypeName) (t : TypeName),
    (program_skeleton p / ctxt |- e : t) ->
    new_skeleton p / ctxt |- e : t.
Proof.
  intros p e ctxt t H.
  unfold new_skeleton.
  gen_dep (ctxt, t);
    induction e using expr_strong_ind; intros;
      match goal with
      | [ H: _ / _ |- _ : _ |- _ ] =>
        inversion_clear H
      end.
  - apply T_Var; auto.
  - eapply T_Constr; eauto.
    clear H1.
    gen_induction cargs ls.
    + inversion_clear H2.
      apply ListTypeDeriv_Nil.
    + destruct cargs; inversion_clear H2.
      inversion_clear H.
      apply ListTypeDeriv_Cons; auto.
  - eapply T_DestrCall; eauto.
    clear H1.
    gen_induction dargs ls; destruct dargs; inversion_clear H3; try apply ListTypeDeriv_Nil.
    inversion_clear H.
    apply ListTypeDeriv_Cons; auto.
  - eapply T_FunCall; eauto.
    clear H1.
    gen_induction argts ls; destruct argts; inversion_clear H2; try apply ListTypeDeriv_Nil.
    inversion_clear H.
    apply ListTypeDeriv_Cons; auto.
  - eapply T_GlobalConsFunCall; eauto.
    clear H1.
    gen_induction argts ls; destruct argts; inversion_clear H3; try apply ListTypeDeriv_Nil.
    inversion_clear H.
    apply ListTypeDeriv_Cons; auto.
  - eapply T_LocalConsFunCall; eauto.
    clear H1.
    gen_induction argts ls; destruct argts; inversion_clear H3; try apply ListTypeDeriv_Nil.
    inversion_clear H.
    apply ListTypeDeriv_Cons; auto.
  - eapply T_GlobalGenFunCall; eauto.
    clear H1.
    gen_induction argts ls; destruct argts; inversion_clear H2; try apply ListTypeDeriv_Nil.
    inversion_clear H.
    apply ListTypeDeriv_Cons; auto.
  - eapply T_LocalGenFunCall; eauto.
    + match goal with
      | [ H: In _ ?ls |- In _ ?ls'] =>
        eapply Permutation_in; [ | eassumption ]
      end.
      unfold sort_gfuns_for_inline_skeleton; simpl.
      unfold new_gfun_sigs_l.
      apply sort_by_index_list_permutes.
      exists fst; split; [ | intros; split; apply eq_QName_eq ].
      apply sorted_gfuns_permutation_of_original_sigs.
    + clear H1.
    gen_induction argts ls; destruct argts; inversion_clear H2; try apply ListTypeDeriv_Nil.
    inversion_clear H.
    apply ListTypeDeriv_Cons; auto.
  - eapply T_Match; eauto.
    + subst. clear - H4 H0.
      gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion_clear H4; try apply ListTypeDeriv_Nil.
      simpl in H0; inversion_clear H0.
      apply ListTypeDeriv_Cons; auto.
    + clear - H7 H.
      gen_induction ctorlist ls; destruct ctorlist; inversion_clear H7; try apply ListTypeDeriv'_Nil.
      inversion_clear H; simpl.
      apply ListTypeDeriv'_Cons; auto.
  - eapply T_CoMatch; eauto.
    + subst. clear - H3 H0.
      gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion_clear H3; try apply ListTypeDeriv_Nil.
      simpl in H0; inversion_clear H0.
      apply ListTypeDeriv_Cons; auto.
    + clear - H6 H.
      gen_induction dtorlist ls; destruct dtorlist; inversion_clear H6; try apply ListTypeDeriv'_Nil.
      inversion_clear H; simpl.
      apply ListTypeDeriv'_Cons; auto.
  - eapply T_Let; eauto.
Qed.

Lemma new_program_fun_bods_tc: forall (p : program),
    fun_bods_typecheck (new_skeleton p) (program_fun_bods p).
Proof.
  intros p.
  pose proof (program_fun_bods_typecheck p).
  unfold fun_bods_typecheck in *.
  match goal with
  | [ H: Forall ?P1 ?ls |- Forall ?P2 ?ls ] =>
    apply (@Forall_impl _ P1); auto
  end.
  clear; intros a H.
  repeat match goal with
         | [ H: exists _, _ |- _ ] =>
           inversion_clear H
         end.
  inversion_clear H0.
  repeat eexists; eauto.
  apply new_skeleton_tc; assumption.
Qed.

Lemma new_program_cfun_bods_g_tc: forall (p : program),
    cfun_bods_g_typecheck (new_skeleton p) (program_cfun_bods_g p).
Proof.
  intros p.
  pose proof (program_cfun_bods_typecheck_g p).
  unfold cfun_bods_g_typecheck in *.
  match goal with
  | [ H: Forall ?P1 ?ls |- Forall ?P2 ?ls ] =>
    apply (@Forall_impl _ P1); auto
  end.
  clear; intros a H.
  repeat match goal with
         | [ H: exists _, _ |- _ ] =>
           inversion_clear H
         end.
  inversion_clear H0.
  repeat eexists; eauto.
  apply new_skeleton_tc; assumption.
Qed.

Lemma new_program_cfun_bods_l_tc: forall (p : program),
    cfun_bods_l_typecheck (new_skeleton p) (program_cfun_bods_l p).
Proof.
  intros p.
  pose proof (program_cfun_bods_typecheck_l p).
  unfold cfun_bods_l_typecheck in *.
  match goal with
  | [ H: Forall ?P1 ?ls |- Forall ?P2 ?ls ] =>
    apply (@Forall_impl _ P1); auto
  end.
  clear; intros a H.
  repeat match goal with
         | [ H: exists _, _ |- _ ] =>
           inversion_clear H
         end.
  inversion_clear H0.
  repeat eexists; eauto.
  apply new_skeleton_tc; assumption.
Qed.

Lemma new_program_gfun_bods_g_tc: forall (p : program),
    gfun_bods_g_typecheck (new_skeleton p) (program_gfun_bods_g p).
Proof.
  intros p.
  pose proof (program_gfun_bods_typecheck_g p).
  unfold gfun_bods_g_typecheck in *.
  match goal with
  | [ H: Forall ?P1 ?ls |- Forall ?P2 ?ls ] =>
    apply (@Forall_impl _ P1); auto
  end.
  clear; intros a H.
  repeat match goal with
         | [ H: exists _, _ |- _ ] =>
           inversion_clear H
         end.
  inversion_clear H.
  repeat eexists; eauto.
  apply new_skeleton_tc; assumption.
Qed.

Lemma new_program_gfun_bods_l_tc: forall (p : program),
    gfun_bods_l_typecheck (new_skeleton p) (sort_gfuns_for_inline_bods p).
Proof.
  intros p.
  pose proof (program_gfun_bods_typecheck_l p).
  unfold gfun_bods_l_typecheck in *.
  match goal with
  | [ H: Forall ?P1 _ |- Forall ?P2 _ ] =>
    apply (@Forall_impl _ P1); auto
  end.
  - clear; intros a H.
    repeat match goal with
           | [ H: exists _, _ |- _ ] =>
             inversion_clear H
           end.
    inversion_clear H.
    repeat eexists; eauto;
      [ | apply new_skeleton_tc; eassumption].
    unfold new_skeleton.
    pose proof UtilsSkeleton.lookup_gfun_sig_name_correct_l as E.
    specialize (E _ _ _ H0); simpl in *; subst.
    unfold sort_gfuns_for_inline_skeleton; simpl;
    unfold UtilsSkeleton.lookup_gfun_sig_l in *;
    unfold UtilsSkeleton.lookup_gfun_sig_x in *; simpl.
    pose proof (skeleton_gfun_sigs_names_unique_l (program_skeleton p)) as H;
      unfold gfun_sigs_names_unique in H.
    match goal with
    | [ H: find _ ?l' = Some ?sig |- find _ ?l = Some _ ] => 
      eapply (unique_sig_lookup l sig)
    end.
    + apply find_in in H0.
      unfold new_gfun_sigs_l.
      eapply Permutation_in; [ | eassumption].
      apply sort_by_index_list_permutes.
      exists fst; split;
        [ | clear; intros; split; apply eq_QName_eq ].
      apply sorted_gfuns_permutation_of_original_sigs.
    + match goal with
      | [ H: unique ?ls |- _ ] =>
        apply (Permutation_unique ls); auto
      end.
      apply Permutation_map.
      unfold new_gfun_sigs_l.
      apply sort_by_index_list_permutes.
      exists fst; split;
        [ | clear; intros; split; apply eq_QName_eq ].
      apply sorted_gfuns_permutation_of_original_sigs.
  - match goal with
    | [ H: Forall ?P ?ls |- Forall ?P ?ls' ] =>
      apply (Permutation_Forall P ls); auto
    end.
    apply  sort_gfuns_for_inline_bods_Permutation_with_gfun_bods.
Qed.

Lemma new_program_has_all_gfun_bods_l: forall (p : program),
    has_all_gfun_bods (skeleton_gfun_sigs_l (new_skeleton p)) (sort_gfuns_for_inline_bods p).
Proof.
  intros p.
  pose proof (program_has_all_gfun_bods_l p).
  unfold has_all_gfun_bods in *.
  unfold new_skeleton.
  unfold sort_gfuns_for_inline_skeleton; simpl.
  unfold new_gfun_sigs_l.
  pose proof (skeleton_gfun_sigs_names_unique_l (program_skeleton p)).
  unfold gfun_sigs_names_unique in H0.
  rewrite H in H0.
  match goal with
  | [  |- context [sort_by_index_list ?f ?index ?to_sort] ] => 
    apply (sort_by_index_list_sorted_like_index f index to_sort)
  end;
   [ unfold sort_gfuns_for_inline_bods;
    match goal with
    | [ H: unique ?ls |- _ ] =>
      apply (Permutation_unique ls); auto
    end;
    apply Permutation_map;
    apply sort_gfuns_for_inline_permutes
    | apply sorted_gfuns_permutation_of_original_sigs
    | intros; split; apply eq_QName_eq ].
Qed.

Lemma new_program_match_names_unique: forall (p : program),
    match_names_unique (program_fun_bods p)
                       (program_cfun_bods_g p ++ program_cfun_bods_l p)
                       (program_gfun_bods_g p ++ (sort_gfuns_for_inline_bods p)).
Proof.
  intros p.
  pose proof (program_match_names_unique p).
  unfold match_names_unique in *.
  repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
  match goal with
  | [ H: unique ?ls |- unique ?ls' ] =>
    apply (Permutation_unique ls); eauto
  end.
  repeat apply Permutation_app; auto.
  repeat (repeat apply Permutation_concat; apply Permutation_map).
  apply sort_gfuns_for_inline_bods_Permutation_with_gfun_bods.
Qed.

Lemma new_program_comatch_names_unique: forall (p : program),
    comatch_names_unique (program_fun_bods p)
                         (program_cfun_bods_g p ++ program_cfun_bods_l p)
                         (program_gfun_bods_g p ++ (sort_gfuns_for_inline_bods p)).
Proof.
  intros p.
  pose proof (program_comatch_names_unique p).
  unfold comatch_names_unique in *.
  repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
  match goal with
  | [ H: unique ?ls |- unique ?ls' ] =>
    apply (Permutation_unique ls); eauto
  end.
  repeat apply Permutation_app; auto.
  repeat (repeat apply Permutation_concat; apply Permutation_map).
  apply sort_gfuns_for_inline_bods_Permutation_with_gfun_bods.
Qed.

Definition sort_gfuns_for_inline_program (p : program) : program :=
  let sorted := sort_gfuns_for_inline_bods p in
  let new_skel := new_skeleton p in
  {|
    program_skeleton := new_skel;
    program_fun_bods := program_fun_bods p;
    program_has_all_fun_bods := program_has_all_fun_bods p;
    program_fun_bods_typecheck := new_program_fun_bods_tc p;
    program_cfun_bods_g := program_cfun_bods_g p;
    program_has_all_cfun_bods_g := program_has_all_cfun_bods_g p;
    program_cfun_bods_typecheck_g := new_program_cfun_bods_g_tc p;
    program_cfun_bods_l := program_cfun_bods_l p;
    program_has_all_cfun_bods_l := program_has_all_cfun_bods_l p;
    program_cfun_bods_typecheck_l := new_program_cfun_bods_l_tc p;
    program_gfun_bods_g := program_gfun_bods_g p;
    program_has_all_gfun_bods_g := program_has_all_gfun_bods_g p;
    program_gfun_bods_typecheck_g := new_program_gfun_bods_g_tc p;
    program_gfun_bods_l := sorted;
    program_has_all_gfun_bods_l := new_program_has_all_gfun_bods_l p;
    program_gfun_bods_typecheck_l := new_program_gfun_bods_l_tc p;
    program_match_names_unique := new_program_match_names_unique p;
    program_comatch_names_unique := new_program_comatch_names_unique p;
  |}.

Lemma contains_at_most_list_Permutation: forall (qn : QName) (ls ls' : list expr),
    Permutation ls ls' ->
    contains_at_most_one_local_gfun_call_list qn ls ->
    contains_at_most_one_local_gfun_call_list qn ls'.
Proof.
  intros qn ls ls' H_per H_most.
  inversion_clear H_most as [H_no|H_one]; [ left; eapply Permutation_Forall; eauto | right ].
  induction H_per; auto.
  - inversion_clear H_one.
    + apply contains_one_local_gfun_call_list_here; auto.
      eapply Permutation_Forall; eauto.
    + apply contains_one_local_gfun_call_list_there; auto.
  - repeat match goal with
           | [ H: contains_one_local_gfun_call_list _ (_ :: _) |- _ ] =>
             inversion_clear H
           end;
      repeat match goal with
             | [ H: Forall _ (_ :: _) |- _ ] =>
               inversion_clear H
             end.
    + apply contains_one_local_gfun_call_list_there; auto.
      apply contains_one_local_gfun_call_list_here; auto.
    + apply contains_one_local_gfun_call_list_here; auto.
    + repeat apply contains_one_local_gfun_call_list_there; auto.
Qed.

Lemma sort_gfuns_for_inline_preserves_local_gfuns_only_used_once: forall (p : program),
    local_gfuns_only_used_once p ->
    local_gfuns_only_used_once (sort_gfuns_for_inline_program p).
Proof.
  intros p H.
  unfold local_gfuns_only_used_once in *.
  unfold sort_gfuns_for_inline_program in *; simpl.
  unfold new_gfun_sigs_l.
  match goal with
  | [ H: Forall ?P1 _ |- Forall ?P2 ?ls ] =>
    apply (@Forall_impl _ P1)
  end.
  - intro qn.
    apply contains_at_most_list_Permutation.
    repeat apply Permutation_app; auto.
    apply Permutation_map.
    repeat rewrite flat_map_concat_map.
    apply Permutation_concat.
    apply Permutation_map.
    apply sort_gfuns_for_inline_bods_Permutation_with_gfun_bods.
  - match goal with
    | [ H: Forall ?P ?ls |- Forall ?P ?ls' ] => 
      eapply (Permutation_Forall P); [ | eapply H]
    end.
    apply Permutation_map.
    apply sort_by_index_list_permutes.
    exists fst; split;
      [ | clear; intros; split; apply eq_QName_eq].
    apply sorted_gfuns_permutation_of_original_sigs.
Qed.

Lemma sort_gfuns_for_inline_ordered_gfun: forall (p : program),
    local_gfuns_only_used_once p ->
    inline_ordered_gfun (sort_gfuns_for_inline_bods p).
Proof.
  intros p H.
  unfold sort_gfuns_for_inline_bods.
  unfold sort_gfuns_for_inline.
Admitted. (* check Results.v for details on missing proofs *)

Theorem sort_gfuns_for_inline_program_ordered_gfun: forall (p : program),
    local_gfuns_only_used_once p ->
    inline_ordered_gfun (program_gfun_bods_l (sort_gfuns_for_inline_program p)).
Proof.
  intros p H. simpl.
  apply sort_gfuns_for_inline_ordered_gfun; assumption.
Qed.
