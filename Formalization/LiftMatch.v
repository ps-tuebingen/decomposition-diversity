(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: LiftMatch.v                                                                              *)
(*                                                                                                *)
(**************************************************************************************************)

Require Coq.Arith.EqNat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Names.
Require Import AST.
Require Import Subterm.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import BodyTypeDefs.
Require Import ProgramDef.
Require Import UtilsProgram.
Require Import GenericLemmas.
Require Import GenericTactics.
Require Import Typechecker.
Require Import UtilsTypechecker.
Require Import Unique.
Require Import Sublist.

Fixpoint replace_matches_by_cfun_calls (tn : TypeName) (e : expr) : expr :=
  match e with
  | E_Var x => E_Var x
  | E_Constr sn args => E_Constr sn (map (replace_matches_by_cfun_calls tn) args)
  | E_DestrCall sn e' args => E_DestrCall sn (replace_matches_by_cfun_calls tn e') (map (replace_matches_by_cfun_calls tn) args)
  | E_FunCall n args => E_FunCall n (map (replace_matches_by_cfun_calls tn) args)
  | E_GenFunCall sn args => E_GenFunCall sn (map (replace_matches_by_cfun_calls tn) args)
  | E_ConsFunCall sn e' args => E_ConsFunCall sn (replace_matches_by_cfun_calls tn e') (map (replace_matches_by_cfun_calls tn) args)
  | E_Match qn e bs cases rtype =>
    if (eq_TypeName tn (fst qn))
    then E_ConsFunCall (local qn) (replace_matches_by_cfun_calls tn e) (map (fun b => (replace_matches_by_cfun_calls tn (fst b))) bs)
    else E_Match qn
                 (replace_matches_by_cfun_calls tn e)
                 (map (fun exp_typ => (replace_matches_by_cfun_calls tn (fst exp_typ), snd exp_typ)) bs)
                 (map (fun sn_exp => (fst sn_exp, replace_matches_by_cfun_calls tn (snd sn_exp))) cases)
                 rtype
  | E_CoMatch qn bs cocases =>
    E_CoMatch qn
              (map (fun exp_typ => (replace_matches_by_cfun_calls tn (fst exp_typ), snd exp_typ)) bs)
              (map (fun sn_exp => (fst sn_exp, replace_matches_by_cfun_calls tn (snd sn_exp))) cocases)
  | E_Let e1 e2 => E_Let (replace_matches_by_cfun_calls tn e1) (replace_matches_by_cfun_calls tn e2)
  end.

(* Generate the set of new cfun_sigs and cfun_bods for a given expression *)
Fixpoint generate_cfuns_from_expr (tn : TypeName) (e : expr) : list (cfun_sig * cfun_bod_named) :=
  match e with
  | E_Var x => []
  | E_Constr _ args => concat (map (generate_cfuns_from_expr tn) args)
  | E_DestrCall _ e args => (generate_cfuns_from_expr tn e) ++ (concat (map (generate_cfuns_from_expr tn) args))
  | E_FunCall _ args => concat (map (generate_cfuns_from_expr tn) args)
  | E_GenFunCall _ args => concat (map (generate_cfuns_from_expr tn) args)
  | E_ConsFunCall _ e args => (generate_cfuns_from_expr tn e) ++ (concat (map (generate_cfuns_from_expr tn) args))
  | E_Match qn e bs cases rtype =>
    (if (eq_TypeName tn (fst qn))
    then let sig : cfun_sig := (qn, map snd bs, rtype) in
         let bod : cfun_bod := map (fun sn_exp => (fst sn_exp, replace_matches_by_cfun_calls tn (snd sn_exp))) cases in
         [(sig, (qn, bod))]
     else [])
      ++ (generate_cfuns_from_expr tn e)
      ++ (concat (map (fun exp_typ => generate_cfuns_from_expr tn (fst exp_typ)) bs))
      ++ (concat (map (fun sn_exp => generate_cfuns_from_expr tn (snd sn_exp)) cases))
  | E_CoMatch qn bs cocases =>
      (concat (map (fun exp_typ => generate_cfuns_from_expr tn (fst exp_typ)) bs))
      ++ (concat (map (fun sn_exp => generate_cfuns_from_expr tn (snd sn_exp)) cocases))
  | E_Let e1 e2 => (generate_cfuns_from_expr tn e1) ++ (generate_cfuns_from_expr tn e2)
  end.

Lemma lift_match_subst: forall (e e' : expr) (tn : TypeName) (n : nat),
    replace_matches_by_cfun_calls tn (substitute' n e e') =
    substitute' n (replace_matches_by_cfun_calls tn e)
                (replace_matches_by_cfun_calls tn e').
Proof.
  intros e e' tn n.
  generalize dependent n;
  induction e' using expr_strong_ind; intro; simpl;
  try solve [
        f_equal; auto;
        do 2 rewrite map_map;
        apply map_ext_in; intros;
        rewrite Forall_forall in H; auto].
  - repeat match_destruct_tac; auto.
  - name_destruct_tac; simpl; f_equal; auto.
    + clear - H0; induction es; auto; simpl; inversion_clear H0; f_equal; auto.
      destruct a; simpl; auto.
    + clear - H0; induction es; auto; simpl; inversion_clear H0; f_equal; auto.
      destruct a; simpl; f_equal; auto.
  - f_equal; auto.
    repeat rewrite map_map.
    clear - H0.
    induction es; auto; inversion_clear H0; simpl; f_equal; auto.
    destruct a; simpl in *; f_equal; auto.
Qed.

Ltac concat_map_induction_tac :=
  match goal with
  | [ H : Forall ?P ?ls |- Forall ?P' (concat (map ?f ?ls)) ] =>
    induction ls; try apply Forall_nil;
    inversion H; subst; clear H;
    apply Forall_app; auto
  end.


Lemma generate_cfuns_from_expr_names_match : forall (tn : TypeName) (e : expr),
    Forall (fun sig_bod => (fst (fst (fst sig_bod))) = (fst (snd (sig_bod)))) (generate_cfuns_from_expr tn e).
Proof with try apply Forall_app; try apply Forall_nil; auto; try IH_auto_tac.
  intros tn e; induction e using expr_strong_ind; simpl; try apply Forall_nil;
    try apply Forall_app; try auto; try concat_map_induction_tac.
  - destruct (eq_TypeName tn (fst n))...
  - apply Forall_app...
    + clear - H0; induction es; inversion H0...
    + clear - H; induction ls; inversion H...
  - clear - H0; induction es; inversion H0...
  - clear - H; induction ls; inversion H...
Qed.


(* Property holds of expression e, if e does not contain comatches on given codata type. *)
Definition contains_no_matches (tn : TypeName) (e : expr) : Prop :=
  filter (fun x => eq_TypeName tn (fst x)) (collect_match_names e) = [].

Lemma replace_matches_by_cfun_calls_removes_all_matches : forall (e : expr) (tn : TypeName),
    contains_no_matches tn (replace_matches_by_cfun_calls tn e).
Proof.
  intros e tn.
  unfold contains_no_matches.
  induction e using expr_strong_ind; auto;
    simpl;
    try (unfold QName in *);
         try rewrite concat_app;
         try
           match goal with
           | [ H: filter _ ?l = [] |- filter _ (?l ++ ?r) = [] ] =>
             rewrite filter_app; rewrite H; simpl
           end;
         repeat
           match goal with
           | [ H: Forall (fun x => _ = []) ?ls |- filter _ (concat (map _ (map _ ?ls))) = [] ] =>
             let IH := fresh in
             let head := fresh in
             let tail := fresh in
             let E := fresh in
             let Es := fresh in
             let a := fresh in
             let b := fresh in
             induction ls as [| head tail IH]; try reflexivity; simpl; rewrite filter_app;
             inversion H as [| a b E Es]; subst; rewrite E; simpl; apply IH; auto
           end.
         - name_destruct_tac.
           + simpl. rewrite filter_app. unfold QName in *; rewrite IHe. simpl.
             clear H IHe; induction es; try reflexivity.
             simpl. inversion_clear H0. rewrite filter_app.
             unfold fst at 2; unfold QName in *; rewrite H.
             simpl. apply IHes; assumption.
           + simpl. rewrite E__name. repeat rewrite concat_app. repeat rewrite filter_app.
             unfold QName in *; rewrite IHe. simpl; clear IHe.
             induction es; simpl.
             * induction ls; try reflexivity; simpl.
               inversion_clear H. rewrite filter_app.
               unfold snd at 1; unfold QName in *; rewrite H1; simpl.
               apply IHls; assumption.
             * inversion_clear H0. rewrite filter_app.
               unfold fst at 2; unfold QName in *; rewrite H1; simpl.
               apply IHes; assumption.
         - rewrite filter_app.
           repeat rewrite map_map.
           induction es; simpl.
           + induction ls; try reflexivity; simpl.
             inversion H; subst. unfold snd at 1. rewrite filter_app; rewrite H3; simpl.
             apply IHls; assumption.
           + inversion H0; subst. unfold fst at 2. rewrite filter_app; rewrite H3; simpl.
             apply IHes; assumption.
         - rewrite IHe2; auto.
Qed.

Lemma generate_cfuns_from_expr_contains_no_matches : forall (e : expr) (tn : TypeName),
    Forall (fun sig_bod => Forall (fun sn_exp => contains_no_matches tn (snd sn_exp)) (snd(snd sig_bod))) (generate_cfuns_from_expr tn e).
Proof.
  intros e tn.
  induction e using expr_strong_ind; try apply Forall_nil;
    simpl; repeat apply Forall_app; try assumption;
      try solve [repeat (match goal with
                         | [ H: Forall (fun x => Forall _ _) _ |- _ ] => apply Forall_flatten in H
                         end); try assumption];
      try match goal with
          | [ |- Forall (fun x => Forall _ _) _ ] => apply Forall_flatten; assumption
          end;
      try solve [ match goal with
                  | [ H: Forall _ (map _ ?ls) |- Forall _ (concat (map _ ?ls)) ] =>
                    clear - H; induction ls; try apply Forall_nil;
                    inversion_clear H; simpl; apply Forall_app; try assumption;
                    IH_auto_tac
                  end].
  name_destruct_tac; try apply Forall_nil.
  apply Forall_cons; try apply Forall_nil; simpl.
  clear - H. induction ls; try apply Forall_nil.
  inversion_clear H; simpl. apply Forall_cons; simpl.
  - apply replace_matches_by_cfun_calls_removes_all_matches.
  - IH_auto_tac.
Qed.

(**************************************************************************************************)
(* ** Construct the new program with lifted data type                                           *)
(*                                                                                                *)
(**************************************************************************************************)

Lemma new_cfun_sigs_from_expr_in_dts : forall (sk : skeleton) (tn : TypeName) (e : expr),
    (exists ctxt t, (sk / ctxt |- e : t)) ->
    cfun_sigs_in_dts (skeleton_dts sk) (map fst (generate_cfuns_from_expr tn e)).
Proof with try reflexivity; try assumption; try apply Forall_nil; eauto; try solve [Forall_tail_tac]; try IH_auto_tac.
  intros sk tn e H. induction e using expr_strong_ind; simpl.
  - (* E_Var *)
    apply Forall_nil.
  - (* E_Constr *)
    destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst. clear H2 H_typecheck.
    generalize dependent cargs. induction ls; intros; try apply Forall_nil.
    inversion H5; subst. clear H5. simpl. rewrite map_app. inversion H0; subst.
    apply Forall_app.
    + apply H2. exists ctxt. exists t. assumption.
    + eapply IHls; try auto. apply H7.
  - (* E_DestrCall *)
    destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst. clear H_typecheck H5.
    rewrite map_app. apply Forall_app.
    + clear - IHe H7. apply IHe. exists ctxt. exists (fst (unscope n)). assumption.
    + clear - H0 H8.
      generalize dependent dargs. induction ls; intros; try apply Forall_nil.
      inversion H8; subst. clear H8. simpl. rewrite map_app. inversion H0; subst.
      apply Forall_app.
      * apply H2. exists ctxt. exists t. assumption.
      * eapply IHls; try auto. apply H6.
  - (* E_FunCall *)
    destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst. clear H4 H_typecheck.
    generalize dependent argts. induction ls; intros; try apply Forall_nil.
    inversion H6; subst. clear H6. simpl. rewrite map_app. inversion H0; subst.
    apply Forall_app.
    + apply H2. exists ctxt. exists t0. assumption.
    + eapply IHls; try auto. apply H7.
  - (* E_ConsFuncall *)
    destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst.
    + clear H_typecheck H5.
      rewrite map_app. apply Forall_app.
      * clear - IHe H7. apply IHe. exists ctxt. exists (fst qn). assumption.
      * clear - H0 H8.
        generalize dependent argts. induction ls; intros; try apply Forall_nil.
        inversion H8; subst. clear H8. simpl. rewrite map_app. inversion H0; subst.
        apply Forall_app.
        -- apply H2. exists ctxt. exists t. assumption.
        -- eapply IHls; try auto. apply H6.
    + clear H_typecheck H5.
      rewrite map_app. apply Forall_app.
      * clear - IHe H7. apply IHe. exists ctxt. exists (fst qn). assumption.
      * clear - H0 H8.
        generalize dependent argts. induction ls; intros; try apply Forall_nil.
        inversion H8; subst. clear H8. simpl. rewrite map_app. inversion H0; subst.
        apply Forall_app.
        -- apply H2. exists ctxt. exists t. assumption.
        -- eapply IHls; try auto. apply H6.
  - (* E_GenFunCall *)
    destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst.
    + clear H4 H_typecheck.
      generalize dependent argts. induction ls; intros; try apply Forall_nil.
      inversion H6; subst. clear H6. simpl. rewrite map_app. inversion H0; subst.
      apply Forall_app.
      * apply H2. exists ctxt. exists t. assumption.
      * eapply IHls; try auto. apply H7.
    + clear H4 H_typecheck.
      generalize dependent argts. induction ls; intros; try apply Forall_nil.
      inversion H6; subst. clear H6. simpl. rewrite map_app. inversion H0; subst.
      apply Forall_app.
      * apply H2. exists ctxt. exists t. assumption.
      * eapply IHls; try auto. apply H7.
  - (* E_Match *)
    inversion H as [ctxt [t H_t]]; clear H.
    name_destruct_tac; simpl.
    + unfold cfun_sigs_in_dts in *.
      apply Forall_cons; simpl.
      * inversion H_t; subst.
        apply lookup_ctors_in_dts in H12...
      * do 2 (rewrite map_app). apply Forall_app; [> | apply Forall_app]...
        -- IH_tac ltac:(do 2 eexists; inversion H_t; subst; eauto).
        -- inversion H_t; clear H_t; subst. clear H14.
           remember (combine bindings_exprs bindings_types) as es;
                                              gen_induction (bindings_exprs, bindings_types) es...
           simpl; rewrite map_app; apply Forall_app; subst;
              destruct bindings_exprs, bindings_types; inversion Heqes.
           ++ simpl in H1; inversion H1; subst. IH_tac.
              inversion H11; subst...
           ++ rewrite <- H3; apply IHes with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types)...
              inversion H11...
        -- inversion H_t; subst; clear H_t H12.
           gen_induction ctorlist ls...
           simpl; rewrite map_app; apply Forall_app.
           ++ inversion H0; subst. apply H3.
              inversion H14...
           ++ destruct ctorlist; inversion H14; subst. apply IHls with (ctorlist := ctorlist)...
    + inversion H_t; subst; clear H_t.
      do 2 (rewrite map_app). apply Forall_app; [> | apply Forall_app]...
      * IH_tac...
      * clear H14. remember (combine bindings_exprs bindings_types) as es;
          gen_induction (bindings_exprs, bindings_types) es...
        simpl; rewrite map_app; apply Forall_app.
        -- inversion H1... IH_tac.
           destruct bindings_exprs, bindings_types; inversion Heqes; subst; inversion H11...
        -- destruct bindings_exprs, bindings_types; inversion Heqes. rewrite <- H3. inversion H11.
           apply IHes with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types)...
      * clear H12. gen_induction ctorlist ls...
        simpl; rewrite map_app; apply Forall_app.
        -- inversion H0; apply H3; inversion H14...
        --  destruct ctorlist; try solve [inversion H14];
              inversion H14; inversion H0; inversion H13.
            IH_auto_tac.
  - (* E_Comatch *)
    inversion H as [ctxt [t H_t]]; clear H; inversion_clear H_t; subst.
    rewrite map_app; apply Forall_app.
    + clear H5; remember (combine bindings_exprs bindings_types) as es;
        gen_induction (bindings_exprs, bindings_types) es...
      simpl; rewrite map_app; apply Forall_app...
      * destruct bindings_exprs, bindings_types; try solve [inversion Heqes].
        inversion H1; IH_tac. inversion Heqes; inversion H2...
      * destruct bindings_exprs, bindings_types; inversion Heqes; subst.
        inversion H1; inversion H2; subst.
        apply IHes with (bindings_exprs0 := bindings_exprs) (bindings_types0 := bindings_types)...
    + clear H2 H3.
      gen_induction dtorlist ls...
      simpl; rewrite map_app; apply Forall_app; destruct dtorlist; try solve [inversion H5].
      * inversion H0. inversion H5... IH_tac...
      * inversion_clear H0; inversion_clear H4; inversion_clear H5; IH_auto_tac.
  - (* E_Let *)
    rewrite map_app. destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst.
    apply Forall_app.
    + apply IHe1. exists ctxt. exists t1. assumption.
    + apply IHe2. exists (t1 :: ctxt). exists t. assumption.
Qed.


Definition new_cfuns_from_funs (p : program) (tn : TypeName) : list (cfun_sig * cfun_bod_named) :=
  let funbods : list expr := map snd (program_fun_bods p) in
  concat (map (generate_cfuns_from_expr tn) funbods).

Lemma new_cfun_sigs_from_funs_in_dts : forall (p : program) (tn : TypeName),
    cfun_sigs_in_dts (skeleton_dts (program_skeleton p)) (map fst (new_cfuns_from_funs p tn)).
Proof.
  intros p tn. unfold cfun_sigs_in_dts. unfold new_cfuns_from_funs.
  pose proof (program_fun_bods_typecheck p).
  induction (program_fun_bods p); try apply Forall_nil.
 simpl. rewrite map_app. inversion H; subst. apply Forall_app.
  - apply new_cfun_sigs_from_expr_in_dts. clear - H2. destruct H2 as [n [args [t [_ H_typecheck]]]].
    exists args. exists t. assumption.
  - apply IHf. inversion H; subst. assumption.
Qed.


Definition new_cfuns_from_cfuns (p : program) (tn : TypeName) : list (cfun_sig * cfun_bod_named) :=
  let cfuncases : list (ScopedName * expr) := concat (map snd (program_cfun_bods_g p)) in
  let cfunbods : list expr := map snd cfuncases in
  concat (map (generate_cfuns_from_expr tn) cfunbods).

Lemma new_cfun_sigs_from_cfuns_in_dts : forall (p : program) (tn : TypeName),
    cfun_sigs_in_dts (skeleton_dts (program_skeleton p)) (map fst (new_cfuns_from_cfuns p tn)).
Proof.
  intros p tn. unfold cfun_sigs_in_dts. unfold new_cfuns_from_cfuns.
  pose proof (program_cfun_bods_typecheck_g p).
  induction (program_cfun_bods_g p); simpl; try apply Forall_nil.
  inversion H; subst.
  repeat rewrite map_app. rewrite concat_app. rewrite map_app. apply Forall_app.
  - clear - H2. destruct a as [a_qn a_bod]; simpl in *. destruct H2 as [qn [args [t H_typecheck]]].
    inversion H_typecheck; subst.
    inversion_clear H0.
    generalize dependent (map (fun ctor => snd ctor ++ bindings_types) ctorlist).
    generalize dependent (map snd ctorlist).
    clear H_typecheck H5.
    induction a_bod; intros; try apply Forall_nil; simpl.
    rewrite map_app. inversion H6; subst.
    apply Forall_app.
    + apply new_cfun_sigs_from_expr_in_dts. eauto.
    + eapply IHa_bod; try eassumption.
  - IH_auto_tac.
Qed.



Definition new_cfuns_from_gfuns (p : program) (tn : TypeName) : list (cfun_sig * cfun_bod_named) :=
  let gfuncases : list (ScopedName * expr) := concat (map snd (program_gfun_bods_g p)) in
  let gfunbods : list expr := map snd gfuncases in
  concat (map (generate_cfuns_from_expr tn) gfunbods).

Lemma new_cfun_sigs_from_gfuns_in_dts : forall (p : program) (tn : TypeName),
    cfun_sigs_in_dts (skeleton_dts (program_skeleton p)) (map fst (new_cfuns_from_gfuns p tn)).
Proof.
  intros p tn. unfold cfun_sigs_in_dts. unfold new_cfuns_from_gfuns.
  pose proof (program_gfun_bods_typecheck_g p).
  induction (program_gfun_bods_g p); try apply Forall_nil.
  inversion H; subst; simpl.
  repeat rewrite map_app. rewrite concat_app. rewrite map_app. apply Forall_app.
  - clear - H2. destruct a as [a_qn a_bod]; simpl in *.  destruct H2 as [qn [args [_ H_typecheck]]].
    inversion H_typecheck; subst. clear - H8.
    gen_induction dtorlist a_bod; try apply Forall_nil; simpl. rewrite map_app.
    destruct dtorlist; try solve [inversion H8].
    inversion H8; subst; apply Forall_app.
    + apply new_cfun_sigs_from_expr_in_dts. eauto.
    + IH_auto_tac.
  - IH_auto_tac.
Qed.

Definition new_cfuns (p : program) (tn : TypeName) : list (cfun_sig * cfun_bod_named) :=
       (new_cfuns_from_funs p tn)
    ++ (new_cfuns_from_gfuns p tn)
    ++ (new_cfuns_from_cfuns p tn).


(**************************************************************************************************)
(* ** Construct the skeleton                                                                      *)
(*                                                                                                *)
(**************************************************************************************************)

Definition new_cfun_sigs (p : program) (tn : TypeName) : list cfun_sig :=
  (skeleton_cfun_sigs_l (program_skeleton p))
    ++ (map fst (new_cfuns p tn)).

Lemma new_cfun_sigs_in_dts : forall (p : program) (tn : TypeName),
    cfun_sigs_in_dts (skeleton_dts (program_skeleton p)) (new_cfun_sigs p tn).
Proof.
  intros p tn; unfold new_cfun_sigs;  apply Forall_app.
  - apply (skeleton_cfun_sigs_in_dts_l (program_skeleton p)).
  - unfold new_cfuns. repeat rewrite map_app. repeat apply Forall_app.
    + apply new_cfun_sigs_from_funs_in_dts.
    + apply new_cfun_sigs_from_gfuns_in_dts.
    + apply new_cfun_sigs_from_cfuns_in_dts.
Qed.

Remark generate_cfuns_collect_matches : forall tn a,
  map (fun x => fst (fst (fst x))) (generate_cfuns_from_expr tn a) =
    filter (fun x => eq_TypeName tn (fst x)) (collect_match_names a).
Proof with auto.
intros.
set (g:=(fun x => filter (fun x0 => eq_TypeName tn (fst x0)) (collect_match_names x))).
set (g2:=(fun x : expr * TypeName => filter (fun x0 => eq_TypeName tn (fst x0)) (collect_match_names (fst x)))).
set (g3:=(fun x : ScopedName * expr => filter (fun x0 => eq_TypeName tn (fst x0)) (collect_match_names (snd x)))).
induction a using expr_strong_ind;
 try (simpl; rewrite concat_map; rewrite map_map; rewrite Forall_forall in H;
  rewrite filter_concat; rewrite map_map; rewrite map_ext_in with (g:=g); auto);
 try (simpl; rewrite filter_app; rewrite map_app; f_equal; auto;
  rewrite concat_map; rewrite map_map; rewrite Forall_forall in H;
  rewrite filter_concat; rewrite map_map; rewrite map_ext_in with (g:=g))...
- rewrite Forall_forall in *. case_eq (eq_TypeName tn (fst n)); intros.
  + simpl. rewrite H1. simpl. f_equal. rewrite <- concat_app.
    rewrite map_app; rewrite concat_map.
    rewrite filter_app; rewrite filter_concat.
    repeat (rewrite map_app); repeat (rewrite concat_app); repeat (rewrite map_map).
    f_equal; try f_equal...
    * rewrite map_ext_in with (g:=g2)...
      intros. destruct a0. simpl. apply H0. change e with (fst (e,t)). apply in_map...
    * rewrite map_ext_in with (g:=g3)...
      intros. destruct a0. simpl. apply H. change e with (snd (s,e)). apply in_map...
  + simpl. rewrite H1. simpl. rewrite <- concat_app.
    rewrite map_app; rewrite concat_map.
    rewrite filter_app; rewrite filter_concat.
    repeat (rewrite map_app); repeat (rewrite concat_app); repeat (rewrite map_map).
    f_equal; try f_equal...
    * rewrite map_ext_in with (g:=g2)...
      intros. destruct a0. simpl. apply H0. change e with (fst (e,t)). apply in_map...
    * rewrite map_ext_in with (g:=g3)...
      intros. destruct a0. simpl. apply H. change e with (snd (s,e)). apply in_map...
- simpl. rewrite Forall_forall in *.
  rewrite concat_app; rewrite filter_app; rewrite map_app.
  repeat (rewrite concat_map). repeat (rewrite filter_concat).
  repeat (rewrite map_map). f_equal.
  + rewrite map_ext_in with (g:=g2)...
    intros. destruct a. simpl. apply H0. change e with (fst (e,t)). apply in_map...
  + rewrite map_ext_in with (g:=g3)...
    intros. destruct a. simpl. apply H. change e with (snd (s,e)). apply in_map...
Qed.

Lemma new_cfun_sigs_names_unique : forall (p : program) (tn : TypeName),
    length (skeleton_cfun_sigs_l (program_skeleton p)) = O ->
    cfun_sigs_names_unique (new_cfun_sigs p tn).
Proof with apply generate_cfuns_collect_matches.
intros. unfold new_cfun_sigs. case_eq (skeleton_cfun_sigs_l (program_skeleton p)); intros.
- simpl. unfold new_cfuns. pose proof (program_match_names_unique p).
  apply match_names_unique_global_sublist in H1.
  unfold match_names_unique in H1. unfold cfun_sigs_names_unique.
  unfold new_cfuns_from_funs. unfold new_cfuns_from_gfuns. unfold new_cfuns_from_cfuns.
  do 2 (rewrite map_app in H1).
  do 2 (rewrite concat_app in H1). apply unique_app_switch in H1.
  do 2 (rewrite <- concat_app in H1).
  do 2 (rewrite <- map_app in H1).
  do 2 (rewrite <- concat_app).
  do 2 (rewrite <- map_app).
  rewrite map_map. rewrite concat_map. rewrite map_map.
  apply filter_unique with (f:=(fun x => eq_TypeName tn (fst x))) in H1.
  rewrite filter_concat in H1. rewrite map_map in H1.
  set (g:=fun x => filter (fun x0 => eq_TypeName tn (fst x0)) (collect_match_names x)).
  rewrite map_ext with (g:=g); auto...
- apply (f_equal (length (A:=_))) in H0. rewrite H in H0. simpl in H0. discriminate.
Qed.

Definition lift_match_to_skeleton (p : program) (tn : TypeName)
    (Uniq : cfun_sigs_names_unique (new_cfun_sigs p tn)) : skeleton :=
  let old_skeleton : skeleton := program_skeleton p in
  {|
      (* Datatypes *)
      skeleton_dts := skeleton_dts old_skeleton;
      skeleton_ctors := skeleton_ctors old_skeleton;
      skeleton_dts_ctors_in_dts := skeleton_dts_ctors_in_dts old_skeleton;
      skeleton_dts_ctor_names_unique := skeleton_dts_ctor_names_unique old_skeleton;
      (* Codatatypes *)
      skeleton_cdts := skeleton_cdts old_skeleton;
      skeleton_dtors :=  skeleton_dtors old_skeleton;
      skeleton_cdts_dtors_in_cdts := skeleton_cdts_dtors_in_cdts old_skeleton;
      skeleton_cdts_dtor_names_unique := skeleton_cdts_dtor_names_unique old_skeleton;
      (* Datatypes + Codatatypes *)
      skeleton_dts_cdts_disjoint := skeleton_dts_cdts_disjoint old_skeleton;
      (* Ordinary Functions *)
      skeleton_fun_sigs := skeleton_fun_sigs old_skeleton;
      skeleton_fun_sigs_names_unique := skeleton_fun_sigs_names_unique old_skeleton;
      (* Consumer functions *)
      skeleton_cfun_sigs_g := skeleton_cfun_sigs_g old_skeleton;
      skeleton_cfun_sigs_in_dts_g := skeleton_cfun_sigs_in_dts_g old_skeleton;
      skeleton_cfun_sigs_names_unique_g := skeleton_cfun_sigs_names_unique_g old_skeleton;
      (* Only interesting part: =====> *)
      skeleton_cfun_sigs_l := new_cfun_sigs p tn;
      skeleton_cfun_sigs_in_dts_l := new_cfun_sigs_in_dts p tn;
      skeleton_cfun_sigs_names_unique_l := Uniq;
      (* <===== *)
      (* Generator functions *)
      skeleton_gfun_sigs_g := skeleton_gfun_sigs_g old_skeleton;
      skeleton_gfun_sigs_in_cdts_g := skeleton_gfun_sigs_in_cdts_g old_skeleton;
      skeleton_gfun_sigs_names_unique_g := skeleton_gfun_sigs_names_unique_g old_skeleton;
      skeleton_gfun_sigs_l := skeleton_gfun_sigs_l old_skeleton;
      skeleton_gfun_sigs_in_cdts_l := skeleton_gfun_sigs_in_cdts_l old_skeleton;
      skeleton_gfun_sigs_names_unique_l := skeleton_gfun_sigs_names_unique_l old_skeleton;
    |}.

Lemma subterm_generate_cfun : forall sk ctx tn rtype e ex n bindings_exprs bindings_types ls,
    subterm (E_Match n ex (combine bindings_exprs bindings_types) ls rtype) e ->
    eq_TypeName tn (fst n) = true ->
    sk / ctx |- ex : tn ->
    sk // ctx ||- bindings_exprs :: bindings_types ->
    In (n, bindings_types, rtype) (map fst (generate_cfuns_from_expr tn e)).
Proof.
  intros. set (e' := E_Match n ex (combine bindings_exprs bindings_types) ls rtype) in *.
  rename H1 into Ht_e; rename H2 into H1.
pose proof (eq_refl e'). unfold e' in H2 at 2. generalize dependent e'. intros e' H.
induction H; intros.
- unfold fun_bod. rewrite H2. simpl. rewrite H0. simpl. left.
  pose proof (listTypeDeriv_lemma _ _ _ _ H1). rewrite Nat.eqb_eq in H.
  rewrite map_snd_combine; auto.
- inversion H2; subst.
  + simpl. rewrite concat_map. rewrite map_map. rewrite <- flat_map_concat_map.
    rewrite in_flat_map. exists e2. split; auto.
  + simpl. rewrite map_app. apply in_or_app. left. apply IHsubterm. auto.
  + simpl. rewrite map_app. apply in_or_app. right.
    rewrite concat_map. rewrite map_map. rewrite <- flat_map_concat_map.
    rewrite in_flat_map. exists e2. split; auto.
  + simpl. rewrite concat_map. rewrite map_map. rewrite <- flat_map_concat_map.
    rewrite in_flat_map. exists e2. split; auto.
  + simpl. rewrite concat_map. rewrite map_map. rewrite <- flat_map_concat_map.
    rewrite in_flat_map. exists e2. split; auto.
  + simpl. rewrite map_app. apply in_or_app. left. apply IHsubterm. auto.
  + simpl. rewrite map_app. apply in_or_app. right.
    rewrite concat_map. rewrite map_map. rewrite <- flat_map_concat_map.
    rewrite in_flat_map. exists e2. split; auto.
  + simpl. rewrite map_app. apply in_or_app. right.  rewrite map_app; apply in_or_app.
    left. IH_tac reflexivity.
  + simpl. rewrite map_app. apply in_or_app. right. rewrite map_app. apply in_or_app.
    right. rewrite map_app; apply in_or_app. left.
    rewrite concat_map. rewrite <- flat_map_concat_map. rewrite <- map_map.
    rewrite in_flat_map. exists (generate_cfuns_from_expr tn e2). split; auto.
    rewrite in_map_iff. exists e2. split; auto.
  + simpl. rewrite map_app. apply in_or_app. right. rewrite map_app. apply in_or_app. right.
    rewrite map_app; apply in_or_app; right. rewrite concat_map.
    rewrite <- flat_map_concat_map. rewrite <- map_map.
    rewrite in_flat_map. eexists. split; eauto.
    rewrite in_map_iff. eexists. esplit; eauto.
  + simpl. rewrite map_app. apply in_or_app. left. rewrite concat_map.
    rewrite <- flat_map_concat_map. rewrite <- map_map.
    rewrite in_flat_map. eexists; esplit; eauto.
    rewrite in_map_iff. eexists; esplit; eauto.
  + simpl. rewrite map_app. apply in_or_app. right. rewrite concat_map.
    rewrite <- flat_map_concat_map. rewrite <- map_map.
    rewrite in_flat_map. eexists; esplit; eauto.
    rewrite in_map_iff. eexists; esplit; eauto.
  + simpl. rewrite map_app. apply in_or_app. left. apply IHsubterm. auto.
  + simpl. rewrite map_app. apply in_or_app. right. apply IHsubterm. auto.
Qed.

Lemma lift_match_to_skeleton_preserves_typing : forall (p : program) (ctxt : ctxt) (e : expr) (t tn : TypeName) Uniq,
    ((program_skeleton p) / ctxt |- e : t) ->
    term_in_original_prog e p ->
    (lift_match_to_skeleton p tn Uniq) / ctxt |- (replace_matches_by_cfun_calls tn e) : t.
Proof with try assumption; try reflexivity; try (solve list_type_deriv_induction_tac); try (solve list_type_deriv_induction_2_tac); try (rewrite map_combine_fst); try auto.
  intros p ctxt e t tn Uniq H.  generalize dependent ctxt. generalize dependent t. generalize dependent tn.
  induction e using expr_strong_ind; intros.
  - inversion H; subst. apply T_Var...
  - inversion H0; subst.
    assert (Forall (fun a => term_in_original_prog a p) ls) as Sub. { eapply subterm_term_in_original_prog_Constr; eauto. } rewrite Forall_forall in Sub.
    apply T_Constr with (cargs := cargs)...
  - inversion H0; subst.
    assert (Forall (fun a => term_in_original_prog a p) ls) as Sub. { eapply subterm_term_in_original_prog_DestrCall_es; eauto. } rewrite Forall_forall in Sub.
    assert (term_in_original_prog e p) as Sub'. { eapply subterm_term_in_original_prog_DestrCall_e0; eauto. }
    apply T_DestrCall with (dargs := dargs)...
  - inversion H0; subst.
    assert (Forall (fun a => term_in_original_prog a p) ls) as Sub. { eapply subterm_term_in_original_prog_FunCall; eauto. } rewrite Forall_forall in Sub.
    apply T_FunCall with (argts := argts)...
  - assert (Forall (fun a => term_in_original_prog a p) ls) as Sub. { eapply subterm_term_in_original_prog_ConsFunCall_es; eauto. } rewrite Forall_forall in Sub.
    assert (term_in_original_prog e p) as Sub'. { eapply subterm_term_in_original_prog_ConsFunCall_e0; eauto. }
    inversion H0; subst.
    + apply T_GlobalConsFunCall with (argts := argts)...
    + apply T_LocalConsFunCall with (argts := argts)...
      unfold lift_match_to_skeleton; simpl; unfold new_cfun_sigs.
        apply in_or_app. left...
  - assert (Forall (fun a => term_in_original_prog a p) ls) as Sub. { eapply subterm_term_in_original_prog_GenFunCall; eauto. } rewrite Forall_forall in Sub.
    inversion H0; subst.
    + apply T_GlobalGenFunCall with (argts := argts)...
    + apply T_LocalGenFunCall with (argts := argts)...
  - inversion H1; subst; simpl. case_eq (eq_TypeName tn0 (fst n)); intro eqTn.
    + apply T_LocalConsFunCall with (argts := bindings_types)...
      * simpl; unfold new_cfun_sigs. apply in_or_app. right.
        unfold new_cfuns. repeat (rewrite map_app).
        destruct H2; [|destruct H2]; rewrite Exists_exists in H2; destruct H2 as [x [xIn xSub]].
        -- apply in_or_app. left. unfold new_cfuns_from_funs.
           rewrite concat_map. rewrite map_map. rewrite map_map.
           rewrite <- flat_map_concat_map. rewrite in_flat_map.
           exists x. split; auto. eapply subterm_generate_cfun; eauto.
           apply eq_TypeName_eq in eqTn; rewrite eqTn; assumption.
        -- apply in_or_app. right. apply in_or_app. right. unfold new_cfuns_from_cfuns.
           rewrite concat_map. rewrite map_map. rewrite map_map.
           rewrite <- flat_map_concat_map. rewrite in_flat_map.
           rewrite Exists_exists in xSub. destruct xSub.
           exists x0. destruct H2. split.
           ++ rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x. split; auto.
           ++ eapply subterm_generate_cfun; eauto.
              apply eq_TypeName_eq in eqTn; rewrite eqTn; assumption.
        -- apply in_or_app. right. apply in_or_app. left. unfold new_cfuns_from_gfuns.
           rewrite concat_map. rewrite map_map. rewrite map_map.
           rewrite <- flat_map_concat_map. rewrite in_flat_map.
           rewrite Exists_exists in xSub. destruct xSub.
           exists x0. destruct H2. split.
           ++ rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x. split; auto.
           ++ eapply subterm_generate_cfun; eauto.
              apply eq_TypeName_eq in eqTn; rewrite eqTn; assumption.
      * apply IHe... eapply subterm_term_in_original_prog_Match_e0; eauto.
      * assert (Forall (fun a => term_in_original_prog a p) bindings_exprs) as Sub.
        { eapply subterm_term_in_original_prog_Match_bs; eauto. symmetry. rewrite <- Nat.eqb_eq. eapply listTypeDeriv_lemma; eauto. }
        rewrite Forall_forall in Sub.
        rewrite map_ext with (g:=fst) in H0; auto.
        clear - H13 H0 Sub;
          pose proof (listTypeDeriv_lemma (program_skeleton p) ctxt bindings_exprs bindings_types H13) as H_length;
          rewrite PeanoNat.Nat.eqb_eq in H_length; generalize dependent bindings_types;
            induction bindings_exprs;intros;  destruct bindings_types; try (solve [inversion H_length]);
              try apply ListTypeDeriv_Nil;
              inversion H13; subst; clear H13;
                inversion H0; subst; clear H0.
        apply ListTypeDeriv_Cons; auto using in_eq, in_cons.
    + assert (Forall (fun a => term_in_original_prog a p) bindings_exprs) as Sub.
      { eapply subterm_term_in_original_prog_Match_bs; eauto. symmetry. rewrite <- Nat.eqb_eq. eapply listTypeDeriv_lemma; eauto. }
      rewrite Forall_forall in Sub.
      apply T_Match with (bindings_exprs := map (replace_matches_by_cfun_calls tn0) bindings_exprs) (bindings_types := bindings_types) (ctorlist := ctorlist)...
      * assert (term_in_original_prog e p); [> eapply subterm_term_in_original_prog_Match_e0; eauto |].
        apply IHe...
      * rewrite <- map_combine_fst. apply Forall_map.
        rewrite Forall_forall in *. intros. pose proof (H15 _ H3).
        destruct x. destruct p0. simpl. assumption.
      * assert (Forall (fun a => term_in_original_prog a p) (map snd ls)) as Sub2. { eapply subterm_term_in_original_prog_Match_cases; eauto. } rewrite Forall_forall in Sub2.
        clear -H16 H Sub2.
        gen_induction ctorlist ls; destruct ctorlist; try solve [inversion H16].
        -- simpl. apply ListTypeDeriv'_Nil.
        -- simpl; inversion_clear H16; inversion_clear H.
           apply ListTypeDeriv'_Cons.
           ++ clear IHls. apply H2... destruct a. simpl in Sub2...
           ++ apply IHls...
              intros. apply Sub2... simpl; right...
  - inversion H1; subst. simpl.
    assert (Forall (fun a => term_in_original_prog a p) bindings_exprs) as Sub.
    { eapply subterm_term_in_original_prog_CoMatch_bs; eauto. symmetry. rewrite <- Nat.eqb_eq. eapply listTypeDeriv_lemma; eauto. }
    rewrite Forall_forall in Sub.
    apply T_CoMatch with (bindings_exprs := map (replace_matches_by_cfun_calls tn) bindings_exprs) (bindings_types := bindings_types) (dtorlist := dtorlist)...
    + rewrite <- map_combine_fst. apply Forall_map.
      rewrite Forall_forall in *. intros. pose proof (H12 _ H3).
      destruct x. destruct p0. simpl. assumption.
    + assert (Forall (fun a => term_in_original_prog a p) (map snd ls)) as Sub2. { eapply subterm_term_in_original_prog_CoMatch_cocases; eauto. } rewrite Forall_forall in Sub2.
      clear -H13 H Sub2.
      gen_induction dtorlist ls; destruct dtorlist; try solve [inversion H13].
      * apply ListTypeDeriv'_Nil.
      * simpl. inversion_clear H13; inversion_clear H.
        apply ListTypeDeriv'_Cons...
        -- apply H2... destruct a. apply Sub2. left...
        -- apply IHls... intros. apply Sub2. right...
  - inversion H; subst.
    assert (term_in_original_prog e1 p) as Sub1. { eapply subterm_term_in_original_prog_Let_e1; eauto. }
    assert (term_in_original_prog e2 p) as Sub2. { eapply subterm_term_in_original_prog_Let_e2; eauto. }
    apply T_Let with (t1 := t1)...
Qed.

Corollary new_funbods_typecheck : forall p tn Uniq,
  fun_bods_typecheck (program_skeleton p) (program_fun_bods p) ->
  fun_bods_typecheck (lift_match_to_skeleton p tn Uniq)
    (map (fun x : Name * expr => (fst x, replace_matches_by_cfun_calls tn (snd x))) (program_fun_bods p)).
Proof.
intros. unfold fun_bods_typecheck in *. rewrite Forall_forall in *. intros.
rewrite in_map_iff in H0. destruct H0. destruct H0.
pose proof (H x0 H1). destruct H2. destruct H2. destruct H2. exists x1. exists x2. exists x3.
destruct H2. split.
- unfold UtilsSkeleton.lookup_fun_sig in *. simpl.
  inversion H0; subst. simpl. assumption.
- inversion H0; subst. apply lift_match_to_skeleton_preserves_typing; auto.
  unfold term_in_original_prog. left. rewrite Exists_exists. exists x0. split; auto. apply Sub_Refl.
Qed.

Require Import Coq.omega.Omega.

Corollary new_cfunbods_g_typecheck : forall p tn Uniq,
  cfun_bods_g_typecheck (program_skeleton p) (program_cfun_bods_g p) ->
  cfun_bods_g_typecheck (lift_match_to_skeleton p tn Uniq)
    (map (fun x : QName * list (ScopedName * expr) =>
      (fst x, map (fun y : ScopedName * expr => (fst y, replace_matches_by_cfun_calls tn (snd y)))
                  (snd x)))
      (program_cfun_bods_g p)).
Proof.
intros. unfold cfun_bods_g_typecheck in *. rewrite Forall_forall in *. intros.
rewrite in_map_iff in H0. destruct H0. destruct H0.
pose proof (H x0 H1). destruct H2. destruct H2. destruct H2. exists x1. exists x2. exists x3.
destruct H2. split.
- unfold UtilsSkeleton.lookup_cfun_sig_g in *. simpl.
  inversion H0; subst. simpl. assumption.
- inversion H0; subst. simpl. inversion H3; subst.
  eapply T_Match; eauto.
  + apply T_Var. inversion H9; subst. assumption.
  + clear - H12 H14. generalize dependent bindings_types.
    replace (index_list 1 x2) with (index_list (S 0) (skipn 0 x2)); auto. generalize 0.
    generalize dependent bindings_exprs.
    induction bindings_exprs; intros.
    * inversion H12; subst. inversion H14; subst; try apply ListTypeDeriv_Nil.
    * inversion H14; subst. simpl in H12.
      apply ListTypeDeriv_Cons.
      -- clear - H12 H3. generalize dependent (skipn n x2).
         intros. destruct l; try discriminate. inversion H12; subst.
         inversion H3; subst. apply T_Var. assumption.
      -- apply IHbindings_exprs with (n:=S n); auto.
         case_eq (skipn n x2); intros; rewrite H in H12; try discriminate.
         simpl in H12. inversion H12; subst. f_equal. clear - H.
         generalize dependent t. generalize dependent l. generalize dependent x2.
         induction n; intros; try (simpl in H; rewrite H; auto).
         destruct x2; try (simpl in H; discriminate).
         simpl in H. replace (skipn (S (S n)) (t0 :: x2)) with (skipn (S n) x2); auto.
         eapply IHn. eassumption.
  + rewrite Forall_forall in *. intros. destruct x. destruct p0. destruct p1.
    assert (exists x, In (s, x, (s0, l)) (combine (snd x0) ctorlist)).
    { rewrite <- map_fst_f_combine in H0. rewrite in_map_iff in H0.
      destruct H0. destruct H0. destruct x. inversion H0; subst. exists (snd p0).
      destruct p0. simpl. auto.
    }
    destruct H5. pose proof (H16 _ H5). simpl in H6. auto.
  + rewrite map_length. rewrite map_map. simpl. clear - H1 H17. destruct x0. simpl in *.
    generalize dependent (map (fun ctor : ScopedName * list TypeName => snd ctor ++ bindings_types) ctorlist).
    generalize dependent (repeat x3 (length l)).
    clear - H1.
    assert (exists xs, l = xs ++ l); try (exists []; auto).
    generalize H. generalize l at - 1.
    induction l0; intros; inversion H17; subst; try apply ListTypeDeriv'_Nil.
    apply ListTypeDeriv'_Cons.
    * apply lift_match_to_skeleton_preserves_typing; auto.
      unfold term_in_original_prog. right. left. rewrite Exists_exists. exists (q, l). split; auto.
      rewrite Exists_exists. simpl. exists a.
      assert (In a l). { clear -H0. destruct H0. rewrite H. apply in_or_app. right. simpl. left. auto. }
      split; auto. apply Sub_Refl.
    * apply IHl0; auto. destruct H0. exists (x ++ [a]). rewrite <- app_assoc. simpl. auto.
Qed.

Corollary new_gfunbods_g_typecheck : forall p tn Uniq,
  gfun_bods_g_typecheck (program_skeleton p) (program_gfun_bods_g p) ->
  gfun_bods_g_typecheck (lift_match_to_skeleton p tn Uniq)
    (map (fun x : QName * list (ScopedName * expr) =>
      (fst x, map (fun y : ScopedName * expr => (fst y, replace_matches_by_cfun_calls tn (snd y)))
                  (snd x)))
      (program_gfun_bods_g p)).
Proof.
intros. unfold gfun_bods_g_typecheck in *. rewrite Forall_forall in *. intros.
rewrite in_map_iff in H0. destruct H0. destruct H0.
pose proof (H x0 H1). destruct H2. destruct H2. exists x1. exists x2.
destruct H2. split.
- unfold UtilsSkeleton.lookup_gfun_sig_g in *. simpl.
  inversion H0; subst. simpl. assumption.
- inversion H0; subst. simpl. inversion H3; subst.
  eapply T_CoMatch; eauto.
  + clear - H7 H8. generalize dependent bindings_types.
    replace (index_list 0 x2) with (index_list 0 (skipn 0 x2)); auto. generalize 0.
    generalize dependent bindings_exprs.
    induction bindings_exprs; intros.
    * inversion H7; subst. inversion H8; subst; try apply ListTypeDeriv_Nil.
    * inversion H8; subst. simpl in H7.
      apply ListTypeDeriv_Cons.
      -- clear - H7 H3. generalize dependent (skipn n x2).
         intros. destruct l; try discriminate. inversion H7; subst.
         inversion H3; subst. apply T_Var. assumption.
      -- apply IHbindings_exprs with (n:=S n); auto.
         case_eq (skipn n x2); intros; rewrite H in H7; try discriminate.
         simpl in H7. inversion H7; subst. f_equal. clear - H.
         generalize dependent t. generalize dependent l. generalize dependent x2.
         induction n; intros; try (simpl in H; rewrite H; auto).
         destruct x2; try (simpl in H; discriminate).
         simpl in H. replace (skipn (S (S n)) (t0 :: x2)) with (skipn (S n) x2); auto.
         eapply IHn. eassumption.
  + rewrite Forall_forall in *. intros. destruct x. destruct p0. destruct p1. destruct p0.
    assert (exists x, In (s, x, (s0, l, t)) (combine (snd x0) dtorlist)).
    { rewrite <- map_fst_f_combine in H0. rewrite in_map_iff in H0.
      destruct H0. destruct H0. destruct x. inversion H0; subst. exists (snd p0).
      destruct p0. simpl. auto.
    }
    destruct H5. pose proof (H12 _ H5). simpl in H6. auto.
  + rewrite map_map. simpl. clear - H1 H13. destruct x0. simpl in *.
    generalize dependent (map (fun dtor : ScopedName * list TypeName * TypeName => snd (fst dtor) ++ bindings_types) dtorlist).
    generalize dependent (map snd dtorlist).
    clear - H1.
    assert (exists xs, l = xs ++ l); try (exists []; auto).
    generalize H. generalize l at - 1.
    induction l0; intros; inversion H13; subst; try apply ListTypeDeriv'_Nil.
    apply ListTypeDeriv'_Cons.
    * apply lift_match_to_skeleton_preserves_typing; auto.
      unfold term_in_original_prog. right. right. rewrite Exists_exists. exists (q, l). split; auto.
      rewrite Exists_exists. simpl. exists a.
      assert (In a l). { clear -H0. destruct H0. rewrite H. apply in_or_app. right. simpl. left. auto. }
      split; auto. apply Sub_Refl.
    * apply IHl0; auto. destruct H0. exists (x ++ [a]). rewrite <- app_assoc. simpl. auto.
Qed.

(**************************************************************************************************)
(* ** Construct the program                                                                       *)
(*                                                                                                *)
(**************************************************************************************************)

Fact new_has_all_funbods : forall p tn Uniq,
  has_all_fun_bods (skeleton_fun_sigs (program_skeleton p)) (program_fun_bods p) ->
  has_all_fun_bods (skeleton_fun_sigs (lift_match_to_skeleton p tn Uniq))
    (map (fun x : Name * expr => (fst x, replace_matches_by_cfun_calls tn (snd x)))
       (program_fun_bods p)).
Proof.
intros. simpl. unfold has_all_fun_bods in *. rewrite map_map. simpl. auto.
Qed.

Fact new_has_all_gfunbods_g : forall p tn Uniq,
  has_all_gfun_bods (skeleton_gfun_sigs_g (program_skeleton p)) (program_gfun_bods_g p) ->
  has_all_gfun_bods (skeleton_gfun_sigs_g (lift_match_to_skeleton p tn Uniq))
    (map (fun x : QName * list (ScopedName * expr) =>
      (fst x, map (fun y : ScopedName * expr => (fst y, replace_matches_by_cfun_calls tn (snd y)))
                  (snd x)))
      (program_gfun_bods_g p)).
Proof.
intros. simpl. unfold has_all_gfun_bods in *. rewrite map_map. simpl. auto.
Qed.

Fact new_has_all_gfunbods_l : forall p tn Uniq,
 length (skeleton_gfun_sigs_l (lift_match_to_skeleton p tn Uniq)) = 0 ->
 has_all_gfun_bods (skeleton_gfun_sigs_l (lift_match_to_skeleton p tn Uniq)) [].
Proof.
intros. unfold has_all_gfun_bods.
case_eq (skeleton_gfun_sigs_l (lift_match_to_skeleton p tn Uniq)); intros; auto.
rewrite H0 in H. simpl in H. discriminate.
Qed.

Fact new_has_all_cfunbods_g : forall p tn Uniq,
  has_all_cfun_bods (skeleton_cfun_sigs_g (program_skeleton p)) (program_cfun_bods_g p) ->
  has_all_cfun_bods (skeleton_cfun_sigs_g (lift_match_to_skeleton p tn Uniq))
    (map (fun x : QName * list (ScopedName * expr) =>
      (fst x, map (fun y : ScopedName * expr => (fst y, replace_matches_by_cfun_calls tn (snd y)))
                  (snd x)))
      (program_cfun_bods_g p)).
Proof.
intros. simpl. unfold has_all_cfun_bods in *. rewrite map_map. simpl. auto.
Qed.

Definition new_cfun_bods_l (p : program) (tn : TypeName) : gfun_bods :=
  map snd (flat_map (generate_cfuns_from_expr tn) (map snd (program_fun_bods p)))
  ++ map snd (flat_map (generate_cfuns_from_expr tn) (map snd (flat_map snd (program_gfun_bods_g p))))
  ++ map snd (flat_map (generate_cfuns_from_expr tn) (map snd (flat_map snd (program_cfun_bods_g p)))).

Fact new_has_all_cfunbods_l : forall p tn Uniq,
  length (skeleton_cfun_sigs_l (program_skeleton p)) = O ->
  has_all_cfun_bods (skeleton_cfun_sigs_l (lift_match_to_skeleton p tn Uniq)) (new_cfun_bods_l p tn).
Proof.
intros. simpl. unfold has_all_cfun_bods. unfold new_cfun_sigs.
assert (skeleton_cfun_sigs_l (program_skeleton p) = []).
{ destruct (skeleton_cfun_sigs_l (program_skeleton p)); auto. simpl in H. discriminate. }
rewrite H0. clear H H0. simpl. unfold new_cfuns. unfold new_cfun_bods_l.
repeat (rewrite map_app). repeat f_equal.
- unfold new_cfuns_from_funs. rewrite <- flat_map_concat_map.
  generalize (map snd (program_fun_bods p)). induction l; auto.
  simpl. repeat (rewrite map_app). rewrite IHl. f_equal. clear.
  unfold fun_bod in a. pose proof (generate_cfuns_from_expr_names_match tn a).
  induction H; auto. simpl. f_equal; auto.
- unfold new_cfuns_from_gfuns. repeat (rewrite <- flat_map_concat_map).
  unfold gfun_bod. generalize (map snd (flat_map snd (program_gfun_bods_g p))). induction l; auto.
  simpl. repeat (rewrite map_app). rewrite IHl. f_equal. clear.
  pose proof (generate_cfuns_from_expr_names_match tn a).
  induction H; auto. simpl. f_equal; auto.
- unfold new_cfuns_from_cfuns. repeat (rewrite <- flat_map_concat_map).
  unfold cfun_bod. generalize (map snd (flat_map snd (program_cfun_bods_g p))). induction l; auto.
  simpl. repeat (rewrite map_app). rewrite IHl. f_equal. clear.
  pose proof (generate_cfuns_from_expr_names_match tn a).
  induction H; auto. simpl. f_equal; auto.
Qed.

Lemma term_in_original_prog_name_eq : forall p tn (x0 : cfun_sig * cfun_bod_named) (x : expr) s e s0 (l : list TypeName),
  In x0 (generate_cfuns_from_expr tn x) ->
  In (s, e, (s0, l))
      (combine (snd (snd x0))
         (filter
            (fun x : ScopedName * list TypeName =>
             let (n, _) := x in eq_TypeName (fst (unscope n)) (fst (fst (snd x0))))
            (skeleton_ctors (program_skeleton p)))) ->
  term_in_original_prog x p ->
  s = s0.
Proof.
intros p tn x0 x s e s0 l xIn H H0.
induction x using expr_strong_ind; simpl in *; try (exfalso; assumption);
try (
 destruct ls; try (simpl in xIn; exfalso; assumption);
 rewrite Forall_forall in H1; rewrite <- flat_map_concat_map in xIn;
 rewrite in_flat_map in xIn; destruct xIn as [x' [x'In x'H]];
 apply H1 with (x:=x'); auto;
 try (
  pose proof (subterm_term_in_original_prog_Constr _ _ _ H0) as Sub;
  rewrite Forall_forall in Sub; apply Sub; auto );
 try (
  pose proof (subterm_term_in_original_prog_FunCall _ _ _ H0) as Sub;
  rewrite Forall_forall in Sub; apply Sub; auto );
 try (
  pose proof (subterm_term_in_original_prog_GenFunCall _ _ _ H0) as Sub;
  rewrite Forall_forall in Sub; apply Sub; auto ) ).
- apply in_app_or in xIn. destruct xIn.
  + pose proof (subterm_term_in_original_prog_DestrCall_e0 _ _ _ _ H0).
    apply IHx; auto.
  + destruct ls; try (simpl in H2; exfalso; assumption).
    rewrite Forall_forall in H1. rewrite <- flat_map_concat_map in H2.
    rewrite in_flat_map in H2. destruct H2 as [x' [x'In x'H]].
    apply H1 with (x:=x'); auto.
    pose proof (subterm_term_in_original_prog_DestrCall_es _ _ _ _ H0).
    rewrite Forall_forall in H2. apply H2. auto.
- apply in_app_or in xIn. destruct xIn.
  + pose proof (subterm_term_in_original_prog_ConsFunCall_e0 _ _ _ _ H0).
    apply IHx; auto.
  + destruct ls; try (simpl in H2; exfalso; assumption).
    rewrite Forall_forall in H1. rewrite <- flat_map_concat_map in H2.
    rewrite in_flat_map in H2. destruct H2 as [x' [x'In x'H]].
    apply H1 with (x:=x'); auto.
    pose proof (subterm_term_in_original_prog_ConsFunCall_es _ _ _ _ H0).
    rewrite Forall_forall in H2. apply H2. auto.
- assert (exists es1 es2, length es1 = length es2 /\ es = combine es1 es2) as CombineEq.
  { clear. exists (fst (split es)). exists (snd (split es)). split.
    - rewrite split_length_l. rewrite split_length_r. auto.
    - symmetry. pose proof (split_combine es). destruct (split es). auto.
  }
  destruct CombineEq as [es1 [es2 [Len Eq]]]. subst.
  name_destruct_tac.
  + apply in_app_or in xIn.
    destruct xIn; [> | apply in_app_or in H3; destruct H3; [> | apply in_app_or in H3; destruct H3] ].
    * simpl in H3. destruct H3; [> | exfalso; auto]. rewrite <- H3 in H; clear - H H0.
      simpl in H. apply term_in_original_prog_typechecks in H0. do 2 (destruct H0).
      inversion_clear H0. unfold lookup_ctors in H4.
      match_destruct_tac; inversion H4; subst; clear H4.
      rewrite Forall_forall in H5.
      rewrite <- map_fst_f_combine in H. rewrite in_map_iff in H. do 2 (destruct H).
      pose proof (H5 _ H0). destruct x2. destruct p0. destruct p1.
      inversion H; subst; auto.
    * pose proof (subterm_term_in_original_prog_Match_e0 _ _ _ _ _ _ _ H0).
      apply IHx; try assumption.
    * pose proof (subterm_term_in_original_prog_Match_bs _ _ _ _ _ _ _ Len H0).
      rewrite Forall_forall in H2.
      rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
      destruct H3. destruct H3. apply H2 with (x:=fst x1); auto.
      -- rewrite in_map_iff. eexists. split; eauto. destruct x1. auto.
      -- rewrite Forall_forall in H4. apply H4. rewrite <- map_fst_combine with (l2:=es2); auto.
         rewrite in_map_iff. exists x1. split; auto.
    *  pose proof (subterm_term_in_original_prog_Match_cases _ _ _ _ _ _ _ H0).
       rewrite Forall_forall in H1.
       rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
       destruct H3. destruct H3. apply H1 with (x:=snd x1); auto.
       -- rewrite in_map_iff. eexists. split; eauto. destruct x1. auto.
       -- rewrite Forall_forall in H4. apply H4. apply in_map. auto.
  + apply in_app_or in xIn.
    destruct xIn; [> | apply in_app_or in H3; destruct H3; [> | apply in_app_or in H3; destruct H3]].
    * inversion H3.
    * pose proof (subterm_term_in_original_prog_Match_e0 _ _ _ _ _ _ _ H0).
      apply IHx; try assumption.
    * pose proof (subterm_term_in_original_prog_Match_bs _ _ _ _ _ _ _ Len H0).
      rewrite Forall_forall in H2.
      rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3. do 2 (destruct H3).
      apply H2 with (x := fst x1); auto.
      -- rewrite in_map_iff. eexists; split; eauto. destruct x1; auto.
      -- rewrite Forall_forall in H4. apply H4. apply in_map with (f := fst) in H3.
         rewrite map_fst_combine in H3; assumption.
    * pose proof (subterm_term_in_original_prog_Match_cases _ _ _ _ _ _ _ H0).
      rewrite Forall_forall in H1.
      rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3. do 2 (destruct H3).
      apply H1 with (x := snd x1); auto.
      -- rewrite in_map_iff. eexists; split; eauto. destruct x1; auto.
      -- rewrite Forall_forall in H4; apply H4. apply in_map; auto.

- assert (exists es1 es2, length es1 = length es2 /\ es = combine es1 es2) as CombineEq.
  { clear. exists (fst (split es)). exists (snd (split es)). split.
    - rewrite split_length_l. rewrite split_length_r. auto.
    - symmetry. pose proof (split_combine es). destruct (split es). auto.
  }
  destruct CombineEq as [es1 [es2 [Len Eq]]]. subst.
  apply in_app_or in xIn. destruct xIn.
  + pose proof (subterm_term_in_original_prog_CoMatch_bs _ _ _ _ _ Len H0).
    rewrite Forall_forall in H2.
    rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
    destruct H3. destruct H3. apply H2 with (x:=fst x); auto.
    * rewrite in_map_iff. eexists. split; eauto. destruct x. auto.
    * rewrite Forall_forall in H4. apply H4. rewrite <- map_fst_combine with (l2:=es2); auto.
      rewrite in_map_iff. exists x. split; auto.
  + pose proof (subterm_term_in_original_prog_CoMatch_cocases _ _ _ _ _ H0).
    rewrite Forall_forall in H1.
    rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
    destruct H3. destruct H3. apply H1 with (x:=snd x); auto.
    * rewrite in_map_iff. eexists. split; eauto. destruct x. auto.
    * rewrite Forall_forall in H4. apply H4. apply in_map. auto.
- apply in_app_or in xIn. destruct xIn.
  + apply IHx1; auto. eapply subterm_term_in_original_prog_Let_e1. eauto.
  + apply IHx2; auto. eapply subterm_term_in_original_prog_Let_e2. eauto.
Qed.

Corollary term_in_fun_bod_name_eq : forall p tn (x0 : cfun_sig * cfun_bod_named) (x : expr) s e s0 (l : list TypeName),
  In x0 (generate_cfuns_from_expr tn x) ->
  In (s, e, (s0, l))
      (combine (snd (snd x0))
         (filter
            (fun x : ScopedName * list TypeName =>
             let (n, _) := x in eq_TypeName (fst (unscope n)) (fst (fst (snd x0))))
            (skeleton_ctors (program_skeleton p)))) ->
  (exists x' : expr, subterm x x' /\ In x' (map snd (program_fun_bods p))) ->
  s = s0.
Proof.
intros p tn x0 x s e s0 l xIn H H0.
assert (term_in_original_prog x p).
{ unfold term_in_original_prog. left. rewrite Exists_exists.
  destruct H0. destruct H0. rewrite in_map_iff in H1. destruct H1. destruct H1. subst.
  exists x2. split; auto.
}
eapply term_in_original_prog_name_eq; eauto.
Qed.

Corollary term_in_cfun_bod_name_eq : forall p  tn (x0 : cfun_sig * cfun_bod_named) (x : expr) s e s0 (l : list TypeName),
  In x0 (generate_cfuns_from_expr tn x) ->
  In (s, e, (s0, l))
      (combine (snd (snd x0))
         (filter
            (fun x : ScopedName * list TypeName =>
             let (n, _) := x in eq_TypeName (fst (unscope n)) (fst (fst (snd x0))))
            (skeleton_ctors (program_skeleton p)))) ->
  (exists x' : expr, subterm x x' /\ In x' (map snd (flat_map snd (program_cfun_bods_g p)))) ->
  s = s0.
Proof.
intros p tn x0 x s e s0 l xIn H H0.
assert (term_in_original_prog x p).
{ unfold term_in_original_prog. right. left. rewrite Exists_exists.
  destruct H0. destruct H0. rewrite in_map_iff in H1. destruct H1. destruct H1. subst.
  rewrite in_flat_map in H2. destruct H2. destruct H1.
  exists x1. split; auto. rewrite Exists_exists. exists x2. split; auto.
}
eapply term_in_original_prog_name_eq; eauto.
Qed.

Corollary term_in_gfun_bod_name_eq : forall p  tn (x0 : cfun_sig * cfun_bod_named) (x : expr) s e s0 (l : list TypeName),
  In x0 (generate_cfuns_from_expr tn x) ->
  In (s, e, (s0, l))
      (combine (snd (snd x0))
         (filter
            (fun x : ScopedName * list TypeName =>
             let (n, _) := x in eq_TypeName (fst (unscope n)) (fst (fst (snd x0))))
            (skeleton_ctors (program_skeleton p)))) ->
  (exists x' : expr, subterm x x' /\ In x' (map snd (flat_map snd (program_gfun_bods_g p)))) ->
  s = s0.
Proof.
intros p tn x0 x s e s0 l xIn H H0.
assert (term_in_original_prog x p).
{ unfold term_in_original_prog. right. right. rewrite Exists_exists.
  destruct H0. destruct H0. rewrite in_map_iff in H1. destruct H1. destruct H1. subst.
  rewrite in_flat_map in H2. destruct H2. destruct H1.
  exists x1. split; auto. rewrite Exists_exists. exists x2. split; auto.
}
eapply term_in_original_prog_name_eq; eauto.
Qed.

Lemma generates_from_match : forall p tn (x0 : cfun_sig * cfun_bod_named) (e : expr) info,
  term_in_original_prog e p ->
  In x0 (generate_cfuns_from_expr tn e) ->
  (In info
       (flat_map (generate_cfuns_from_expr tn)
          (map snd (program_fun_bods p)) ++
        flat_map (generate_cfuns_from_expr tn)
          (map snd (flat_map snd (program_gfun_bods_g p))) ++
        flat_map (generate_cfuns_from_expr tn)
          (map snd (flat_map snd (program_cfun_bods_g p)))) /\
    fst info = fst x0) ->
  exists (x' : list expr) (sn : Name) (bs_es : list expr) (e' : expr),
    length bs_es = length (snd (fst (fst info))) /\
    map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd x0)) /\
    term_in_original_prog
      (E_Match (fst (fst (snd x0)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd x0))) x') (snd (fst info))) p.
Proof.
intros. induction e using expr_strong_ind; simpl in H0.
- exfalso. auto.
- rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
  rewrite Forall_forall in H2. apply H2 with (x:=x); auto.
  pose proof (subterm_term_in_original_prog_Constr _ _ _ H). rewrite Forall_forall in H4. apply H4. auto.
- apply in_app_or in H0. destruct H0.
  + apply IHe; auto. eapply subterm_term_in_original_prog_DestrCall_e0; eauto.
  + rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
    rewrite Forall_forall in H2. apply H2 with (x:=x); auto.
    pose proof (subterm_term_in_original_prog_DestrCall_es _ _ _ _ H). rewrite Forall_forall in H4. apply H4. auto.
- rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
  rewrite Forall_forall in H2. apply H2 with (x:=x); auto.
  pose proof (subterm_term_in_original_prog_FunCall _ _ _ H). rewrite Forall_forall in H4. apply H4. auto.
- apply in_app_or in H0. destruct H0.
  + apply IHe; auto. eapply subterm_term_in_original_prog_ConsFunCall_e0; eauto.
  + rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
    rewrite Forall_forall in H2. apply H2 with (x:=x); auto.
    pose proof (subterm_term_in_original_prog_ConsFunCall_es _ _ _ _ H). rewrite Forall_forall in H4. apply H4. auto.
- rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
  rewrite Forall_forall in H2. apply H2 with (x:=x); auto.
  pose proof (subterm_term_in_original_prog_GenFunCall _ _ _ H). rewrite Forall_forall in H4. apply H4. auto.
- assert (exists es1 es2, length es1 = length es2 /\ es = combine es1 es2) as CombineEq.
  { clear. exists (fst (split es)). exists (snd (split es)). split.
    - rewrite split_length_l. rewrite split_length_r. auto.
    - symmetry. pose proof (split_combine es). destruct (split es). auto.
  }
  destruct CombineEq as [es1 [es2 [Len Eq]]]. subst.
  name_destruct_tac.
  + repeat (apply in_app_or in H0; destruct H0).
    * inversion H0; [> | exfalso; auto]. rewrite <- H4. simpl. destruct n. clear H2 H3 IHe.
      do 4 eexists. repeat split.
      -- instantiate (1 := es1). inversion H1. rewrite H3. rewrite <- H4; simpl. rewrite map_snd_combine; assumption.
      -- rewrite map_map with (g := snd). simpl. rewrite map_map. eauto.
      -- rewrite map_map. simpl. rewrite <- combine_fst_snd.
         inversion H1. rewrite H3. rewrite <- H4. simpl. rewrite map_snd_combine; try assumption.
         simpl. eassumption.
    * clear H2 H3. pose proof (subterm_term_in_original_prog_Match_e0 _ _ _ _ _ _ _ H).
      IH_auto_tac.
    * rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. do 2 (destruct H0).
      rewrite Forall_forall in H3. clear H2 IHe. apply H3 with (x := fst x); auto.
      -- apply in_map; assumption.
      -- pose proof (subterm_term_in_original_prog_Match_bs _ _ _ _ _ _ _ Len H).
         rewrite Forall_forall in H2. apply H2. destruct x. apply in_map with (f := fst) in H0.
         rewrite map_fst_combine in H0; assumption.
    * clear H3 IHe.
      rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. do 2 (destruct H0).
      rewrite Forall_forall in H2. apply H2 with (x := snd x); auto.
      -- apply in_map with (f := snd) in H0. assumption.
      -- pose proof (subterm_term_in_original_prog_Match_cases _ _ _ _ _ _ _ H).
         rewrite Forall_forall in H4; apply H4.
         apply in_map with (f := snd) in H0; assumption.
  + simpl in H0. repeat (apply in_app_or in H0; destruct H0).
    * pose proof (subterm_term_in_original_prog_Match_e0 _ _ _ _ _ _ _ H).
      IH_auto_tac.
    * rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
      rewrite Forall_forall in H3. apply H3 with (x:=fst x); auto.
      -- apply in_map. auto.
      -- pose proof (subterm_term_in_original_prog_Match_bs _ _ _ _ _ _ _ Len H).
         rewrite Forall_forall in H5. apply H5. destruct x. simpl. eapply in_combine_l. eauto.
    *  rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
       rewrite Forall_forall in H2. apply H2 with (x:=snd x); auto.
       -- apply in_map. auto.
       -- pose proof (subterm_term_in_original_prog_Match_cases _ _ _ _ _ _ _ H).
          rewrite Forall_forall in H5. apply H5. apply in_map. auto.


- assert (exists es1 es2, length es1 = length es2 /\ es = combine es1 es2) as CombineEq.
  { clear. exists (fst (split es)). exists (snd (split es)). split.
    - rewrite split_length_l. rewrite split_length_r. auto.
    - symmetry. pose proof (split_combine es). destruct (split es). auto.
  }
  destruct CombineEq as [es1 [es2 [Len Eq]]].
  apply in_app_or in H0. destruct H0.
  + rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
    rewrite Forall_forall in H3. apply H3 with (x:=fst x); auto.
    * apply in_map. auto.
    * subst. pose proof (subterm_term_in_original_prog_CoMatch_bs _ _ _ _ _ Len H).
      rewrite Forall_forall in H5. apply H5. destruct x. simpl. eapply in_combine_l. eauto.
  + rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
    rewrite Forall_forall in H2. apply H2 with (x:=snd x); auto.
    *  apply in_map. auto.
    * subst. pose proof (subterm_term_in_original_prog_CoMatch_cocases _ _ _ _ _ H).
      rewrite Forall_forall in H5. apply H5. destruct x. apply in_map. auto.
- apply in_app_or in H0. destruct H0.
  + apply IHe1; auto. eapply subterm_term_in_original_prog_Let_e1; eauto.
  + apply IHe2; auto. eapply subterm_term_in_original_prog_Let_e2; eauto.
Qed.

Lemma fun_generates_from_match :
forall p tn (x0 : cfun_sig * cfun_bod_named) (x1 : Name * fun_bod) info,
  In x1 (program_fun_bods p) ->
  In x0 (generate_cfuns_from_expr tn (snd x1)) ->
  In info
           (flat_map (generate_cfuns_from_expr tn)
              (map snd (program_fun_bods p)) ++
            flat_map (generate_cfuns_from_expr tn)
              (map snd (flat_map snd (program_gfun_bods_g p))) ++
            flat_map (generate_cfuns_from_expr tn)
              (map snd (flat_map snd (program_cfun_bods_g p)))) ->
  fst info = fst x0 ->
  exists (x' : list expr) (sn : Name) (bs_es : list expr) (e': expr),
    length bs_es = length (snd (fst (fst info))) /\
    map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd x0)) /\
    term_in_original_prog
      (E_Match (fst (fst (snd x0)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd x0))) x') (snd (fst info))) p.
Proof.
intros. destruct x1. simpl in *. apply generates_from_match with (e:=f); auto.
unfold term_in_original_prog. left. rewrite Exists_exists. exists (n,f). split; auto.
apply Sub_Refl.
Qed.

Lemma gfun_generates_from_match :
forall p tn (x0 : cfun_sig * cfun_bod_named) (x1 : ScopedName * expr) info,
  In x1 (flat_map snd (program_gfun_bods_g p)) ->
  In x0 (generate_cfuns_from_expr tn (snd x1)) ->
  In info
           (flat_map (generate_cfuns_from_expr tn)
              (map snd (program_fun_bods p)) ++
            flat_map (generate_cfuns_from_expr tn)
              (map snd (flat_map snd (program_gfun_bods_g p))) ++
            flat_map (generate_cfuns_from_expr tn)
              (map snd (flat_map snd (program_cfun_bods_g p)))) ->
  fst info = fst x0 ->
  exists (x' : list expr) (sn : Name) (bs_es : list expr) (e': expr),
    length bs_es = length (snd (fst (fst info))) /\
    map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd x0)) /\
    term_in_original_prog
      (E_Match (fst (fst (snd x0)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd x0))) x') (snd (fst info))) p.

Proof.
intros. rewrite in_flat_map in H. destruct H. destruct H. apply generates_from_match with (e:=snd x1); auto.
unfold term_in_original_prog. right. right. rewrite Exists_exists. exists x. split; auto.
rewrite Exists_exists. exists x1. split; auto. apply Sub_Refl.
Qed.

Lemma cfun_generates_from_match :
forall p tn (x0 : cfun_sig * cfun_bod_named) (x1 : ScopedName * expr) info,
  In x1 (flat_map snd (program_cfun_bods_g p)) ->
  In x0 (generate_cfuns_from_expr tn (snd x1)) ->
  In info
           (flat_map (generate_cfuns_from_expr tn)
              (map snd (program_fun_bods p)) ++
            flat_map (generate_cfuns_from_expr tn)
              (map snd (flat_map snd (program_gfun_bods_g p))) ++
            flat_map (generate_cfuns_from_expr tn)
              (map snd (flat_map snd (program_cfun_bods_g p)))) ->
  fst info = fst x0 ->
  exists (x' : list expr) (sn : Name) (bs_es : list expr) (e' : expr),
    length bs_es = length (snd (fst (fst info))) /\
    map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd x0)) /\
    term_in_original_prog
      (E_Match (fst (fst (snd x0)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd x0))) x') (snd (fst info))) p.
Proof.
intros. rewrite in_flat_map in H. destruct H. destruct H. apply generates_from_match with (e:=snd x1); auto.
unfold term_in_original_prog. right. left. rewrite Exists_exists. exists x. split; auto.
rewrite Exists_exists. exists x1. split; auto. apply Sub_Refl.
Qed.

Fact info_in_fun_bods : forall p tn x0 info,
  In x0 (program_fun_bods p) ->
  In info (generate_cfuns_from_expr tn (snd x0)) ->
  In info
    (flat_map (generate_cfuns_from_expr tn) (map snd (program_fun_bods p)) ++
     flat_map (generate_cfuns_from_expr tn)
       (map snd (flat_map snd (program_gfun_bods_g p))) ++
     flat_map (generate_cfuns_from_expr tn)
       (map snd (flat_map snd (program_cfun_bods_g p)))).
Proof.
intros. apply in_or_app. left. rewrite in_flat_map. destruct x0. simpl in *.
exists f. apply (in_map snd) in H. simpl in H. split; auto.
Qed.

Fact info_in_gfun_bods : forall p tn x0 info,
  In x0 (flat_map snd (program_gfun_bods_g p)) ->
  In info (generate_cfuns_from_expr tn (snd x0)) ->
  In info
    (flat_map (generate_cfuns_from_expr tn) (map snd (program_fun_bods p)) ++
     flat_map (generate_cfuns_from_expr tn)
       (map snd (flat_map snd (program_gfun_bods_g p))) ++
     flat_map (generate_cfuns_from_expr tn)
       (map snd (flat_map snd (program_cfun_bods_g p)))).
Proof.
intros. apply in_or_app. right. apply in_or_app. left.
rewrite in_flat_map. destruct x0. simpl in *.
exists e. apply (in_map snd) in H. simpl in H. split; auto.
Qed.

Fact info_in_cfun_bods : forall p tn x0 info,
  In x0 (flat_map snd (program_cfun_bods_g p)) ->
  In info (generate_cfuns_from_expr tn (snd x0)) ->
  In info
    (flat_map (generate_cfuns_from_expr tn) (map snd (program_fun_bods p)) ++
     flat_map (generate_cfuns_from_expr tn)
       (map snd (flat_map snd (program_gfun_bods_g p))) ++
     flat_map (generate_cfuns_from_expr tn)
       (map snd (flat_map snd (program_cfun_bods_g p)))).
Proof.
intros. apply in_or_app. right. apply in_or_app. right.
rewrite in_flat_map. destruct x0. simpl in *.
exists e. apply (in_map snd) in H. simpl in H. split; auto.
Qed.

Fact unique_sig_lookup : forall {A : Type}  (l : list A) (f : A -> QName) sig,
  In sig l ->
  unique (map f l) ->
  find (fun sig0 : A => eq_QName (f sig) (f sig0)) l =
    Some sig.
Proof.
intros. induction l; inversion H.
- rewrite H1. simpl. rewrite eq_QName_refl. auto.
- simpl. inversion H0; subst. name_destruct_tac.
  + rewrite eq_QName_eq in E__name. apply (in_map f) in H1. rewrite E__name in H1. exfalso. apply H4. auto.
  + IH_auto_tac.
Qed.

Corollary new_cfun_bods_l_typecheck: forall p tn Uniq,
  length (skeleton_cfun_sigs_l (program_skeleton p)) = O ->
  cfun_bods_l_typecheck (lift_match_to_skeleton p tn Uniq) (new_cfun_bods_l p tn).
Proof.
intros. unfold cfun_bods_l_typecheck. rewrite Forall_forall. intros.
pose proof (new_has_all_cfunbods_l p tn Uniq H) as Aux. simpl in Aux.
unfold has_all_cfun_bods in Aux.
exists (fst x).
pose proof H0 as AllInfo. unfold new_cfun_bods_l in AllInfo. repeat (rewrite <- map_app in AllInfo).
rewrite in_map_iff in AllInfo. destruct AllInfo as [info [infoEq infoIn]]. subst.
exists (snd (fst (fst info))). exists (snd (fst info)).
unfold lookup_cfun_sig_l. unfold lookup_cfun_sig_x. simpl. split.
- pose proof (skeleton_cfun_sigs_names_unique_l (lift_match_to_skeleton p tn Uniq)). simpl in H1.
  unfold cfun_sigs_names_unique in H1.
  apply (in_map fst) in H0. unfold cfun_bod in *. rewrite <- Aux in H0.
  assert (In (fst info) (new_cfun_sigs p tn)).
  { clear - infoIn H. unfold new_cfun_sigs. case_eq (skeleton_cfun_sigs_l (program_skeleton p)); intros.
    - simpl. unfold new_cfuns. apply in_map.
      unfold new_cfuns_from_funs. unfold new_cfuns_from_gfuns. unfold new_cfuns_from_cfuns.
      repeat (rewrite <- flat_map_concat_map). auto.
    - apply (f_equal (length (A:=_))) in H0. rewrite H in H0. simpl in H0. discriminate.
  }
  assert (fst (snd info) = fst (fst (fst info))).
  { clear - H Aux infoIn. unfold new_cfun_sigs in Aux. case_eq (skeleton_cfun_sigs_l (program_skeleton p)); intros.
    - rewrite H0 in Aux. simpl in Aux. unfold new_cfuns in Aux. unfold new_cfun_bods_l in Aux.
      unfold new_cfuns_from_funs in Aux. unfold new_cfuns_from_gfuns in Aux. unfold new_cfuns_from_cfuns in Aux.
      repeat (rewrite <- flat_map_concat_map in Aux). repeat (rewrite <- map_app in Aux).
      rewrite combine_fst_snd in infoIn.
      apply (in_map (fun x => (fst (fst (fst x)),snd x))) in infoIn.
      unfold cfun_sig in *.
      rewrite map_fst_f_combine with (f := fun x => fst (fst x)) in infoIn.
      apply (in_map (fun x => (fst x, fst (snd x)))) in infoIn.
      rewrite map_snd_f_combine in infoIn.
      unfold cfun_bods in *. unfold cfun_bod in *.
      unfold cfun_bods in *. unfold cfun_bod in *.
      simpl in infoIn.
      rewrite <- Aux in infoIn.
      evar (q_dummy : QName). pose proof (In_nth _ _ (q_dummy, q_dummy) infoIn).
      do 2 (destruct H1). destruct info. simpl in *. destruct p0. destruct p0. destruct c. simpl in *.
      rewrite combine_nth in H2.
      + inversion H2. auto.
      + do 4 (rewrite map_length). auto.
    - apply (f_equal (length (A:=_))) in H0. rewrite H in H0. simpl in H0. discriminate.
  }
  unfold cfun_bod in *. rewrite H3. do 2 (rewrite <- surjective_pairing). apply unique_sig_lookup with (f := fun x => fst (fst x)); auto.
- eapply T_Match with (bindings_exprs := map fst (index_list 1 (snd (fst (fst info))))) (bindings_types := snd (fst (fst info))).
  + clear; destruct info. simpl. apply T_Var. reflexivity.
  + clear. destruct info. destruct c. destruct p. simpl.
    gen_induction 1 l.
    * reflexivity.
    * simpl. f_equal. apply IHl.
  + apply index_list_typechecks with (r := [fst (fst (snd info))]); reflexivity.
  + unfold lift_match_to_skeleton. unfold lookup_ctors. simpl.
    match_destruct_tac.
    2: { unfold cfun_bod in *.  eauto. }
    pose proof (in_map fst _ _ H0).
    unfold cfun_bod in *. pose proof H1 as H3. rewrite <- Aux in H3.
    unfold new_cfun_sigs in H3.
    assert (skeleton_cfun_sigs_l (program_skeleton p) = []).
    { case_eq (skeleton_cfun_sigs_l (program_skeleton p)); intros; auto. rewrite H2 in H. simpl in H. discriminate. }
    rewrite H2 in H3. simpl in H3. unfold new_cfuns in H3. rewrite map_app in H3. rewrite map_app in H3.
    apply in_app_or in H3. destruct H3; [| repeat (rewrite map_app in H3); apply in_app_or in H3; destruct H3];
    [pose proof (new_cfun_sigs_from_funs_in_dts p tn)
    |pose proof (new_cfun_sigs_from_gfuns_in_dts p tn)
    |pose proof (new_cfun_sigs_from_cfuns_in_dts p tn)];
    unfold cfun_sigs_in_dts in H4;
    rewrite in_map_iff in H3; destruct H3; destruct H3; rewrite Forall_forall in H4;
    pose proof (H4 _ H5); unfold QName in H3; rewrite H3 in H6;
    assert (eq_TypeName (fst (fst (fst x))) (fst (fst (fst x))) = true); try apply eq_TypeName_refl;
    pose proof (conj H6 H7); rewrite <- H3 in H8; rewrite <- filter_In in H8; apply in_split in H8;
    destruct H8; destruct H8; unfold cfun_bod in *; unfold QName in *;
    rewrite <- H3 in E_match; rewrite H8 in E_match; symmetry in E_match; apply app_cons_not_nil in E_match;
    exfalso; auto.
  + clear -H0. rewrite Forall_forall. intros. destruct x. destruct p0. destruct p1.
    unfold new_cfun_bods_l in H0.
    repeat (rewrite map_app in H0). apply in_app_or in H0.
    destruct H0; [| apply in_app_or in H0; destruct H0];
     rewrite in_map_iff in H0; destruct H0 as [x0 [x0Eq x0In]]; subst;
     rewrite in_flat_map in x0In; destruct x0In as [x [xEq xIn]]; rewrite <- x0Eq in H.
    * eapply term_in_fun_bod_name_eq; eauto.
      exists x. split; auto. apply Sub_Refl.
    * eapply term_in_gfun_bod_name_eq; eauto.
      exists x. split; auto. apply Sub_Refl.
    * eapply term_in_cfun_bod_name_eq; eauto.
      exists x. split; auto. apply Sub_Refl.
  + clear - H0 Aux infoIn.
    apply in_app_or in infoIn.
    destruct infoIn; [| apply in_app_or in H; destruct H].
    * rewrite in_flat_map in H; destruct H; destruct H.
      pose proof (program_fun_bods_typecheck p) as Typ.
      unfold fun_bods_typecheck in Typ.
      assert (exists x' sn bs_es e', length bs_es = length (snd (fst (fst info))) /\ map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd info)) /\
        term_in_original_prog (E_Match (fst (fst (snd info)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd info))) x') (snd (fst info))) p) as Aux0.
      { rewrite in_map_iff in H. do 2 (destruct H). rewrite <- H in H1.
        eapply fun_generates_from_match; eauto.
        eapply info_in_fun_bods; eauto.
      }
      destruct Aux0 as [x2 Aux0].
      assert (Forall (fun e => term_in_original_prog e p) x2 /\ map (replace_matches_by_cfun_calls tn) x2 = map snd (snd (snd info))) as Aux'.
      { destruct Aux0. do 3 (destruct H2). destruct H3. split; auto.
        erewrite <- map_snd_combine;
        [ eapply subterm_term_in_original_prog_Match_cases |]; eauto.
        apply (f_equal (length (A:=_))) in H3. rewrite map_length; do 2 (rewrite map_length in H3); auto.
      }
      assert (exists x', Forall (fun e => term_in_original_prog e p) x' /\ map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd info))).
      { exists x2. auto. }
      assert (exists ctx sn bs_es e', length bs_es = length (snd (fst (fst info))) /\
        program_skeleton p / ctx |- (E_Match (fst (fst (snd info)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd info))) x2) (snd (fst info))) : (snd (fst info)));
      [ destruct Aux0 as [snAux [bs_esAux [e [Len [Aux1 Aux2]]]]];
          apply term_in_original_prog_typechecks in Aux2; destruct Aux2 as [ctx [t Typ']];
            inversion Typ'; subst;
              exists ctx; exists snAux; exists bs_esAux; exists e; split; auto
      |].
      destruct H3 as [ctxSub [snSub [bs_esSub [e_sub [LenEq TypSub]]]]]. inversion TypSub; subst.
      apply (f_equal (map snd)) in H11; rewrite map_snd_combine in H11; auto.
      rewrite map_snd_combine in H11; [| symmetry; apply Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto]. subst.
      assert (ctorlist = (filter
               (fun y : ScopedName * list TypeName =>
               let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd info))))
               (skeleton_ctors (program_skeleton p))));
      [> clear - H13; unfold lookup_ctors in H13;
        match_destruct_tac; inversion H13; reflexivity |].
      unfold cfun_bod in *. rewrite <- H3.
      clear H3; pose proof Aux' as H3. destruct H3 as [H3_1 H3_2].
      assert (length (map fst (snd (snd info))) = length x2).
      { apply (f_equal (length (A:=_))) in H3_2; repeat (rewrite map_length in * ); auto. }
      assert (length ctorlist = length x2).
      { clear - H3 H15. rewrite combine_length in H15. rewrite <- H3 in H15.
        rewrite Nat.min_id in H15. rewrite H3 in H15.
        unfold cfun_bod in *.
        destruct info. destruct c0. simpl in *.
        gen_induction (c0, x2) ctorlist.
        - destruct x2; try reflexivity.
          simpl in H15. inversion H15.
        - destruct x2; try solve [inversion H15].
          destruct c0; simpl in*; try solve [inversion H3].
          inversion H15; subst. simpl; f_equal. apply IHctorlist with (c0 := c0); auto.
      }
      unfold cfun_bod in *; rewrite <- H3_2; clear - H3_1 H3_2 H15 H3 H4.
      unfold cfun_bod_named in *; unfold cfun_sig in *; unfold cfun_bod in *.
      destruct info. destruct p1. simpl in *.
      gen_induction (ctorlist, l) x2.
      -- destruct l; try solve [inversion H3_2].
         simpl. destruct ctorlist; try solve [inversion H4].
         apply ListTypeDeriv'_Nil.
      -- destruct l; try solve [inversion H3_2].
         destruct ctorlist; try solve [inversion H4].
         simpl. apply ListTypeDeriv'_Cons.
         ++ inversion H15; subst. apply lift_match_to_skeleton_preserves_typing; auto.
            rewrite Forall_forall in H3_1. apply H3_1. left; auto.
         ++ inversion H15; inversion H3_1; inversion H3_2; subst. apply IHx2; auto.

    * rewrite in_flat_map in H; destruct H; destruct H.
      pose proof (program_cfun_bods_typecheck_g p) as Typ.
      unfold fun_bods_typecheck in Typ.
      assert (exists x' sn bs_es e', length bs_es = length (snd (fst (fst info))) /\ map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd info)) /\
        term_in_original_prog (E_Match (fst (fst (snd info)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd info))) x') (snd (fst info))) p) as Aux0.
      { rewrite in_map_iff in H. do 2 (destruct H). rewrite <- H in H1.
        eapply gfun_generates_from_match; eauto.
        eapply info_in_gfun_bods; eauto.
      }
      destruct Aux0 as [x2 Aux0].
      assert (Forall (fun e => term_in_original_prog e p) x2 /\ map (replace_matches_by_cfun_calls tn) x2 = map snd (snd (snd info))) as Aux'.
      { destruct Aux0. do 3 (destruct H2). destruct H3. split; auto.
        erewrite <- map_snd_combine;
        [ eapply subterm_term_in_original_prog_Match_cases |]; eauto.
        apply (f_equal (length (A:=_))) in H3. rewrite map_length; do 2 (rewrite map_length in H3); auto.
      }
      assert (exists x', Forall (fun e => term_in_original_prog e p) x' /\ map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd info)));
      [> exists x2; auto |].
      assert (exists ctx sn bs_es e', length bs_es = length (snd (fst (fst info))) /\
        program_skeleton p / ctx |- (E_Match (fst (fst (snd info)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd info))) x2) (snd (fst info))) : (snd (fst info)));
      [> destruct Aux0 as [snAux [bs_esAux [e_Aux [Len [Aux1 Aux2]]]]];
        apply term_in_original_prog_typechecks in Aux2; destruct Aux2 as [ctx [t Typ']];
          exists ctx; exists snAux; exists bs_esAux; exists e_Aux; split; auto;
        inversion Typ'; subst; auto
      |].
      destruct H3 as [ctxSub [snSub [bs_esSub [e_Sub [LenEq TypSub]]]]]. inversion TypSub; subst.
      apply (f_equal (map snd)) in H11; rewrite map_snd_combine in H11; auto.
      rewrite map_snd_combine in H11; [| symmetry; apply Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto]. subst.
      assert (ctorlist = (filter
               (fun y : ScopedName * list TypeName =>
               let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd info))))
               (skeleton_ctors (program_skeleton p))));
      [> clear - H13; unfold lookup_ctors in H13;
        match_destruct_tac;
        inversion H13; auto
      |].
      unfold cfun_bod in *. rewrite <- H3.
      clear H3; pose proof Aux' as H3. destruct H3 as [H3_1 H3_2].
      destruct info. destruct c0.
      unfold cfun_bod in *; rewrite <- H3_2; clear - H3_1 H3_2 H15; simpl in *.
      gen_induction (c0, ctorlist) x2; destruct ctorlist; destruct c0; try solve [inversion H15]; try solve [inversion H3_2].
      -- apply ListTypeDeriv'_Nil.
      -- simpl. inversion_clear H15; inversion_clear H3_1; inversion H3_2. apply ListTypeDeriv'_Cons.
         ++ apply lift_match_to_skeleton_preserves_typing; auto.
         ++ apply IHx2; auto.


    * rewrite in_flat_map in H; destruct H; destruct H.
      pose proof (program_cfun_bods_typecheck_g p) as Typ.
      unfold fun_bods_typecheck in Typ.
      assert (exists x' sn bs_es e', length bs_es = length (snd (fst (fst info))) /\ map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd info)) /\
        term_in_original_prog (E_Match (fst (fst (snd info)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd info))) x') (snd (fst info))) p) as Aux0.
      { rewrite in_map_iff in H. do 2 (destruct H). rewrite <- H in H1.
        unfold cfun_bods in *.
        eapply cfun_generates_from_match; eauto.
        eapply info_in_cfun_bods; eauto.
      }
      destruct Aux0 as [x2 Aux0].
      assert (Forall (fun e => term_in_original_prog e p) x2 /\ map (replace_matches_by_cfun_calls tn) x2 = map snd (snd (snd info))) as Aux'.
      { destruct Aux0. do 3 (destruct H2). destruct H3. split; auto.
        erewrite <- map_snd_combine;
        [ eapply subterm_term_in_original_prog_Match_cases |]; eauto.
        apply (f_equal (length (A:=_))) in H3. rewrite map_length; do 2 (rewrite map_length in H3); auto.
      }
      assert (exists x', Forall (fun e => term_in_original_prog e p) x' /\ map (replace_matches_by_cfun_calls tn) x' = map snd (snd (snd info)));
      [> exists x2; auto |].
      assert (exists ctx sn bs_es e', length bs_es = length (snd (fst (fst info))) /\
        program_skeleton p / ctx |- (E_Match (fst (fst (snd info)), sn) e' (combine bs_es (snd (fst (fst info)))) (combine (map fst (snd (snd info))) x2) (snd (fst info))) : (snd (fst (info))));
      [> destruct Aux0 as [snAux [bs_esAux [e_Aux [Len [Aux1 Aux2]]]]];
          apply term_in_original_prog_typechecks in Aux2; destruct Aux2 as [ctx [t Typ']];
            inversion Typ'; subst;
        exists ctx; exists snAux; exists bs_esAux; exists e_Aux; split; auto
      |].
      destruct H3 as [ctxSub [snSub [bs_esSub [e_Sub [LenEq TypSub]]]]]. inversion TypSub; subst.
      apply (f_equal (map snd)) in H11; rewrite map_snd_combine in H11; auto.
      rewrite map_snd_combine in H11; [| symmetry; apply Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto]. subst.
      assert (ctorlist = (filter
               (fun y : ScopedName * list TypeName =>
               let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd info))))
               (skeleton_ctors (program_skeleton p))));
      [> clear - H13; unfold lookup_ctors in H13;
        match_destruct_tac;
        inversion H13; auto
      |].
      unfold cfun_bod in *. rewrite <- H3.
      clear H3; pose proof Aux' as H3. destruct H3 as [H3_1 H3_2].
      destruct info; destruct c0; simpl in *.
      unfold cfun_bod in *; rewrite <- H3_2; clear - H3_1 H3_2 H15.
      gen_induction (c0, ctorlist) x2; destruct ctorlist; destruct c0; inversion H3_2; inversion H15; subst.
      -- apply ListTypeDeriv'_Nil.
      -- inversion H3_1. apply ListTypeDeriv'_Cons; auto.
         apply lift_match_to_skeleton_preserves_typing; auto.

            Unshelve. destruct info. destruct p0. destruct p0. exact q.
Qed.


Lemma replace_matches_by_cfun_calls_no_new_matches: forall (tn : TypeName) (e : expr),
    sublist (collect_match_names (replace_matches_by_cfun_calls tn e))
            (collect_match_names e).
Proof.
  intros tn e.
  induction e using expr_strong_ind; simpl; repeat rewrite map_map;
    try solve [ try (apply sublist_app; try assumption);
                apply sublist_concat; assumption]; simpl.
  - apply sublist_nil.
  - destruct n as [tn' n']. simpl.
    name_destruct_tac; simpl.
    + rewrite map_map.
      apply sublist_skip.
      apply sublist_app; try assumption.
      match goal with
      | [ |- sublist (concat (map _ ?l)) (concat (map _ ?l ++ map _ _)) ] =>
        induction l;
          [> try apply sublist_nil
          | apply sublist_app; try (inversion H0; assumption);
            IH_tac Forall_tail_tac
          ]
      end.
    + apply sublist_cons.
      repeat rewrite map_map. simpl. repeat rewrite concat_app.
      apply sublist_app; try assumption.
      apply sublist_app; apply sublist_concat;
        match goal with
        | [ H: Forall _ (map _ ?l) |- Forall _ ?l ] =>
            induction l;
            [> apply Forall_nil
            | apply Forall_cons;
              [> simpl; inversion H; assumption
              | IH_tac Forall_tail_tac
              ]
            ]
        end.
  - repeat rewrite concat_app.
    apply sublist_app;
    apply sublist_concat; try assumption;
    match goal with
    | [ H: Forall _ (map _ ?l) |- Forall _ ?l ] =>
      induction l;
        [> apply Forall_nil
        | apply Forall_cons;
          [> simpl; inversion H; assumption
          | IH_tac Forall_tail_tac
          ]
        ]
    end.
Qed.

(********************************************************************)
(*** lemmas for uniqueness of matches ***)
(********************************************************************)


Ltac liftmatch_destruct_hin_app_tac :=
  try match goal with
      | [ Hin: In _ _ |- _ ] =>
        repeat (rewrite map_app in Hin; rewrite concat_app in Hin);
        repeat rewrite in_app_iff in Hin
      end.

Lemma replace_matches_reflects_match_names:
  forall (tn : TypeName) (qn : QName) (e : expr),
    In qn (collect_match_names (replace_matches_by_cfun_calls tn e)) ->
    In qn (collect_match_names e).
Proof.
  intros tn qn e Hin.
  induction e using expr_strong_ind; simpl in *; auto;
    let rec listtac :=
        match goal with
        | [ Hf: Forall _ ?lst, Hin: In _ _ |- _ ] =>
          induction lst;
            auto;
            simpl in *;
                       inversion_clear Hf;
                       rewrite in_app_iff in Hin; rewrite in_app_iff;
                         inversion_clear Hin; [> left | right ]; auto
        end
    in let rec app_tac :=
           match goal with
           | [ Hin: In _ _ |- _ ] =>
             repeat (rewrite map_app in Hin; rewrite concat_app in Hin);
               repeat rewrite in_app_iff in Hin;
                                              repeat rewrite in_app_iff
  end
    in try name_destruct_tac; simpl in *; try rewrite concat_app; try rewrite concat_app in Hin;
    try app_tac;
    try listtac;
    try match goal with
        | [ Hin: _ \/ _ \/ _ |- _ ] =>
          inversion_clear Hin; [> left; solve [auto] |]
        end;
  try solve [match goal with
             | [ Hin: _ \/ _ |- _ ] =>
               inversion Hin; [> left | right ]; auto; try listtac
             end].
  - rewrite map_map in Hin.
    inversion_clear Hin; right; [> left; solve [auto] | right; left].
    repeat rewrite in_app_iff; repeat rewrite in_app_iff in H1.
    induction es; auto; simpl in *.
    rewrite in_app_iff in H1; rewrite in_app_iff.
    inversion_clear H0.
    inversion_clear H1; [> left | right ]; auto.
  - do 2 rewrite map_map in Hin.
    repeat rewrite in_app_iff in *; rename Hin into H1.
    inversion_clear H1 as [Hin | [Hin | [Hin | Hin]]]; [> left | right; left | right; right; left | right; right; right ]; auto.
    + induction es; auto; simpl in *.
      rewrite in_app_iff in Hin; rewrite in_app_iff.
      inversion_clear H0.
      inversion_clear Hin; [> left | right ]; auto.
    + induction ls; auto; simpl in *.
      rewrite in_app_iff in Hin; rewrite in_app_iff.
      inversion_clear H.
      inversion_clear Hin; [> left | right ]; auto.
  - inversion_clear Hin; [> left; clear H | right; clear H0].
    + induction es; auto; simpl in *.
      rewrite in_app_iff in H1; rewrite in_app_iff.
      inversion_clear H0.
      inversion_clear H1; [> left | right ]; auto.
    + induction ls; auto; simpl in *.
      rewrite in_app_iff in H1; rewrite in_app_iff.
      inversion_clear H.
      inversion_clear H1; [> left | right ]; auto.
Qed.

Ltac liftmatch_generate_cfuns_reflects_match_names_list_tac :=
  match goal with
  | [ Hin: In _ _, Hf: Forall _ ?lst |- _ ] =>
    let lst'' := match lst with
                 | context [?lst'] => lst'
                 end
    in clear - Hin Hf;
       let lst'' := match lst with
                    | context [?lst'] =>
                      match type of Hin with
                      | context [lst'] =>
                        match type of lst' with
                        | list _ => lst'
                        end
                      end
                    end
       in clear - Hin Hf;
          induction lst''; simpl in *; auto;
          inversion_clear Hf;
          liftmatch_destruct_hin_app_tac;
          rewrite in_app_iff;
          inversion Hin; [> left | right]; auto
  end.

Lemma generate_cfuns_reflects_match_names: forall (tn : TypeName) (e : expr) (qn : QName),
    In qn (concat
             (map (fun x : ScopedName * expr => collect_match_names (snd x))
                  (concat
                     (map (fun x : cfun_sig * cfun_bod_named => snd (snd x))
                          (generate_cfuns_from_expr tn e))))) ->
    In qn (collect_match_names e).
Proof.
  intros tn e qn H.
  induction e using expr_strong_ind; simpl in *; auto;
    try liftmatch_destruct_hin_app_tac;
    try (rewrite in_app_iff;
    match goal with
      | [ Hin: _ \/ _ |- _ ] =>
        inversion Hin; [> left; solve [auto] | right; auto ]
      end);
    try solve [liftmatch_generate_cfuns_reflects_match_names_list_tac].

  - rewrite concat_app; repeat rewrite in_app_iff in *.
    inversion_clear H as [Hin | [Hin | [Hin | Hin]]]; auto.
    + name_destruct_tac; simpl in *; try contradiction.
      rewrite app_nil_r in Hin; rewrite map_map in Hin; simpl in Hin.
      do 3 right.
      induction ls; auto; simpl in *.
      rewrite in_app_iff in Hin; rewrite in_app_iff.
      inversion_clear Hin as [Hin' | Hin']; [> left | right ].
      * eapply replace_matches_reflects_match_names; eauto.
      * apply IHls; auto. Forall_tail_tac.
    + do 2 right; left.
      liftmatch_generate_cfuns_reflects_match_names_list_tac.
    + do 3 right.
      liftmatch_generate_cfuns_reflects_match_names_list_tac.
  - rewrite concat_app; repeat rewrite in_app_iff.
    inversion_clear H as [Hin | Hin];
    [> left | right]; liftmatch_generate_cfuns_reflects_match_names_list_tac.
Qed.

Lemma generate_cfuns_reflects_match_names_flat: forall (tn : TypeName) (g : list expr) (qn : QName),
    In qn
       (concat
          (map (fun x : ScopedName * expr => collect_match_names (snd x))
               (concat
                  (map (fun x : cfun_sig * cfun_bod_named => snd (snd x))
                       (flat_map (generate_cfuns_from_expr tn) g))))) ->
    In qn (flat_map collect_match_names g).
Proof.
  intros tn g qn H.
  induction g; auto; simpl in *.
  repeat (rewrite map_app in H; rewrite concat_app in H).
  rewrite in_app_iff in *.
  inversion H; auto; left.
  apply (generate_cfuns_reflects_match_names tn); auto.
Qed.


Ltac Forall_notin_app_destr_tac :=
  match goal with
  | [ Hf: Forall (fun x => ~ In x (?l ++ ?r)) ?ls |- _ ] =>
    let Hl := fresh Hf in
    let Hr := fresh Hf in
    assert (Hl: Forall (fun x => ~ In x l) ls);
    [> rewrite Forall_forall in Hf |- *; intros; intro; eapply Hf; eauto |];
    assert (Hr: Forall (fun x => ~ In x r) ls);
    [> rewrite Forall_forall in Hf |- *; intros; intro; eapply Hf; eauto |];
    clear Hf
  end.
Ltac unique_app_destr_full_tac :=
  repeat unique_app_destr_tac; repeat Forall_notin_app_destr_tac.
Ltac split_fun_by full splitfun :=
  match full with
  | fun x => ?f (splitfun x) => f
  | fun x => ?f (@?g x) =>
    let h := split_fun_by g splitfun in
    constr:(fun x => f (h x))
  end.




Local Hint Resolve -> In_app_iff.
Section split_matches_into_replace_generate_sec.

Lemma split_matches_into_replace_generate: forall (tn : TypeName) (e : expr) (qn : QName),
    unique (collect_match_names e) ->
    ~ (In qn (collect_match_names (replace_matches_by_cfun_calls tn e)) /\
       In qn (concat (map collect_match_names (concat (map (fun x => (map snd (snd (snd x)))) (generate_cfuns_from_expr tn e)))))).
Proof.
  intros tn e qn Hunique H.
  inversion_clear H as [Hin_rep Hin_gen].
  induction e using expr_strong_ind; simpl in *; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_matches_reflects_match_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
      assert (In qn (concat (map collect_match_names ls)));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      apply H3. clear - H2.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in H2; repeat rewrite concat_app in H2).
      rewrite in_app_iff; rewrite in_app_iff in H2.
      inversion H2; [> left | right]; auto.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + assert (In qn (concat (map collect_match_names ls))); [> | clear H].
      { clear - H.
        apply (in_map_concat _ _ qn ls (replace_matches_reflects_match_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_match_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_cfuns_reflects_match_names tn).
        induction (generate_cfuns_from_expr tn a); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion H2; [> left | right ]; auto.
        rewrite <- map_map; auto.
      }
  - unique_app_destr_tac.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    rewrite in_app_iff in *.
    repeat match goal with
           | [ H: _ \/ _ |- _ ] =>
             let H1 := fresh H
             in inversion_clear H as [H1 | H1]
           end; auto;
      try solve [
            (rewrite map_map in Hin_rep0;
             apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hin_rep0)
            || apply (replace_matches_reflects_match_names tn) in Hin_rep0;
            rewrite <- map_map with (g := map snd) in Hin_gen0;
            rewrite <- concat_map in Hin_gen0;
            rewrite map_map in Hin_gen0;
            (rewrite <- flat_map_concat_map with (l := ls) in Hin_gen0;
             apply (generate_cfuns_reflects_match_names_flat tn) in Hin_gen0;
             rewrite flat_map_concat_map in Hin_gen0)
            || apply generate_cfuns_reflects_match_names in Hin_gen0;
            rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto
          ].
    + clear IHe Hunique0 Hunique_f.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in *; rewrite concat_app in * ).
      rewrite in_app_iff in *.
      inversion_clear H.
      unique_app_destr_tac; rewrite Forall_forall in Hunique1_f.
      repeat match goal with
             | [ H: _ \/ _ |- _ ] =>
               let H1 := fresh H
               in inversion_clear H as [H1 | H1]
             end; auto.
      * eapply Hunique1_f; eauto;
          try (eapply replace_matches_reflects_match_names; eauto).
        rewrite <- flat_map_concat_map;
          apply (generate_cfuns_reflects_match_names_flat tn);
          rewrite flat_map_concat_map.
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * eapply Hunique1_f; eauto;
          try (apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)); rewrite map_map in Hin_rep1; eauto).
        apply (generate_cfuns_reflects_match_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_matches_reflects_match_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
      assert (In qn (concat (map collect_match_names ls)));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      apply H3. clear - H2.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in H2; repeat rewrite concat_app in H2).
      rewrite in_app_iff; rewrite in_app_iff in H2.
      inversion H2; [> left | right]; auto.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + assert (In qn (concat (map collect_match_names ls))); [> | clear H].
      { clear - H.
        apply (in_map_concat _ _ qn ls (replace_matches_reflects_match_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_match_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_cfuns_reflects_match_names tn).
        induction (generate_cfuns_from_expr tn a); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion H2; [> left | right ]; auto.
        rewrite <- map_map; auto.
      }
  - unique_app_destr_tac.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    rewrite in_app_iff in *.
    repeat match goal with
           | [ H: _ \/ _ |- _ ] =>
             let H1 := fresh H
             in inversion_clear H as [H1 | H1]
           end; auto;
      try solve [
            (rewrite map_map in Hin_rep0;
             apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hin_rep0)
            || apply (replace_matches_reflects_match_names tn) in Hin_rep0;
            rewrite <- map_map with (g := map snd) in Hin_gen0;
            rewrite <- concat_map in Hin_gen0;
            rewrite map_map in Hin_gen0;
            (rewrite <- flat_map_concat_map with (l := ls) in Hin_gen0;
             apply (generate_cfuns_reflects_match_names_flat tn) in Hin_gen0;
             rewrite flat_map_concat_map in Hin_gen0)
            || apply generate_cfuns_reflects_match_names in Hin_gen0;
            rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto
          ].

    + clear IHe Hunique0 Hunique_f.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in *; rewrite concat_app in * ).
      rewrite in_app_iff in *.
      inversion_clear H.
      unique_app_destr_tac; rewrite Forall_forall in Hunique1_f.
      repeat match goal with
             | [ H: _ \/ _ |- _ ] =>
               let H1 := fresh H
               in inversion_clear H as [H1 | H1]
             end; auto.
      * eapply Hunique1_f; eauto;
          try (eapply replace_matches_reflects_match_names; eauto).
        rewrite <- flat_map_concat_map;
          apply (generate_cfuns_reflects_match_names_flat tn);
          rewrite flat_map_concat_map.
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * eapply Hunique1_f; eauto;
          try (apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)); rewrite map_map in Hin_rep1; eauto).
        apply (generate_cfuns_reflects_match_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_matches_reflects_match_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
      assert (In qn (concat (map collect_match_names ls)));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      apply H3. clear - H2.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in H2; repeat rewrite concat_app in H2).
      rewrite in_app_iff; rewrite in_app_iff in H2.
      inversion H2; [> left | right]; auto.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + assert (In qn (concat (map collect_match_names ls))); [> | clear H].
      { clear - H.
        apply (in_map_concat _ _ qn ls (replace_matches_reflects_match_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_match_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_cfuns_reflects_match_names tn).
        induction (generate_cfuns_from_expr tn a); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion H2; [> left | right ]; auto.
        rewrite <- map_map; auto.
      }
  - repeat (rewrite map_app in *; rewrite concat_app in * ).
    inversion_clear Hunique as [| _x __x Hunique_f Hunique0].
    unique_app_destr_full_tac.
    name_destruct_tac; simpl in *;
      repeat (rewrite map_app in *; rewrite concat_app in * );
      repeat (rewrite in_app_iff in * ).
    + inversion_clear Hin_gen as [Hin_gen' | [Hin_gen' | [ Hin_gen' | Hin_gen' ]]];
        [> try (inversion_clear Hin_gen' as [Hin_gen | Hin_gen]; [> | easy]) | .. ];
        inversion_clear Hin_rep as [Hin_rep' | Hin_rep']; auto;
      try solve [
            repeat
              match goal with
              | [ Hr: In _ _ |- _ ] =>
                (apply replace_matches_reflects_match_names in Hr)
                || (try (rewrite (map_map _ snd) in Hr; simpl in Hr);
                   rewrite map_map in Hr;
                   match type of Hr with
                   | In _ ?l =>
                     (let rec go lst :=
                          match lst with
                          | _ (map ?f ?l) =>
                            match f with
                            | context [@fst ?lt ?rt] =>
                              (let g := split_fun_by f (@fst lt rt)
                               in rewrite <- (map_map (@fst lt rt) g) in Hr;
                                  apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hr);
                              rewrite map_map in Hr
                     | context [@snd ?lt ?rt] =>
                       (let g := split_fun_by f (@snd lt rt)
                        in rewrite <- (map_map (@snd lt rt) g) in Hr;
                           apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hr);
                       rewrite map_map in Hr
                      end
                     | ?f ?l => go l
                      end
                       in go l)
                   end)
              end;
            repeat
              match goal with
              | [ Hg: In _ _ |- _ ] =>
                rewrite <- (map_map _ (map snd)) in Hg;
                rewrite <- concat_map in Hg;
                rewrite map_map in Hg;
                (apply generate_cfuns_reflects_match_names in Hg)
                || (match type of Hg with
                   | In _ ?l =>
                     (let rec go lst :=
                          match lst with
                          | _ (map ?f ?l) =>
                            match f with
                            | context [@fst ?lt ?rt] =>
                              (let g := split_fun_by f (@fst lt rt)
                               in rewrite <- (map_map (@fst lt rt) g) in Hg;
                                  rewrite <- (flat_map_concat_map g _) in Hg)
                            | context [@snd ?lt ?rt] =>
                              (let g := split_fun_by f (@snd lt rt)
                               in rewrite <- (map_map (@snd lt rt) g) in Hg;
                                  rewrite <- (flat_map_concat_map g _) in Hg)
                            end;
                            (apply generate_cfuns_reflects_match_names_flat in Hg);
                            (rewrite flat_map_concat_map in Hg);
                            rewrite map_map in Hg
                     | ?f ?l => go l
                      end
                       in go l)
                   end)
              end;
            match goal with
            | [ Hf: Forall (fun x => ~ In x ?ls) ?ls',
                    H: In _ ?ls,
                       H': In _ ?ls' |- _ ] =>
              rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
            end
          ].

      clear - Hin_gen' Hin_rep' Hunique0 H0.
      induction es; auto; simpl in *; inversion_clear H0.
      repeat (repeat rewrite map_app in *; rewrite concat_app in * );
        rewrite in_app_iff in *.
      unique_app_destr_tac.
      inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
      * rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          apply generate_cfuns_reflects_match_names in H0.
        rewrite <- map_map with (f := fst) in H2;
          rewrite map_map in H2;
          apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in H2;
          rewrite map_map in H2.
        rewrite Forall_forall in Hunique0_f; eapply Hunique0_f; eauto.
      * rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          rewrite <- map_map with (f := fst) in H0;
          rewrite <- flat_map_concat_map with (l := map fst es) in H0;
          apply generate_cfuns_reflects_match_names_flat in H0;
          rewrite flat_map_concat_map in H0; rewrite map_map in H0.
        apply replace_matches_reflects_match_names in H2.
        rewrite Forall_forall in Hunique0_f; eapply Hunique0_f; eauto.
    + rewrite concat_app in Hin_rep; rewrite in_app_iff in Hin_rep.
      inversion_clear Hin_gen as [Hin_gen' | [Hin_gen' | Hin_gen']];
        inversion_clear Hin_rep as [Hin_rep' | [Hin_rep' | [Hin_rep' | Hin_rep']]]; auto;
          try solve [
                repeat
                  match goal with
                  | [ Hr: In _ _ |- _ ] =>
                    (apply replace_matches_reflects_match_names in Hr)
                    || (try (rewrite (map_map _ snd) in Hr; simpl in Hr);
                       rewrite map_map in Hr; simpl in Hr;
                       match type of Hr with
                       | In _ ?l =>
                         (let rec go lst :=
                              match lst with
                              | _ (map ?f ?l) =>
                                match f with
                                | context [@fst ?lt ?rt] =>
                                  (let g := split_fun_by f (@fst lt rt)
                                   in rewrite <- (map_map (@fst lt rt) g) in Hr;
                                      apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hr);
                                  rewrite map_map in Hr
                         | context [@snd ?lt ?rt] =>
                           (let g := split_fun_by f (@snd lt rt)
                            in rewrite <- (map_map (@snd lt rt) g) in Hr;
                               apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hr);
                           rewrite map_map in Hr
                          end
                         | ?f ?l => go l
                          end
                           in go l)
                       end)
                  end;
                repeat
                  match goal with
                  | [ Hg: In _ _ |- _ ] =>
                    rewrite <- (map_map _ (map snd)) in Hg;
                    rewrite <- concat_map in Hg;
                    rewrite map_map in Hg;
                    (apply generate_cfuns_reflects_match_names in Hg)
                    || (match type of Hg with
                       | In _ ?l =>
                         (let rec go lst :=
                              match lst with
                              | _ (map ?f ?l) =>
                                match f with
                                | context [@fst ?lt ?rt] =>
                                  (let g := split_fun_by f (@fst lt rt)
                                   in rewrite <- (map_map (@fst lt rt) g) in Hg;
                                      rewrite <- (flat_map_concat_map g _) in Hg)
                                | context [@snd ?lt ?rt] =>
                                  (let g := split_fun_by f (@snd lt rt)
                                   in rewrite <- (map_map (@snd lt rt) g) in Hg;
                                      rewrite <- (flat_map_concat_map g _) in Hg)
                                end;
                                (apply generate_cfuns_reflects_match_names_flat in Hg);
                                (rewrite flat_map_concat_map in Hg);
                                rewrite map_map in Hg
                         | ?f ?l => go l
                          end
                           in go l)
                       end)
                  end;
                (match goal with
                 | [ Hf: Forall (fun x => ~ In x ?ls) ?ls',
                         H: In _ ?ls,
                            H': In _ ?ls' |- _ ] =>
                   rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
                 end
                 ||
                 match goal with
                 | [ Hn: ~ _ |- _ ] =>
                   subst; apply Hn; auto
                 end)
              ].
      * clear - Hin_gen' Hin_rep' Hunique0 H0.
        induction es; auto; simpl in *; inversion_clear H0.
        repeat (repeat rewrite map_app in *; rewrite concat_app in * );
          rewrite in_app_iff in *.
        unique_app_destr_tac.
        inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
        -- rewrite <- map_map with (g := map snd) in H0;
             rewrite <- concat_map in H0;
             rewrite map_map in H0;
             apply generate_cfuns_reflects_match_names in H0.
           rewrite map_map in H2; simpl in H2;
             rewrite <- map_map with (f := fst) (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) in H2;
             apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in H2;
             rewrite map_map in H2.
           rewrite Forall_forall in Hunique0_f; eapply Hunique0_f; eauto.
        -- rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          rewrite <- map_map with (f := fst) in H0;
          rewrite <- flat_map_concat_map with (l := map fst es) in H0;
          apply generate_cfuns_reflects_match_names_flat in H0;
          rewrite flat_map_concat_map in H0; rewrite map_map in H0.
        apply replace_matches_reflects_match_names in H2.
        rewrite Forall_forall in Hunique0_f; eapply Hunique0_f; eauto.
      * clear - Hin_gen' Hin_rep' Hunique3 H.
        induction ls; auto; simpl in *; inversion_clear H.
        repeat (repeat rewrite map_app in *; rewrite concat_app in * );
          rewrite in_app_iff in *.
        unique_app_destr_tac.
        inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
        -- rewrite <- map_map with (g := map snd) in H;
             rewrite <- concat_map in H;
             rewrite map_map in H;
             apply generate_cfuns_reflects_match_names in H.
           rewrite map_map in H2; simpl in H2;
             rewrite <- map_map with (f := snd) (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) in H2;
             apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in H2;
             rewrite map_map in H2.
           rewrite Forall_forall in Hunique3_f; eapply Hunique3_f; eauto.
        -- rewrite <- map_map with (g := map snd) in H;
          rewrite <- concat_map in H;
          rewrite map_map in H;
          rewrite <- map_map with (f := snd) (l := ls) in H;
          rewrite <- flat_map_concat_map with (l := map snd ls) in H;
          apply generate_cfuns_reflects_match_names_flat in H;
          rewrite flat_map_concat_map in H; rewrite map_map in H.
        apply replace_matches_reflects_match_names in H2.
        rewrite Forall_forall in Hunique3_f; eapply Hunique3_f; eauto.
  - repeat (rewrite map_app in *; rewrite concat_app in * ).
    rewrite in_app_iff in *.
    unique_app_destr_tac.
    inversion_clear Hin_rep as [Hin_rep' | Hin_rep'];
      inversion_clear Hin_gen as [Hin_gen' | Hin_gen']; auto;
        try solve [
              repeat
                match goal with
                | [ Hr: In _ _ |- _ ] =>
                  (apply replace_matches_reflects_match_names in Hr)
                  || (try (rewrite (map_map _ snd) in Hr; simpl in Hr);
                     rewrite map_map in Hr; simpl in Hr;
                     match type of Hr with
                     | In _ ?l =>
                       (let rec go lst :=
                            match lst with
                            | _ (map ?f ?l) =>
                              match f with
                              | context [@fst ?lt ?rt] =>
                                (let g := split_fun_by f (@fst lt rt)
                                 in rewrite <- (map_map (@fst lt rt) g) in Hr;
                                    apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hr);
                                rewrite map_map in Hr
                       | context [@snd ?lt ?rt] =>
                         (let g := split_fun_by f (@snd lt rt)
                          in rewrite <- (map_map (@snd lt rt) g) in Hr;
                             apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hr);
                         rewrite map_map in Hr
                        end
                       | ?f ?l => go l
                        end
                         in go l)
                     end)
                end;
              repeat
                match goal with
                | [ Hg: In _ _ |- _ ] =>
                  rewrite <- (map_map _ (map snd)) in Hg;
                  rewrite <- concat_map in Hg;
                  rewrite map_map in Hg;
                  (apply generate_cfuns_reflects_match_names in Hg)
                  || (match type of Hg with
                     | In _ ?l =>
                       (let rec go lst :=
                            match lst with
                            | _ (map ?f ?l) =>
                              match f with
                              | context [@fst ?lt ?rt] =>
                                (let g := split_fun_by f (@fst lt rt)
                                 in rewrite <- (map_map (@fst lt rt) g) in Hg;
                                    rewrite <- (flat_map_concat_map g _) in Hg)
                              | context [@snd ?lt ?rt] =>
                                (let g := split_fun_by f (@snd lt rt)
                                 in rewrite <- (map_map (@snd lt rt) g) in Hg;
                                    rewrite <- (flat_map_concat_map g _) in Hg)
                              end;
                              (apply generate_cfuns_reflects_match_names_flat in Hg);
                              (rewrite flat_map_concat_map in Hg);
                              rewrite map_map in Hg
                       | ?f ?l => go l
                        end
                         in go l)
                     end)
                end;
              match goal with
              | [ Hf: Forall (fun x => ~ In x ?ls) ?ls',
                      H: In _ ?ls,
                         H': In _ ?ls' |- _ ] =>
                rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
              end
            ].
    + clear - Hin_gen' Hin_rep' Hunique0 H0.
      induction es; auto; simpl in *; inversion_clear H0.
      repeat (repeat rewrite map_app in *; rewrite concat_app in * );
        rewrite in_app_iff in *.
      unique_app_destr_tac.
      inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
      * rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          apply generate_cfuns_reflects_match_names in H0.
        rewrite map_map in H2; simpl in H2;
          rewrite <- map_map with (f := fst) (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) in H2;
          apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in H2;
          rewrite map_map in H2.
        rewrite Forall_forall in Hunique0_f; eapply Hunique0_f; eauto.
      * rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          rewrite <- map_map with (f := fst) in H0;
          rewrite <- flat_map_concat_map with (l := map fst es) in H0;
          apply generate_cfuns_reflects_match_names_flat in H0;
          rewrite flat_map_concat_map in H0; rewrite map_map in H0.
        apply replace_matches_reflects_match_names in H2.
        rewrite Forall_forall in Hunique0_f; eapply Hunique0_f; eauto.
    + clear - Hin_gen' Hin_rep' Hunique1 H.
      induction ls; auto; simpl in *; inversion_clear H.
      repeat (repeat rewrite map_app in *; rewrite concat_app in * );
        rewrite in_app_iff in *.
      unique_app_destr_tac.
      inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
      * rewrite <- map_map with (g := map snd) in H;
          rewrite <- concat_map in H;
          rewrite map_map in H;
          apply generate_cfuns_reflects_match_names in H.
        rewrite map_map in H2; simpl in H2;
          rewrite <- map_map with (f := snd) (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) in H2;
          apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in H2;
          rewrite map_map in H2.
        rewrite Forall_forall in Hunique1_f; eapply Hunique1_f; eauto.
      * rewrite <- map_map with (g := map snd) in H;
          rewrite <- concat_map in H;
          rewrite map_map in H;
          rewrite <- map_map with (f := snd) (l := ls) in H;
          rewrite <- flat_map_concat_map with (l := map snd ls) in H;
          apply generate_cfuns_reflects_match_names_flat in H;
          rewrite flat_map_concat_map in H; rewrite map_map in H.
        apply replace_matches_reflects_match_names in H2.
        rewrite Forall_forall in Hunique1_f; eapply Hunique1_f; eauto.
  - repeat (rewrite map_app in Hin_gen; rewrite concat_app in Hin_gen).
    rewrite in_app_iff in *.
    inversion_clear Hin_rep; inversion_clear Hin_gen.
    * apply IHe1; auto; unique_sublist_tac.
    * apply replace_matches_reflects_match_names in H.
      rewrite <- map_map with (g := map snd) (f := fun x => snd (@snd cfun_sig (QName * list (ScopedName * expr)) x)) in H0;
        rewrite <- concat_map in H0; rewrite map_map in H0.
      apply (generate_cfuns_reflects_match_names tn _ qn) in H0.
      rewrite <- uniqueness_app_rewrite in Hunique.
      inversion Hunique as [Hx [Hxx Hxxx]].
      rewrite Forall_forall in Hxxx.
      apply (Hxxx qn); auto.
    * apply replace_matches_reflects_match_names in H.
      rewrite <- map_map with (g := map snd) (f := fun x => snd (@snd cfun_sig (QName * list (ScopedName * expr)) x)) in H0;
        rewrite <- concat_map in H0; rewrite map_map in H0.
      apply (generate_cfuns_reflects_match_names tn _ qn) in H0.
      rewrite <- uniqueness_app_rewrite in Hunique.
      inversion Hunique as [Hx [Hxx Hxxx]].
      rewrite Forall_forall in Hxxx.
      apply (Hxxx qn); auto.
    * apply IHe2; auto; unique_sublist_tac.
      Unshelve. all: apply True.
Qed.

End split_matches_into_replace_generate_sec.

Local Hint Immediate Forall_nil.
Local Hint Immediate Unique_nil.

Lemma generate_cfuns_unique_matches_propagates: forall (tn : TypeName) (e : expr),
    unique (collect_match_names e) ->
    unique (concat (map (fun x : ScopedName * expr => collect_match_names (snd x))
                        (concat (map (fun x : cfun_sig * cfun_bod_named => snd (snd x)) (generate_cfuns_from_expr tn e))))).
Proof.
  intros tn e H.
  induction e using expr_strong_ind; simpl in *; auto.
  - match goal with
    | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
      induction lst; inversion_clear Hf; auto; simpl;
        repeat (rewrite map_app; rewrite concat_app);
        simpl in Hunique;
        apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
    end.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_cfuns_reflects_match_names in Hin.
    pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1.
    rewrite concat_map in Hnin at 1.
    rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_cfuns_from_expr tn)).
    unfold cfun_bod_named in *.
    specialize Hlem' with (2 := Hnin).
    apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
    apply Hlem'; intros. apply Hlem.
    rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    apply uniqueness_app; auto.
    + IH_tac. unique_sublist_tac.
    + rewrite <- uniqueness_app_rewrite in H; apply proj2 in H; apply proj1 in H.
      match goal with
      | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Hunique;
          apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      unfold cfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      unfold cfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - match goal with
    | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
      induction lst; inversion_clear Hf; auto; simpl;
        repeat (rewrite map_app; rewrite concat_app);
        simpl in Hunique;
        apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
    end.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_cfuns_reflects_match_names in Hin.
    pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1.
    rewrite concat_map in Hnin at 1.
    rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_cfuns_from_expr tn)).
    unfold cfun_bod_named in *.
    specialize Hlem' with (2 := Hnin).
    apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
    apply Hlem'; intros. apply Hlem.
    rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    apply uniqueness_app; auto.
    + IH_tac. unique_sublist_tac.
    + rewrite <- uniqueness_app_rewrite in H; apply proj2 in H; apply proj1 in H.
      match goal with
      | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Hunique;
          apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      unfold cfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      unfold cfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - match goal with
    | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
      induction lst; inversion_clear Hf; auto; simpl;
        repeat (rewrite map_app; rewrite concat_app);
        simpl in Hunique;
        apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
    end.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_cfuns_reflects_match_names in Hin.
    pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_cfuns_from_expr tn)).
    specialize Hlem' with (2 := Hnin).
    apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
    apply Hlem'; intros. apply Hlem.
    rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    rewrite concat_app in H.
    inversion_clear H as [|_x __x Hnin' Hunique].
    unique_app_destr_full_tac.
    repeat match goal with
           | [ |- unique (?l ++ ?r) ] =>
             apply uniqueness_app
           end;
      repeat
        match goal with
        | [  |- Forall (fun x => ~ In x (?l ++ ?r)) ?ls  ] =>
          let H := fresh in
          assert (H: Forall (fun x => ~ In x l) ls /\ Forall (fun x => ~ In x r) ls ->
                     Forall (fun x => ~ In x (l ++ r)) ls);
            [> let H' := fresh in intro H'; inversion_clear H';
                                  rewrite Forall_forall in *;
                                  intros;
                                  (let H'' := fresh in
                                   intro H'';
                                   rewrite in_app_iff in H''; inversion H'';
                                   match goal with
                                   | [ H: _ |- _ ] =>
                                     eapply H; solve [eauto]
                                   end)
            | apply H; split; clear H ]
        end;
      try (name_destruct_tac; simpl; auto; rewrite app_nil_r); auto;
        try solve [
               match goal with
      | [ Hf: Forall _ _ |- context [?lst] ] =>
        match type of lst with
        | list _ => idtac
        end;
          match lst with
          | _ _ => fail 1
          | _ => idtac
          end;
          match goal with
          | [ Hu: unique ?ls |- _ ] =>
            match ls with
            | context [lst] => clear - Hu Hf
            end
          end;
          induction lst; inversion_clear Hf; simpl in *; auto;
            unique_app_destr_tac;
            repeat (rewrite map_app; rewrite concat_app);
            apply uniqueness_app; auto;
              rewrite Forall_forall;
              intros qn Hnin Hin;
              apply generate_cfuns_reflects_match_names in Hnin;
              rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hin;
              match type of Hin with
              | context [map ?f lst] =>
                rewrite <- (flat_map_concat_map _ (map f lst)) in Hin;
                  apply generate_cfuns_reflects_match_names_flat in Hin;
                  rewrite flat_map_concat_map in Hin;
                  rewrite map_map in Hin
              end
      end;
      match goal with
      | [ H: Forall _ _ |- _ ] =>
        rewrite Forall_forall in H; eapply H; solve [eauto]
      end
            ];
        try solve [
              rewrite Forall_forall; intros; intro;
              repeat match goal with
                     | [ H: In _ _ |- _ ] =>
                       apply generate_cfuns_reflects_match_names in H
                     end;
              repeat match goal with
                     | [ Hin: In _ _ |- _ ] =>
                             rewrite <- map_map with (f := snd) in Hin; rewrite map_map with (g := snd) in Hin;
                             simpl in Hin; rewrite <- map_map with (f := snd) in Hin; rewrite map_map in Hin;
                             apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in Hin;
                             rewrite map_map in Hin
                     end;
              match goal with
              | [ H: In _ ?lst |- _ ] =>
                match lst with
                | context [?lst'] =>
                  match lst' with
                  | map (fun x => generate_cfuns_from_expr _ (?f x)) ?l' =>
                    rewrite <- map_map with (l := l') in H;
                    rewrite <- flat_map_concat_map with (l := map f l') in H;
                    apply generate_cfuns_reflects_match_names_flat in H;
                    rewrite flat_map_concat_map in H; rewrite map_map in *
                  end
                end
              end;
              match goal with
              | [ H: Forall _ _ |- _ ] =>
                rewrite Forall_forall in H; eapply H; solve [eauto]
              end
            ].

    + rewrite map_map; simpl.
      clear - H0 Hunique3.
      induction ls; auto; simpl in *; inversion_clear H0.
      replace_with_snd in *.
      unique_app_destr_tac.
      apply uniqueness_app; auto.
      * pose proof (replace_matches_by_cfun_calls_no_new_matches tn (snd a)).
        unique_sublist_tac.
      * rewrite Forall_forall; intros; intro.
        apply replace_matches_reflects_match_names in H0.
        rewrite <- map_map with (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) (f := snd) in H2.
        apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in H2;
          rewrite map_map in H2.
        rewrite Forall_forall in Hunique3_f; eapply Hunique3_f; eauto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      rewrite <- map_map with (l := ls) in Hnin;
        rewrite <- map_map with (l := es) in Hin.
      rewrite <- flat_map_concat_map with (l := map fst es) in Hin;
        rewrite <- flat_map_concat_map with (l := map snd ls) in Hnin.
      apply (generate_cfuns_reflects_match_names_flat tn) in Hnin;
        apply (generate_cfuns_reflects_match_names_flat tn) in Hin.
      rewrite flat_map_concat_map in Hin, Hnin; rewrite map_map in *.
      match goal with
      | [ H: Forall _ _ |- _ ] =>
        rewrite Forall_forall in H; eapply H; solve [eauto]
      end.
    + rewrite Forall_forall; intros qn Hin Hin'.
      apply generate_cfuns_reflects_match_names in Hin'.
      rewrite <- map_map with (f := snd) in Hin; rewrite map_map with (g := snd) in Hin;
        simpl in Hin; rewrite <- map_map with (f := snd) in Hin; rewrite map_map in Hin.
      apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in Hin;
        rewrite map_map in Hin.
      match goal with
      | [ H: Forall _ _ |- _ ] =>
        rewrite Forall_forall in H; eapply H; solve [eauto]
      end.
    + rewrite Forall_forall; intros qn Hin Hin'.
      clear - Hin Hin' H0 Hunique3.
      induction ls; auto; simpl in *; inversion_clear H0; unique_app_destr_tac.
      repeat (rewrite map_app in *; rewrite concat_app in * ).
      rewrite in_app_iff in *.
      inversion_clear Hin as [Hin0 | Hin0]; inversion_clear Hin' as [Hin1 | Hin1]; auto.
      * rewrite <- map_map in Hin1; rewrite concat_map in Hin1; rewrite map_map in Hin1.
        eapply split_matches_into_replace_generate; eauto.
      * apply replace_matches_reflects_match_names in Hin0.
        rewrite <- map_map with (f := snd) (l := ls) in Hin1;
          rewrite <- flat_map_concat_map with (l := map snd ls) in Hin1;
          apply generate_cfuns_reflects_match_names_flat in Hin1;
          rewrite flat_map_concat_map in Hin1;
          rewrite map_map in Hin1.
        match goal with
        | [ H: Forall _ _ |- _ ] =>
          rewrite Forall_forall in H; eapply H; solve [eauto]
        end.
      * apply generate_cfuns_reflects_match_names in Hin1.
        rewrite <- map_map in Hin0; rewrite map_map with (g := snd) in Hin0; simpl in Hin0;
          rewrite <- map_map with (f := snd) in Hin0;
          rewrite map_map in Hin0;
          apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names _)) in Hin0;
          rewrite map_map in Hin0.
        match goal with
        | [ H: Forall _ _ |- _ ] =>
          rewrite Forall_forall in H; eapply H; solve [eauto]
        end.
  - repeat (rewrite map_app in *; rewrite concat_app in * ).
    rename H into Hunique.
    unique_app_destr_full_tac.
    apply uniqueness_app.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0; specialize (Hunique0 qn Hin); apply Hunique0.
      rewrite <- map_map.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique1; rewrite Forall_forall in Hunique1; specialize (Hunique1 qn Hin); apply Hunique1.
      rewrite <- map_map.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + clear - Hunique_f.
      rewrite Forall_forall; intros qn Hin Hnin.
      induction es; try solve [inversion Hin]; simpl in *.
      repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
      rewrite <- Forall_app_iff in Hunique_f; inversion_clear Hunique_f as [Hunique Hx].
      rewrite in_app_iff in Hin.
      rename Hin into Hin'; inversion_clear Hin' as [Hin | Hin]; auto.
      apply generate_cfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      rewrite Forall_forall in Hunique; specialize (Hunique qn Hin); apply Hunique.
      rewrite <- map_map.
      apply Hlem'; intros; apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    rewrite <- uniqueness_app_rewrite in H; inversion_clear H; inversion_clear H1.
    apply uniqueness_app; auto.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_cfuns_reflects_match_names in Hin.
    pose proof (fun qn e => generate_cfuns_reflects_match_names tn e qn) as Hlem.
    rewrite Forall_forall in H2; specialize (H2 qn Hin); apply H2; auto.
Qed.

(******************* finished till this point *************)


(********************************************************************)
(*** uniqueness of matches ***)
(********************************************************************)

Lemma new_match_names_unique : forall p tn,
  match_names_unique
    (map (fun x : Name * expr => (fst x, replace_matches_by_cfun_calls tn (snd x)))
       (program_fun_bods p))
    (map
       (fun x : QName * list (ScopedName * expr) =>
        (fst x,
        map
          (fun y : ScopedName * expr => (fst y, replace_matches_by_cfun_calls tn (snd y)))
          (snd x))) (program_cfun_bods_g p)
          ++ new_cfun_bods_l p tn)
    (map
       (fun x : QName * list (ScopedName * expr) =>
        (fst x,
        map
          (fun y : ScopedName * expr => (fst y, replace_matches_by_cfun_calls tn (snd y)))
          (snd x))) (program_gfun_bods_g p)
          ++ []).
Proof.
  intros p tn.
  unfold match_names_unique.
  rewrite app_nil_r.
  repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
  reassoc_list_to_right.
  match goal with
  | [  |- unique (?l1 ++ ?l2 ++ ?l3 ++ ?l4) ] =>
    reassoc (l1 ++ l2 ++ l3 ++ l4) ((l1 ++ l2) ++ l3 ++ l4);
      apply unique_app_switch;
      reassoc ((l1 ++ l2) ++ l4 ++ l3) ((l1 ++ l2 ++ l4) ++ l3)
  end.

  apply uniqueness_app.
  - apply uniqueness_app_3way; repeat rewrite map_compose; simpl; try rewrite concat_map; repeat rewrite map_compose;

    (let unique_xfun_tac :=
        match goal with
        | [ |- unique (concat (concat (map (fun a => map ?f (map (fun y => (fst y, ?rep ?t (snd y))) (snd a)))
                                          ?bods))) ] =>
          apply uniqueness_sublist with (tot := (concat (concat (map (fun a => map (fun a0 => collect_match_names (snd a0))
                                                                                (snd a))
                                                                     bods))))
        end;
          [> apply sublist_concat';
           match goal with
           | [  |- Forall2 _ _ (concat (map _ ?bods)) ] =>
             induction bods
           end; try apply Forall2_nil;
           simpl; apply Forall2_app; try assumption;
           rewrite map_map; clear;
           match goal with
           | [  |- Forall2 _ (map _ ?ls) (map _ ?ls) ] =>
             induction ls
           end; try apply Forall2_nil;
           simpl; apply Forall2_cons; try assumption;
           apply replace_matches_by_cfun_calls_no_new_matches
          | pose proof (program_match_names_unique p);
            apply match_names_unique_global_sublist in H;
            unfold match_names_unique in H;
            repeat rewrite map_app in H;
            repeat rewrite concat_app in H;
            repeat rewrite map_map in H;
            rewrite <- map_map; rewrite <- concat_map;
            (idtac + rewrite app_assoc in H); unique_sublist_tac
          ]

    in
      let forall_fun_tac :=

          match goal with
          | [  |- Forall _ ?ls ] =>
            match ls with
            | concat (map _ ?bods) =>
              assert (H_sub: sublist ls (concat (map collect_match_names (map snd bods))))
            end
          end;
            [> apply sublist_concat';
             induction (program_fun_bods p); try apply Forall2_nil;
             simpl; apply Forall2_cons; try assumption;
             apply replace_matches_by_cfun_calls_no_new_matches
            |];
            match goal with
            | [ H: sublist ?ss ?ts' |- Forall _ ?ss ] =>
              apply Forall_sublist with (ts := ts'); try assumption
            end; clear H_sub;
              match goal with
              | [  |- Forall ?P _ ] =>
                match P with
                | context [concat (map _ ?l)] =>
                  assert (H: forall x, ~ In x (concat (concat (map (fun a => (map (fun a0 => collect_match_names (snd a0))
                                                                          (snd a)))
                                                              l)))
                                  -> P x)
                end
              end;
              [> clear; intros x H H_in;
               match goal with
               | [ H: ~ In ?x ?ts, H_in: In ?x ?ss |- _ ] =>
                 assert (H_in': In x ts);
                 [> apply In_sublist with (sub := ss); [> | assumption]
                 | apply H; assumption ]
               end;
               clear; apply sublist_concat';
               match goal with
               | [  |- Forall2 _ _ (concat (map _ ?bods)) ] =>
                 induction bods
               end; try apply Forall2_nil; apply Forall2_app; try assumption;
               clear; match goal with
                      | [  |- Forall2 _ _ (map _ ?x) ] =>
                        induction x; try apply Forall2_nil; apply Forall2_cons; try assumption
                      end;
               apply replace_matches_by_cfun_calls_no_new_matches
              |];

              simpl in H;
              match goal with
              | [ H: forall x, ~ In x ?ss -> ~ In x ?ts |- Forall _ ?ls ] =>
                apply Forall_impl with (P := fun x => ~ In x ss); try assumption
              end; clear H;
                pose proof (program_match_names_unique p) as H;
              apply match_names_unique_global_sublist in H;
              unfold match_names_unique in H;
                repeat rewrite map_app in H; repeat rewrite map_map in H; repeat rewrite concat_app in H;
                  rewrite map_map;
                  match goal with
                  | [ H: unique (?x ++ _ ++ ?y) |- _ ] =>
                    assert (H': unique (x ++ y)); [> unique_sublist_tac |]; clear H; rename H' into H
                  end +
                  match goal with
                  | [ H: unique (?x ++ ?y ++ _) |- _ ] =>
                    assert (H': unique (x ++ y)); [> unique_sublist_tac |]; clear H; rename H' into H
                  end;
                  apply uniqueness_app_not_in;
                  match goal with
                  | [ H: unique (?l ++ ?r) |- unique (?l ++ ?r') ] =>
                    assert (E: r' = r);
                      [> | rewrite E; assumption]
                  end;
                  rewrite concat_map; rewrite map_map; reflexivity

    in
      [> | unique_xfun_tac | unique_xfun_tac | forall_fun_tac | forall_fun_tac | ]).


    + apply uniqueness_sublist with (tot := concat (map (fun a => collect_match_names (snd a)) (program_fun_bods p))).
      * apply sublist_concat.
        induction (program_fun_bods p); try apply Forall_nil.
        apply Forall_cons; try assumption.
        apply replace_matches_by_cfun_calls_no_new_matches.
      * pose proof (program_match_names_unique p) as H_unique.
        unfold match_names_unique in H_unique.
        match goal with
        | [ H: unique ?t |- unique ?s ] =>
          apply uniqueness_sublist with (tot := t)
        end; try assumption.
        repeat rewrite map_app.
        repeat rewrite concat_app.
        rewrite map_map. apply sublist_app_embed_l.
    + pose proof (program_match_names_unique p) as H;
        apply match_names_unique_global_sublist in H;
        unfold match_names_unique in H.
      repeat rewrite map_app in H. repeat rewrite concat_app in H.
      match goal with
      | [ H: unique ?bs |- Forall _ ?ls ] =>
        match ls with
        | context [?bods] =>
          match bods with
          | (?p_bods p) =>
            match bs with
            | context [concat ?bs'] =>
              match bs' with
              | context [p_bods p] =>
                clear H; assert (H_sub: sublist ls (concat bs'));
                  [> apply sublist_concat';
                   induction (p_bods p); try apply Forall2_nil;
                   simpl; repeat rewrite map_app; apply Forall2_app; try assumption; unfold cfun_bod;
                   match goal with
                   | [  |- Forall2 _ _ (map _ (map _ ?x)) ] =>
                     induction x; try apply Forall2_nil
                   end; simpl; apply Forall2_cons; try assumption;
                   apply replace_matches_by_cfun_calls_no_new_matches
                  |]
              end
            end
          end
        end
      end.
      match goal with
      | [ H: sublist ?ss ?ts' |- Forall _ ?ss ] =>
        apply Forall_sublist with (ts := ts'); try assumption
      end; clear H_sub.
      match goal with
      | [  |- Forall ?P _ ] =>
        match P with
        | context [concat (map _ ?l)] =>
          assert (H: forall x, ~ In x (concat (concat (map (fun a => (map (fun a0 => collect_match_names (snd a0))
                                                                  (snd a)))
                                                      l)))
                          -> P x)
        end
      end;
        [> clear; intros x H H_in;
         match goal with
         | [ H: ~ In ?x ?ts, H_in: In ?x ?ss |- _ ] =>
           assert (H_in': In x ts);
           [> apply In_sublist with (sub := ss); [> | assumption]
           | apply H; assumption ]
         end;
         clear; apply sublist_concat';
         match goal with
         | [  |- Forall2 _ _ (concat (map _ ?bods)) ] =>
           induction bods
         end; try apply Forall2_nil; apply Forall2_app; try assumption;
         clear; match goal with
                | [  |- Forall2 _ _ (map _ ?x) ] =>
                  induction x; try apply Forall2_nil; apply Forall2_cons; try assumption
                end;
         simpl; apply replace_matches_by_cfun_calls_no_new_matches
        |].

      simpl in H.
      match goal with
      | [ H: forall x, ~ In x ?ss -> ~ In x ?ts |- Forall _ ?ls ] =>
        apply Forall_impl with (P := fun x => ~ In x ss); try assumption
      end; clear H.
      pose proof (program_match_names_unique p) as H;
        apply match_names_unique_global_sublist in H;
        unfold match_names_unique in H.
      repeat rewrite map_app in H; repeat rewrite map_map in H; repeat rewrite concat_app in H;
        rewrite map_map.
      match goal with
      | [ H: unique (_ ++ ?x ++ ?y) |- _ ] =>
        assert (H': unique (x ++ y)); [> unique_sublist_tac |]; clear H; rename H' into H
      end;
        apply uniqueness_app_not_in;
        match goal with
        | [ H: unique (?l ++ ?r) |- unique (?l ++ ?r') ] =>
          assert (E: r' = r);
            [> | rewrite E; assumption]
        end;
        rewrite concat_map; rewrite map_map; reflexivity.

 - pose proof (program_match_names_unique p) as H.
   apply match_names_unique_global_sublist in H.
   unfold match_names_unique in H.
   unfold new_cfun_bods_l.
   repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
   repeat rewrite map_map in *.
   repeat unique_app_destr_tac.
   apply uniqueness_app_3way.
   + clear - H0.
     induction (program_fun_bods p); auto; simpl in *.
     repeat (rewrite map_app; rewrite concat_app).
     unique_app_destr_tac.
     apply uniqueness_app; auto.
     * apply generate_cfuns_unique_matches_propagates; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_cfuns_reflects_match_names in Hin.
       rewrite Forall_forall in H0_f; eapply H0_f; eauto.
       rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
       clear - Hnin; unfold fun_bod in *.
       induction (@map (Name * expr) expr snd f); auto.
       simpl in *. repeat (rewrite map_app in *; rewrite concat_app in * ).
       rewrite in_app_iff in *.
       inversion Hnin; auto.
   + clear - H3.
     induction (program_gfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; repeat rewrite flat_map_app in *; repeat rewrite concat_app in * ).
     unique_app_destr_tac.
     apply uniqueness_app; auto.
     * clear - H0. unfold cfun_bod_named in *. unfold cfun_bod in *.
       destruct a; simpl in *.
       induction g; auto; simpl in *.
       repeat (rewrite map_app; rewrite concat_app).
       unique_app_destr_tac.
       apply uniqueness_app; auto.
       -- apply generate_cfuns_unique_matches_propagates; auto.
       -- rewrite Forall_forall; intros qn Hin Hnin.
          rewrite Forall_forall in H0_f; eapply H0_f.
          ++ eapply (generate_cfuns_reflects_match_names tn _ qn); auto.
          ++ rewrite <- map_map.
             eapply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
             clear - Hnin.
             induction (map snd g); auto.
             simpl in *.
             repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
             rewrite in_app_iff; rewrite in_app_iff in Hnin.
             inversion_clear Hnin; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_cfuns_reflects_match_names_flat in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite map_map in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite Forall_forall in H3_f; eapply H3_f; eauto.
       rewrite <- map_map; rewrite <- flat_map_concat_map.
       apply generate_cfuns_reflects_match_names_flat in Hin; auto.
   + clear - H2.
     induction (program_cfun_bods_g p) as [| a g]; auto; simpl in *.
     repeat (repeat rewrite map_app in *; repeat rewrite flat_map_app in *; repeat rewrite concat_app in * ).
     unique_app_destr_tac.
     apply uniqueness_app; auto.
     * clear - H0. unfold cfun_bod_named in *. unfold cfun_bod in *.
       induction (@snd QName _ a); auto; simpl in *.
       repeat (rewrite map_app; rewrite concat_app).
       unique_app_destr_tac.
       apply uniqueness_app; auto.
       -- apply generate_cfuns_unique_matches_propagates; auto.
       -- rewrite Forall_forall; intros qn Hin Hnin.
          rewrite Forall_forall in H0_f; eapply H0_f.
          ++ eapply (generate_cfuns_reflects_match_names tn _ qn); auto.
          ++ rewrite <- map_map.
             eapply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
             clear - Hnin.
             induction (map snd l); auto.
             simpl in *.
             repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
             rewrite in_app_iff; rewrite in_app_iff in Hnin.
             inversion_clear Hnin; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_cfuns_reflects_match_names_flat in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite map_map in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite Forall_forall in H2_f; eapply H2_f; eauto.
       rewrite <- map_map; rewrite <- flat_map_concat_map.
       apply generate_cfuns_reflects_match_names_flat in Hin; auto.
   + clear - H_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H_f.
     * clear H_f Hnin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
       unfold fun_bod in *.
       induction (@map _ expr snd (program_fun_bods p)); eauto; simpl in *.
       repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
       rewrite in_app_iff in *.
       inversion_clear Hin; auto.
     * rewrite in_app_iff; right. unfold cfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_cfuns_reflects_match_names_flat tn); auto. repeat rewrite flat_map_concat_map in *; auto.
   + clear - H_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H_f.
     * clear H_f Hnin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
       unfold fun_bod in *.
       induction (@map _ expr snd (program_fun_bods p)); eauto; simpl in *.
       repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
       rewrite in_app_iff in *.
       inversion_clear Hin; auto.
     * rewrite in_app_iff; left. unfold cfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_cfuns_reflects_match_names_flat tn); auto. repeat rewrite flat_map_concat_map in *; auto.
   + clear - H1_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H1_f.
     * clear H1_f Hin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_match_names tn e qn)).
       rewrite <- flat_map_concat_map with (l := program_cfun_bods_g p).
       unfold cfun_bod_named in *; unfold cfun_bod in *.
       induction (@map _ expr snd (flat_map snd (program_cfun_bods_g p))); eauto; simpl in *.
       repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin); eauto.
       rewrite in_app_iff in *.
       inversion_clear Hnin; auto.
     * unfold cfun_bod_named in *; unfold cfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_cfuns_reflects_match_names_flat tn).
       repeat rewrite flat_map_concat_map in *; auto.
 - unfold new_cfun_bods_l. repeat rewrite map_map; simpl.
   repeat rewrite concat_map; repeat (rewrite map_map; simpl).
   rewrite Forall_forall; intros qn Hin Hnin.
   repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
   repeat rewrite in_app_iff in *.
   rename Hin into Hin'; rename Hnin into Hnin';
     inversion_clear Hin' as [Hin|[Hin|Hin]]; inversion_clear Hnin' as [Hnin|[Hnin|Hnin]].
   + rewrite <- map_map with (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) (f := snd) in Hin.
     assert (unique (flat_map collect_match_names (map snd (program_fun_bods p)))).
     { pose proof (program_match_names_unique p); unfold match_names_unique in *.
       rewrite flat_map_concat_map.
       repeat rewrite map_app in H; repeat rewrite concat_app in H.
       unique_sublist_tac.
     }
     unfold fun_bod in *.
     induction (@map _ expr snd (program_fun_bods p)); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion_clear Hin; inversion_clear Hnin; auto;
     unique_app_destr_tac; auto.
     * eapply split_matches_into_replace_generate; eauto.
       split; eauto. clear - H1.
       induction (generate_cfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_matches_reflects_match_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_cfuns_reflects_match_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_cfuns_reflects_match_names tn).
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite map_map in H1; auto.
   + pose proof (program_match_names_unique p); unfold match_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := fs
       in assert (unique (l ++ ggs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map with (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) in Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hnin. rewrite <- flat_map_concat_map. apply (generate_cfuns_reflects_match_names_flat tn).
     unfold gfun_bod_named in *. unfold gfun_bod in *.
     rewrite flat_map_concat_map with (f := snd) in Hnin.
     induction (map snd (concat (@map _ (list (ScopedName * expr)) snd (program_gfun_bods_g p)))); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *; inversion_clear Hnin; auto.
     left. repeat rewrite map_map in H; rewrite concat_map; rewrite map_map; auto.
   + pose proof (program_match_names_unique p); unfold match_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := fs
       in assert (unique (l ++ cgs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map with (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) in Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hnin. rewrite <- flat_map_concat_map. apply (generate_cfuns_reflects_match_names_flat tn).
     unfold cfun_bod_named in *. unfold cfun_bod in *.
     rewrite flat_map_concat_map with (f := snd) in Hnin.
     induction (map snd (concat (@map _ (list (ScopedName * expr)) snd (program_cfun_bods_g p)))); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *; inversion_clear Hnin; auto.
     left. repeat rewrite map_map in H; rewrite concat_map; rewrite map_map; auto.
   + pose proof (program_match_names_unique p); unfold match_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := fs
       in assert (unique (l ++ cgs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_cfuns_reflects_match_names_flat tn) in Hnin.
     rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)).
     induction (program_cfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion Hin; auto; left.
     rewrite map_map in H; simpl in H.
     rewrite <- map_map with (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) (f := snd) in H; auto.
   + pose proof (program_match_names_unique p); unfold match_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := cgs
       in assert (unique (l ++ ggs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map in Hin. rewrite <- concat_map in Hin. rewrite <- map_map in Hin.
     rewrite concat_map in Hin. rewrite <- map_map with (f := snd) in Hin.
     rewrite map_map in Hin.
     rewrite (map_ext _ _ (map_map _ _)) in Hin.
     simpl in Hin. rewrite (map_ext _ _ (fun x => eq_sym (map_map _ _ x))) in Hin.
     rewrite <- map_map with (f := map snd) in Hin.
     rewrite <- concat_map in Hin. rewrite map_map in Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hin.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_cfuns_reflects_match_names_flat tn) in Hnin.
     rewrite <- concat_map in Hin; repeat rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); clear H0; auto.
   + rewrite <- map_map in Hin. rewrite <- concat_map in Hin.
     rewrite <- map_map with (f := snd) (g := map (fun y => (fst y, replace_matches_by_cfun_calls tn (snd y)))) in Hin.
     rewrite <- concat_map in Hin; repeat rewrite <- flat_map_concat_map in Hin; rewrite flat_map_concat_map in Hin.
     rewrite map_map in Hin; simpl in Hin. rewrite <- map_map with (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) (f := snd) in Hin.
     assert (unique (flat_map collect_match_names (map snd (flat_map snd (program_cfun_bods_g p))))).
     { pose proof (program_match_names_unique p); unfold match_names_unique in *.
       rewrite flat_map_concat_map.
       repeat (repeat rewrite map_app in H; repeat rewrite concat_app in H).
       rewrite flat_map_concat_map. unique_sublist_tac.
     }
     unfold cfun_bod in *.
     induction (@map _ expr snd (flat_map snd (program_cfun_bods_g p))); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion_clear Hin; inversion_clear Hnin; auto;
     unique_app_destr_tac; auto.
     * eapply split_matches_into_replace_generate; eauto.
       split; eauto. clear - H1.
       induction (generate_cfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_matches_reflects_match_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_cfuns_reflects_match_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_cfuns_reflects_match_names tn).
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite map_map in H1; auto.
   + pose proof (program_match_names_unique p); unfold match_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := fs
       in assert (unique (l ++ ggs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_cfuns_reflects_match_names_flat tn) in Hnin.
     rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)).
     induction (program_gfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion Hin; auto; left.
     rewrite map_map in H; simpl in H.
     rewrite <- map_map with (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) (f := snd) in H; auto.
   + rewrite <- map_map in Hin. rewrite <- concat_map in Hin.
     rewrite <- map_map with (f := snd) (g := map (fun y => (fst y, replace_matches_by_cfun_calls tn (snd y)))) in Hin.
     rewrite <- concat_map in Hin; repeat rewrite <- flat_map_concat_map in Hin; rewrite flat_map_concat_map in Hin.
     rewrite map_map in Hin; simpl in Hin. rewrite <- map_map with (g := fun x => collect_match_names (replace_matches_by_cfun_calls tn x)) (f := snd) in Hin.
     assert (unique (flat_map collect_match_names (map snd (flat_map snd (program_gfun_bods_g p))))).
     { pose proof (program_match_names_unique p); unfold match_names_unique in *.
       rewrite flat_map_concat_map.
       repeat (repeat rewrite map_app in H; repeat rewrite concat_app in H).
       rewrite flat_map_concat_map. unique_sublist_tac.
     }
     unfold gfun_bod in *.
     induction (@map _ expr snd (flat_map snd (program_gfun_bods_g p))); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion_clear Hin; inversion_clear Hnin; auto;
     unique_app_destr_tac; auto.
     * eapply split_matches_into_replace_generate; eauto.
       split; eauto. clear - H1.
       induction (generate_cfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_matches_reflects_match_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_cfuns_reflects_match_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_cfuns_reflects_match_names tn).
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite map_map in H1; auto.
   + pose proof (program_match_names_unique p); unfold match_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := cgs
       in assert (unique (l ++ ggs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map in Hin. rewrite <- concat_map in Hin. rewrite <- map_map in Hin.
     rewrite concat_map in Hin. rewrite <- map_map with (f := snd) in Hin.
     rewrite map_map in Hin.
     rewrite (map_ext _ _ (map_map _ _)) in Hin.
     simpl in Hin. rewrite (map_ext _ _ (fun x => eq_sym (map_map _ _ x))) in Hin.
     rewrite <- map_map with (f := map snd) in Hin.
     rewrite <- concat_map in Hin. rewrite map_map in Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_match_names tn)) in Hin.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_cfuns_reflects_match_names_flat tn) in Hnin.
     rewrite <- concat_map in Hin; repeat rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); clear H0; auto.
Qed.

(********************************************************************)
(*** lemmas for uniqueness of comatches ***)
(********************************************************************)

Lemma replace_matches_by_cfun_calls_no_new_comatches: forall (tn : TypeName) (e : expr),
    sublist (collect_comatch_names (replace_matches_by_cfun_calls tn e))
            (collect_comatch_names e).
Proof.
  intros tn e.
  induction e using expr_strong_ind; simpl; repeat rewrite map_map;
    try solve [ try (apply sublist_app; try assumption);
                apply sublist_concat; assumption]; simpl.
  - apply sublist_nil.
  - destruct n as [tn' n']. simpl.
    name_destruct_tac; simpl.
    + rewrite map_map.
      apply sublist_app; try assumption.
      match goal with
      | [ |- sublist (concat (map _ ?l)) (concat (map _ ?l ++ map _ _)) ] =>
        induction l;
          [> try apply sublist_nil
          | apply sublist_app; try (inversion H0; assumption);
            IH_tac Forall_tail_tac
          ]
      end.
    + repeat rewrite map_map. simpl. repeat rewrite concat_app.
      apply sublist_app; [> assumption | apply sublist_app; apply sublist_concat];
        match goal with
        | [ H: Forall _ (map _ ?l) |- Forall _ ?l ] =>
            induction l;
            [> apply Forall_nil
            | apply Forall_cons;
              [> simpl; inversion H; assumption
              | IH_tac Forall_tail_tac
              ]
            ]
        end.
  - apply sublist_cons.
    repeat rewrite concat_app.
    apply sublist_app;
    apply sublist_concat; try assumption;
    match goal with
    | [ H: Forall _ (map _ ?l) |- Forall _ ?l ] =>
      induction l;
        [> apply Forall_nil
        | apply Forall_cons;
          [> simpl; inversion H; assumption
          | IH_tac Forall_tail_tac
          ]
        ]
    end.
Qed.

Lemma replace_matches_reflects_comatch_names:
  forall (tn : TypeName) (qn : QName) (e : expr),
    In qn (collect_comatch_names (replace_matches_by_cfun_calls tn e)) ->
    In qn (collect_comatch_names e).
Proof.
  intros tn qn e Hin.
  induction e using expr_strong_ind; simpl in *; auto;
    let rec listtac :=
        match goal with
        | [ Hf: Forall _ ?lst, Hin: In _ _ |- _ ] =>
          induction lst;
            auto;
            simpl in *;
                       inversion_clear Hf;
                       rewrite in_app_iff in Hin; rewrite in_app_iff;
                         inversion_clear Hin; [> left | right ]; auto
  end
    in let rec app_tac :=
           match goal with
           | [ Hin: In _ _ |- _ ] =>
             repeat (rewrite map_app in Hin; rewrite concat_app in Hin);
               repeat rewrite in_app_iff in Hin;
                                              repeat rewrite in_app_iff
  end
    in try name_destruct_tac; simpl in *; try rewrite concat_app; try rewrite concat_app in Hin;
    try app_tac;
    try listtac;
    try match goal with
        | [ Hin: _ \/ _ \/ _ |- _ ] =>
          inversion_clear Hin; [> left; solve [auto] |]
        end;
    try solve [match goal with
               | [ Hin: _ \/ _ |- _ ] =>
                 inversion Hin; [> left | right ]; auto; try listtac
               end].
  - inversion_clear Hin; auto; right; left.
    clear H IHe.
    induction es; auto; simpl in *; inversion_clear H0.
    rewrite in_app_iff in H1; rewrite in_app_iff.
    inversion H1; [> left | right ]; auto.
  - inversion_clear H1.
    + right; left; induction es; auto; simpl in *.
      inversion H0; rewrite in_app_iff; rewrite in_app_iff in H2; inversion H2; auto.
    + right; right; induction ls; auto; simpl in *.
      inversion H; rewrite in_app_iff; rewrite in_app_iff in H2; inversion H2; auto.
  - inversion_clear Hin as [E | Hin']; auto.
    rewrite in_app_iff in *; right.
    inversion_clear Hin'; [> left; clear H | right; clear H0].
    + induction es; auto; simpl in *; try contradiction.
      rewrite in_app_iff in H1; rewrite in_app_iff.
      inversion_clear H0.
      inversion_clear H1; [> left | right ]; auto.
    + induction ls; auto; simpl in *.
      rewrite in_app_iff in H1; rewrite in_app_iff.
      inversion_clear H.
      inversion_clear H1; [> left | right ]; auto.
Qed.

Ltac liftmatch_generate_cfuns_reflects_comatch_names_list_tac :=
  match goal with
  | [ Hin: In _ _, Hf: Forall _ ?lst |- _ ] =>
    let lst'' := match lst with
                 | context [?lst'] => lst'
                 end
    in clear - Hin Hf;
       let lst'' := match lst with
                    | context [?lst'] =>
                      match type of Hin with
                      | context [lst'] =>
                        match type of lst' with
                        | list _ => lst'
                        end
                      end
                    end
       in clear - Hin Hf;
          induction lst''; simpl in *; auto;
          inversion_clear Hf;
          liftmatch_destruct_hin_app_tac;
          rewrite in_app_iff;
          inversion Hin; [> left | right]; auto
  end.

Lemma generate_cfuns_reflects_comatch_names: forall (tn : TypeName) (e : expr) (qn : QName),
    In qn (concat
             (map (fun x : ScopedName * expr => collect_comatch_names (snd x))
                  (concat
                     (map (fun x : cfun_sig * cfun_bod_named => snd (snd x))
                          (generate_cfuns_from_expr tn e))))) ->
    In qn (collect_comatch_names e).
Proof.
  intros tn e qn H.
  induction e using expr_strong_ind; simpl in *; auto;
    try liftmatch_destruct_hin_app_tac;
    try (rewrite in_app_iff;
    match goal with
      | [ Hin: _ \/ _ |- _ ] =>
        inversion Hin; [> left; solve [auto] | right; auto ]
      end);
    try solve [liftmatch_generate_cfuns_reflects_comatch_names_list_tac].

  - rewrite concat_app; repeat rewrite in_app_iff.
    inversion H as [Hin | [Hin | [Hin |Hin]]];
    [> | left | right; left | right; right]; auto; [> | liftmatch_generate_cfuns_reflects_comatch_names_list_tac ..].
    name_destruct_tac; try solve [inversion Hin]; simpl in Hin; rewrite app_nil_r in Hin.
    rewrite map_map in Hin; simpl in Hin; right.
    rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) (f := snd) in Hin.
    apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hin.
    rewrite map_map in Hin; auto.
  - right; inversion_clear H as [Hin | Hin];
      rewrite concat_app; rewrite in_app_iff; (left + right);
      liftmatch_generate_cfuns_reflects_comatch_names_list_tac.
Qed.

Lemma generate_cfuns_reflects_comatch_names_flat: forall (tn : TypeName) (g : list expr) (qn : QName),
    In qn
       (concat
          (map (fun x : ScopedName * expr => collect_comatch_names (snd x))
               (concat
                  (map (fun x : cfun_sig * cfun_bod_named => snd (snd x))
                       (flat_map (generate_cfuns_from_expr tn) g))))) ->
    In qn (flat_map collect_comatch_names g).
Proof.
  intros tn g qn H.
  induction g; auto; simpl in *.
  repeat (rewrite map_app in H; rewrite concat_app in H).
  rewrite in_app_iff in *.
  inversion H; auto; left.
  apply (generate_cfuns_reflects_comatch_names tn); auto.
Qed.

Section split_comatches_into_replace_generate_sec.

Lemma split_comatches_into_replace_generate: forall (tn : TypeName) (e : expr) (qn : QName),
    unique (collect_comatch_names e) ->
    ~ (In qn (collect_comatch_names (replace_matches_by_cfun_calls tn e)) /\
       In qn (concat (map collect_comatch_names (concat (map (fun x => (map snd (snd (snd x)))) (generate_cfuns_from_expr tn e)))))).
Proof.
  intros tn e qn Hunique H.
  inversion_clear H as [Hin_rep Hin_gen].
  induction e using expr_strong_ind; simpl in *; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_matches_reflects_comatch_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
      assert (In qn (concat (map collect_comatch_names ls)));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      apply H3. clear - H2.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in H2; repeat rewrite concat_app in H2).
      rewrite in_app_iff; rewrite in_app_iff in H2.
      inversion H2; [> left | right]; auto.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + assert (In qn (concat (map collect_comatch_names ls))); [> | clear H].
      { clear - H.
        apply (in_map_concat _ _ qn ls (replace_matches_reflects_comatch_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_comatch_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_cfuns_reflects_comatch_names tn).
        induction (generate_cfuns_from_expr tn a); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion H2; [> left | right ]; auto.
        rewrite <- map_map; auto.
      }
  - unique_app_destr_tac.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    rewrite in_app_iff in *.
    repeat match goal with
           | [ H: _ \/ _ |- _ ] =>
             let H1 := fresh H
             in inversion_clear H as [H1 | H1]
           end; auto;
      try solve [
            (rewrite map_map in Hin_rep0;
             apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hin_rep0)
            || apply (replace_matches_reflects_comatch_names tn) in Hin_rep0;
            rewrite <- map_map with (g := map snd) in Hin_gen0;
            rewrite <- concat_map in Hin_gen0;
            rewrite map_map in Hin_gen0;
            (rewrite <- flat_map_concat_map with (l := ls) in Hin_gen0;
             apply (generate_cfuns_reflects_comatch_names_flat tn) in Hin_gen0;
             rewrite flat_map_concat_map in Hin_gen0)
            || apply generate_cfuns_reflects_comatch_names in Hin_gen0;
            rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto
          ].

    + clear IHe Hunique0 Hunique_f.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in *; rewrite concat_app in * ).
      rewrite in_app_iff in *.
      inversion_clear H.
      unique_app_destr_tac; rewrite Forall_forall in Hunique1_f.
      repeat match goal with
             | [ H: _ \/ _ |- _ ] =>
               let H1 := fresh H
               in inversion_clear H as [H1 | H1]
             end; auto.
      * eapply Hunique1_f; eauto;
          try (eapply replace_matches_reflects_comatch_names; eauto).
        rewrite <- flat_map_concat_map;
          apply (generate_cfuns_reflects_comatch_names_flat tn);
          rewrite flat_map_concat_map.
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * eapply Hunique1_f; eauto;
          try (apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)); rewrite map_map in Hin_rep1; eauto).
        apply (generate_cfuns_reflects_comatch_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_matches_reflects_comatch_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
      assert (In qn (concat (map collect_comatch_names ls)));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      apply H3. clear - H2.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in H2; repeat rewrite concat_app in H2).
      rewrite in_app_iff; rewrite in_app_iff in H2.
      inversion H2; [> left | right]; auto.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + assert (In qn (concat (map collect_comatch_names ls))); [> | clear H].
      { clear - H.
        apply (in_map_concat _ _ qn ls (replace_matches_reflects_comatch_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_comatch_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_cfuns_reflects_comatch_names tn).
        induction (generate_cfuns_from_expr tn a); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion H2; [> left | right ]; auto.
        rewrite <- map_map; auto.
      }
  - unique_app_destr_tac.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    rewrite in_app_iff in *.
    repeat match goal with
           | [ H: _ \/ _ |- _ ] =>
             let H1 := fresh H
             in inversion_clear H as [H1 | H1]
           end; auto;
      try solve [
            (rewrite map_map in Hin_rep0;
             apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hin_rep0)
            || apply (replace_matches_reflects_comatch_names tn) in Hin_rep0;
            rewrite <- map_map with (g := map snd) in Hin_gen0;
            rewrite <- concat_map in Hin_gen0;
            rewrite map_map in Hin_gen0;
            (rewrite <- flat_map_concat_map with (l := ls) in Hin_gen0;
             apply (generate_cfuns_reflects_comatch_names_flat tn) in Hin_gen0;
             rewrite flat_map_concat_map in Hin_gen0)
            || apply generate_cfuns_reflects_comatch_names in Hin_gen0;
            rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto
          ].

    + clear IHe Hunique0 Hunique_f.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in *; rewrite concat_app in * ).
      rewrite in_app_iff in *.
      inversion_clear H.
      unique_app_destr_tac; rewrite Forall_forall in Hunique1_f.
      repeat match goal with
             | [ H: _ \/ _ |- _ ] =>
               let H1 := fresh H
               in inversion_clear H as [H1 | H1]
             end; auto.
      * eapply Hunique1_f; eauto;
          try (eapply replace_matches_reflects_comatch_names; eauto).
        rewrite <- flat_map_concat_map;
          apply (generate_cfuns_reflects_comatch_names_flat tn);
          rewrite flat_map_concat_map.
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * eapply Hunique1_f; eauto;
          try (apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)); rewrite map_map in Hin_rep1; eauto).
        apply (generate_cfuns_reflects_comatch_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_matches_reflects_comatch_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
      assert (In qn (concat (map collect_comatch_names ls)));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      apply H3. clear - H2.
      induction ls; auto; simpl in *.
      repeat (rewrite map_app in H2; repeat rewrite concat_app in H2).
      rewrite in_app_iff; rewrite in_app_iff in H2.
      inversion H2; [> left | right]; auto.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + assert (In qn (concat (map collect_comatch_names ls))); [> | clear H].
      { clear - H.
        apply (in_map_concat _ _ qn ls (replace_matches_reflects_comatch_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_comatch_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_cfuns_reflects_comatch_names tn).
        induction (generate_cfuns_from_expr tn a); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion H2; [> left | right ]; auto.
        rewrite <- map_map; auto.
      }

  - repeat (rewrite map_app in *; rewrite concat_app in * ).
    unique_app_destr_full_tac.
    name_destruct_tac; simpl in *;
      repeat (rewrite map_app in *; rewrite concat_app in * );
      repeat (rewrite in_app_iff in * ).
    + inversion_clear Hin_gen as [Hin_gen' | [Hin_gen' | [ Hin_gen' | Hin_gen' ]]];
        [> try (inversion_clear Hin_gen' as [Hin_gen | Hin_gen]; [> | easy]) | .. ];
        inversion_clear Hin_rep as [Hin_rep' | Hin_rep']; auto;
          try solve [
                repeat
                  match goal with
                  | [ Hr: In _ _ |- _ ] =>
                    (apply replace_matches_reflects_comatch_names in Hr)
                    || (try (rewrite (map_map _ snd) in Hr; simpl in Hr);
                       rewrite map_map in Hr;
                       match type of Hr with
                       | In _ ?l =>
                         (let rec go lst :=
                              match lst with
                              | _ (map ?f ?l) =>
                                match f with
                                | context [@fst ?lt ?rt] =>
                                  (let g := split_fun_by f (@fst lt rt)
                                   in rewrite <- (map_map (@fst lt rt) g) in Hr;
                                      apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hr);
                                  rewrite map_map in Hr
                         | context [@snd ?lt ?rt] =>
                           (let g := split_fun_by f (@snd lt rt)
                            in rewrite <- (map_map (@snd lt rt) g) in Hr;
                               apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hr);
                           rewrite map_map in Hr
                          end
                         | ?f ?l => go l
                          end
                           in go l)
                       end)
                  end;
                repeat
                  match goal with
                  | [ Hg: In _ _ |- _ ] =>
                    rewrite <- (map_map _ (map snd)) in Hg;
                    rewrite <- concat_map in Hg;
                    rewrite map_map in Hg;
                    (apply generate_cfuns_reflects_comatch_names in Hg)
                    || (match type of Hg with
                       | In _ ?l =>
                         (let rec go lst :=
                              match lst with
                              | _ (map ?f ?l) =>
                                match f with
                                | context [@fst ?lt ?rt] =>
                                  (let g := split_fun_by f (@fst lt rt)
                                   in rewrite <- (map_map (@fst lt rt) g) in Hg;
                                      rewrite <- (flat_map_concat_map g _) in Hg)
                                | context [@snd ?lt ?rt] =>
                                  (let g := split_fun_by f (@snd lt rt)
                                   in rewrite <- (map_map (@snd lt rt) g) in Hg;
                                      rewrite <- (flat_map_concat_map g _) in Hg)
                                end;
                                (apply generate_cfuns_reflects_comatch_names_flat in Hg);
                                (rewrite flat_map_concat_map in Hg);
                                rewrite map_map in Hg
                         | ?f ?l => go l
                          end
                           in go l)
                       end)
                  end;
                match goal with
                | [ Hf: Forall (fun x => ~ In x ?ls) ?ls',
                        H: In _ ?ls,
                           H': In _ ?ls' |- _ ] =>
                  rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
                end
              ].

      clear - Hin_gen' Hin_rep' Hunique2 H0.
      induction es; auto; simpl in *; inversion_clear H0.
      repeat (repeat rewrite map_app in *; rewrite concat_app in * );
        rewrite in_app_iff in *.
      unique_app_destr_tac.
      inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
      * rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          apply generate_cfuns_reflects_comatch_names in H0.
        rewrite <- map_map with (f := fst) in H2;
          rewrite map_map in H2;
          apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in H2;
          rewrite map_map in H2.
        rewrite Forall_forall in Hunique2_f; eapply Hunique2_f; eauto.
      * rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          rewrite <- map_map with (f := fst) in H0;
          rewrite <- flat_map_concat_map with (l := map fst es) in H0;
          apply generate_cfuns_reflects_comatch_names_flat in H0;
          rewrite flat_map_concat_map in H0; rewrite map_map in H0.
        apply replace_matches_reflects_comatch_names in H2.
        rewrite Forall_forall in Hunique2_f; eapply Hunique2_f; eauto.
    + rewrite concat_app in Hin_rep; rewrite in_app_iff in Hin_rep.
      inversion_clear Hin_gen as [Hin_gen' | [Hin_gen' | Hin_gen']];
        inversion_clear Hin_rep as [Hin_rep' | [Hin_rep' | Hin_rep']]; auto;
          try solve [
                repeat
                  match goal with
                  | [ Hr: In _ _ |- _ ] =>
                    (apply replace_matches_reflects_comatch_names in Hr)
                    || (try (rewrite (map_map _ snd) in Hr; simpl in Hr);
                       rewrite map_map in Hr; simpl in Hr;
                       match type of Hr with
                       | In _ ?l =>
                         (let rec go lst :=
                              match lst with
                              | _ (map ?f ?l) =>
                                match f with
                                | context [@fst ?lt ?rt] =>
                                  (let g := split_fun_by f (@fst lt rt)
                                   in rewrite <- (map_map (@fst lt rt) g) in Hr;
                                      apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hr);
                                  rewrite map_map in Hr
                         | context [@snd ?lt ?rt] =>
                           (let g := split_fun_by f (@snd lt rt)
                            in rewrite <- (map_map (@snd lt rt) g) in Hr;
                               apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hr);
                           rewrite map_map in Hr
                          end
                         | ?f ?l => go l
                          end
                           in go l)
                       end)
                  end;
                repeat
                  match goal with
                  | [ Hg: In _ _ |- _ ] =>
                    rewrite <- (map_map _ (map snd)) in Hg;
                    rewrite <- concat_map in Hg;
                    rewrite map_map in Hg;
                    (apply generate_cfuns_reflects_comatch_names in Hg)
                    || (match type of Hg with
                       | In _ ?l =>
                         (let rec go lst :=
                              match lst with
                              | _ (map ?f ?l) =>
                                match f with
                                | context [@fst ?lt ?rt] =>
                                  (let g := split_fun_by f (@fst lt rt)
                                   in rewrite <- (map_map (@fst lt rt) g) in Hg;
                                      rewrite <- (flat_map_concat_map g _) in Hg)
                                | context [@snd ?lt ?rt] =>
                                  (let g := split_fun_by f (@snd lt rt)
                                   in rewrite <- (map_map (@snd lt rt) g) in Hg;
                                      rewrite <- (flat_map_concat_map g _) in Hg)
                                end;
                                (apply generate_cfuns_reflects_comatch_names_flat in Hg);
                                (rewrite flat_map_concat_map in Hg);
                                rewrite map_map in Hg
                         | ?f ?l => go l
                          end
                           in go l)
                       end)
                  end;
                (match goal with
                 | [ Hf: Forall (fun x => ~ In x ?ls) ?ls',
                         H: In _ ?ls,
                            H': In _ ?ls' |- _ ] =>
                   rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
                 end
                 ||
                 match goal with
                 | [ Hn: ~ _ |- _ ] =>
                   subst; apply Hn; auto
                 end)
              ].
      * clear - Hin_gen' Hin_rep' Hunique2 H0.
        induction es; auto; simpl in *; inversion_clear H0.
        repeat (repeat rewrite map_app in *; rewrite concat_app in * );
          rewrite in_app_iff in *.
        unique_app_destr_tac.
        inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
        -- rewrite <- map_map with (g := map snd) in H0;
             rewrite <- concat_map in H0;
             rewrite map_map in H0;
             apply generate_cfuns_reflects_comatch_names in H0.
           rewrite map_map in H2; simpl in H2;
             rewrite <- map_map with (f := fst) (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) in H2;
             apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in H2;
             rewrite map_map in H2.
           rewrite Forall_forall in Hunique2_f; eapply Hunique2_f; eauto.
        -- rewrite <- map_map with (g := map snd) in H0;
             rewrite <- concat_map in H0;
             rewrite map_map in H0;
             rewrite <- map_map with (f := fst) in H0;
             rewrite <- flat_map_concat_map with (l := map fst es) in H0;
             apply generate_cfuns_reflects_comatch_names_flat in H0;
             rewrite flat_map_concat_map in H0; rewrite map_map in H0.
           apply replace_matches_reflects_comatch_names in H2.
           rewrite Forall_forall in Hunique2_f; eapply Hunique2_f; eauto.
      * clear - Hin_gen' Hin_rep' Hunique3 H.
        induction ls; auto; simpl in *; inversion_clear H.
        repeat (repeat rewrite map_app in *; rewrite concat_app in * );
          rewrite in_app_iff in *.
        unique_app_destr_tac.
        inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
        -- rewrite <- map_map with (g := map snd) in H;
             rewrite <- concat_map in H;
             rewrite map_map in H;
             apply generate_cfuns_reflects_comatch_names in H.
           rewrite map_map in H2; simpl in H2;
             rewrite <- map_map with (f := snd) (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) in H2;
             apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in H2;
             rewrite map_map in H2.
           rewrite Forall_forall in Hunique3_f; eapply Hunique3_f; eauto.
        -- rewrite <- map_map with (g := map snd) in H;
             rewrite <- concat_map in H;
             rewrite map_map in H;
             rewrite <- map_map with (f := snd) (l := ls) in H;
             rewrite <- flat_map_concat_map with (l := map snd ls) in H;
             apply generate_cfuns_reflects_comatch_names_flat in H;
             rewrite flat_map_concat_map in H; rewrite map_map in H.
           apply replace_matches_reflects_comatch_names in H2.
           rewrite Forall_forall in Hunique3_f; eapply Hunique3_f; eauto.
  - repeat (rewrite map_app in *; rewrite concat_app in * ).
    rewrite in_app_iff in *.
    rename Hunique into Htmp;
    inversion_clear Htmp as [|_x __x Hn_f Hunique].
    unique_app_destr_tac.
    inversion_clear Hin_rep as [Hin_rep' | [Hin_rep' | Hin_rep']];
      inversion_clear Hin_gen as [Hin_gen' | Hin_gen']; auto;
        try solve [
              repeat
                match goal with
                | [ Hr: In _ _ |- _ ] =>
                  (apply replace_matches_reflects_comatch_names in Hr)
                  || (try (rewrite (map_map _ snd) in Hr; simpl in Hr);
                     rewrite map_map in Hr; simpl in Hr;
                     match type of Hr with
                     | In _ ?l =>
                       (let rec go lst :=
                            match lst with
                            | _ (map ?f ?l) =>
                              match f with
                              | context [@fst ?lt ?rt] =>
                                (let g := split_fun_by f (@fst lt rt)
                                 in rewrite <- (map_map (@fst lt rt) g) in Hr;
                                    apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hr);
                                rewrite map_map in Hr
                       | context [@snd ?lt ?rt] =>
                         (let g := split_fun_by f (@snd lt rt)
                          in rewrite <- (map_map (@snd lt rt) g) in Hr;
                             apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hr);
                         rewrite map_map in Hr
                        end
                       | ?f ?l => go l
                        end
                         in go l)
                     end)
                end;
              repeat
                match goal with
                | [ Hg: In _ _ |- _ ] =>
                  rewrite <- (map_map _ (map snd)) in Hg;
                  rewrite <- concat_map in Hg;
                  rewrite map_map in Hg;
                  (apply generate_cfuns_reflects_comatch_names in Hg)
                  || (match type of Hg with
                     | In _ ?l =>
                       (let rec go lst :=
                            match lst with
                            | _ (map ?f ?l) =>
                              match f with
                              | context [@fst ?lt ?rt] =>
                                (let g := split_fun_by f (@fst lt rt)
                                 in rewrite <- (map_map (@fst lt rt) g) in Hg;
                                    rewrite <- (flat_map_concat_map g _) in Hg)
                              | context [@snd ?lt ?rt] =>
                                (let g := split_fun_by f (@snd lt rt)
                                 in rewrite <- (map_map (@snd lt rt) g) in Hg;
                                    rewrite <- (flat_map_concat_map g _) in Hg)
                              end;
                              (apply generate_cfuns_reflects_comatch_names_flat in Hg);
                              (rewrite flat_map_concat_map in Hg);
                              rewrite map_map in Hg
                       | ?f ?l => go l
                        end
                         in go l)
                     end)
                end;
              (match goal with
              | [ Hf: Forall (fun x => ~ In x ?ls) ?ls',
                      H: In _ ?ls,
                         H': In _ ?ls' |- _ ] =>
                rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
              end
              || match goal with
                | [ H: ~ In _ _ |- _ ] =>
                  subst; apply H; auto
                end)
            ].

    + clear - Hin_gen' Hin_rep' Hunique0 H0.
      induction es; auto; simpl in *; inversion_clear H0.
      repeat (repeat rewrite map_app in *; rewrite concat_app in * );
        rewrite in_app_iff in *.
      unique_app_destr_tac.
      inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
      * rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          apply generate_cfuns_reflects_comatch_names in H0.
        rewrite map_map in H2; simpl in H2;
          rewrite <- map_map with (f := fst) (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) in H2.
          apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in H2.
          rewrite map_map in H2.
        rewrite Forall_forall in Hunique0_f; eapply Hunique0_f; eauto.
      * rewrite <- map_map with (g := map snd) in H0;
          rewrite <- concat_map in H0;
          rewrite map_map in H0;
          rewrite <- map_map with (f := fst) in H0;
          rewrite <- flat_map_concat_map with (l := map fst es) in H0;
          apply generate_cfuns_reflects_comatch_names_flat in H0;
          rewrite flat_map_concat_map in H0; rewrite map_map in H0.
        apply replace_matches_reflects_comatch_names in H2.
        rewrite Forall_forall in Hunique0_f; eapply Hunique0_f; eauto.
    + clear - Hin_gen' Hin_rep' Hunique1 H.
      induction ls; auto; simpl in *; inversion_clear H.
      repeat (repeat rewrite map_app in *; rewrite concat_app in * );
        rewrite in_app_iff in *.
      unique_app_destr_tac.
      inversion_clear Hin_gen'; inversion_clear Hin_rep'; auto.
      * rewrite <- map_map with (g := map snd) in H;
          rewrite <- concat_map in H;
          rewrite map_map in H;
          apply generate_cfuns_reflects_comatch_names in H.
        rewrite map_map in H2; simpl in H2;
          rewrite <- map_map with (f := snd) (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) in H2;
          apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in H2;
          rewrite map_map in H2.
        rewrite Forall_forall in Hunique1_f; eapply Hunique1_f; eauto.
      * rewrite <- map_map with (g := map snd) in H;
          rewrite <- concat_map in H;
          rewrite map_map in H;
          rewrite <- map_map with (f := snd) (l := ls) in H;
          rewrite <- flat_map_concat_map with (l := map snd ls) in H;
          apply generate_cfuns_reflects_comatch_names_flat in H;
          rewrite flat_map_concat_map in H; rewrite map_map in H.
        apply replace_matches_reflects_comatch_names in H2.
        rewrite Forall_forall in Hunique1_f; eapply Hunique1_f; eauto.
  - repeat (rewrite map_app in *; rewrite concat_app in * ).
      repeat unique_app_destr_tac.
      repeat rewrite in_app_iff in *.
      repeat match goal with
             | [ H: _ \/ _ |- _ ] =>
               let H1 := fresh H
               in inversion_clear H as [H1 | H1]
             end; auto;
        try let Hinr := match goal with
                    | [ H: In _ ?lst |- _ ] =>
                      match lst with
                      | context [replace_matches_by_cfun_calls] => H
                      end
                    end
        in let Hing := match goal with
                    | [ H: In _ ?lst |- _ ] =>
                      match lst with
                      | context [generate_cfuns_from_expr] => H
                      end
                    end
           in
           try apply replace_matches_reflects_comatch_names in Hinr;
             try (rewrite map_map in Hinr; simpl in Hinr;
                  rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) in Hinr;
                  apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hinr);

             rewrite <- map_map with (g := map snd) in Hing;
             rewrite <- concat_map in Hing;
             rewrite map_map in Hing;
             try apply generate_cfuns_reflects_comatch_names in Hing;
             try (rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hing;
                  rewrite <- flat_map_concat_map with (f := generate_cfuns_from_expr tn) in Hing;
                  apply generate_cfuns_reflects_comatch_names_flat in Hing;
                  rewrite flat_map_concat_map in Hing);
        repeat rewrite map_map in *;
        match goal with
        | [ Hin: In ?qn ?lst, Hf: Forall _ ?lst |- _ ] =>
          rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
        end.
Qed.

End split_comatches_into_replace_generate_sec.

Lemma generate_cfuns_unique_comatches_propagates: forall (tn : TypeName) (e : expr),
    unique (collect_comatch_names e) ->
    unique (concat (map (fun x : ScopedName * expr => collect_comatch_names (snd x))
                        (concat (map (fun x : cfun_sig * cfun_bod_named => snd (snd x)) (generate_cfuns_from_expr tn e))))).
Proof.
  intros tn e H.
  induction e using expr_strong_ind; simpl in *; auto.
  - match goal with
    | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
      induction lst; inversion_clear Hf; auto; simpl;
        repeat (rewrite map_app; rewrite concat_app);
        simpl in Hunique;
        apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
    end.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_cfuns_reflects_comatch_names in Hin.
    pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1.
    rewrite concat_map in Hnin at 1.
    rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_cfuns_from_expr tn)).
    unfold cfun_bod_named in *.
    specialize Hlem' with (2 := Hnin).
    apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
    apply Hlem'; intros. apply Hlem.
    rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    apply uniqueness_app; auto.
    + IH_tac. unique_sublist_tac.
    + rewrite <- uniqueness_app_rewrite in H; apply proj2 in H; apply proj1 in H.
      match goal with
      | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Hunique;
          apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      unfold cfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      unfold cfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - match goal with
    | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
      induction lst; inversion_clear Hf; auto; simpl;
        repeat (rewrite map_app; rewrite concat_app);
        simpl in Hunique;
        apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
    end.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_cfuns_reflects_comatch_names in Hin.
    pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1.
    rewrite concat_map in Hnin at 1.
    rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_cfuns_from_expr tn)).
    unfold cfun_bod_named in *.
    specialize Hlem' with (2 := Hnin).
    apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
    apply Hlem'; intros. apply Hlem.
    rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    apply uniqueness_app; auto.
    + IH_tac. unique_sublist_tac.
    + rewrite <- uniqueness_app_rewrite in H; apply proj2 in H; apply proj1 in H.
      match goal with
      | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Hunique;
          apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      unfold cfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      unfold cfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - match goal with
    | [ Hf: Forall _ ?lst, Hunique: unique _ |- _ ] =>
      induction lst; inversion_clear Hf; auto; simpl;
        repeat (rewrite map_app; rewrite concat_app);
        simpl in Hunique;
        apply uniqueness_app; [> solve [ IH_tac; unique_sublist_tac] .. | ]
    end.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_cfuns_reflects_comatch_names in Hin.
    pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_cfuns_from_expr tn)).
    specialize Hlem' with (2 := Hnin).
    apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
    apply Hlem'; intros. apply Hlem.
    rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.

  - repeat (rewrite map_app; rewrite concat_app).
    rewrite concat_app in H.
    rename H into Hunique.
    unique_app_destr_full_tac.
    repeat match goal with
           | [ |- unique (?l ++ ?r) ] =>
             apply uniqueness_app
           end;
      repeat
        match goal with
        | [  |- Forall (fun x => ~ In x (?l ++ ?r)) ?ls  ] =>
          let H := fresh in
          assert (H: Forall (fun x => ~ In x l) ls /\ Forall (fun x => ~ In x r) ls ->
                     Forall (fun x => ~ In x (l ++ r)) ls);
            [> let H' := fresh in intro H'; inversion_clear H';
                                  rewrite Forall_forall in *;
                                  intros;
                                  (let H'' := fresh in
                                   intro H'';
                                   rewrite in_app_iff in H''; inversion H'';
                                   match goal with
                                   | [ H: _ |- _ ] =>
                                     eapply H; solve [eauto]
                                   end)
            | apply H; split; clear H ]
        end;
      try (name_destruct_tac; simpl; auto; rewrite app_nil_r); auto;
        try solve [
               match goal with
      | [ Hf: Forall _ _ |- context [?lst] ] =>
        match type of lst with
        | list _ => idtac
        end;
          match lst with
          | _ _ => fail 1
          | _ => idtac
          end;
          match goal with
          | [ Hu: unique ?ls |- _ ] =>
            match ls with
            | context [lst] => clear - Hu Hf
            end
          end;
          induction lst; inversion_clear Hf; simpl in *; auto;
            unique_app_destr_tac;
            repeat (rewrite map_app; rewrite concat_app);
            apply uniqueness_app; auto;
              rewrite Forall_forall;
              intros qn Hnin Hin;
              apply generate_cfuns_reflects_comatch_names in Hnin;
              rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hin;
              match type of Hin with
              | context [map ?f lst] =>
                rewrite <- (flat_map_concat_map _ (map f lst)) in Hin;
                  apply generate_cfuns_reflects_comatch_names_flat in Hin;
                  rewrite flat_map_concat_map in Hin;
                  rewrite map_map in Hin
              end
      end;
      match goal with
      | [ H: Forall _ _ |- _ ] =>
        rewrite Forall_forall in H; eapply H; solve [eauto]
      end
            ];
        try solve [
              rewrite Forall_forall; intros; intro;
              repeat match goal with
                     | [ H: In _ _ |- _ ] =>
                       apply generate_cfuns_reflects_comatch_names in H
                     end;
              repeat match goal with
                     | [ Hin: In _ _ |- _ ] =>
                             rewrite <- map_map with (f := snd) in Hin; rewrite map_map with (g := snd) in Hin;
                             simpl in Hin; rewrite <- map_map with (f := snd) in Hin; rewrite map_map in Hin;
                             apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in Hin;
                             rewrite map_map in Hin
                     end;
              match goal with
              | [ H: In _ ?lst |- _ ] =>
                match lst with
                | context [?lst'] =>
                  match lst' with
                  | map (fun x => generate_cfuns_from_expr _ (?f x)) ?l' =>
                    rewrite <- map_map with (l := l') in H;
                    rewrite <- flat_map_concat_map with (l := map f l') in H;
                    apply generate_cfuns_reflects_comatch_names_flat in H;
                    rewrite flat_map_concat_map in H; rewrite map_map in *
                  end
                end
              end;
              match goal with
              | [ H: Forall _ _ |- _ ] =>
                rewrite Forall_forall in H; eapply H; solve [eauto]
              end
            ].

    + rewrite map_map; simpl.
      clear - H0 Hunique3.
      induction ls; auto; simpl in *; inversion_clear H0.
      replace_with_snd in *.
      unique_app_destr_tac.
      apply uniqueness_app; auto.
      * pose proof (replace_matches_by_cfun_calls_no_new_comatches tn (snd a)).
        unique_sublist_tac.
      * rewrite Forall_forall; intros; intro.
        apply replace_matches_reflects_comatch_names in H0.
        rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) (f := snd) in H2.
        apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in H2;
          rewrite map_map in H2.
        rewrite Forall_forall in Hunique3_f; eapply Hunique3_f; eauto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      rewrite <- map_map with (l := ls) in Hnin;
        rewrite <- map_map with (l := es) in Hin.
      rewrite <- flat_map_concat_map with (l := map fst es) in Hin;
        rewrite <- flat_map_concat_map with (l := map snd ls) in Hnin.
      apply (generate_cfuns_reflects_comatch_names_flat tn) in Hnin;
        apply (generate_cfuns_reflects_comatch_names_flat tn) in Hin.
      rewrite flat_map_concat_map in Hin, Hnin; rewrite map_map in *.
      match goal with
      | [ H: Forall _ _ |- _ ] =>
        rewrite Forall_forall in H; eapply H; solve [eauto]
      end.
    + rewrite Forall_forall; intros qn Hin Hin'.
      apply generate_cfuns_reflects_comatch_names in Hin'.
      rewrite <- map_map with (f := snd) in Hin; rewrite map_map with (g := snd) in Hin;
        simpl in Hin; rewrite <- map_map with (f := snd) in Hin; rewrite map_map in Hin.
      apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in Hin;
        rewrite map_map in Hin.
      match goal with
      | [ H: Forall _ _ |- _ ] =>
        rewrite Forall_forall in H; eapply H; solve [eauto]
      end.
    + rewrite Forall_forall; intros qn Hin Hin'.
      clear - Hin Hin' H0 Hunique3.
      induction ls; auto; simpl in *; inversion_clear H0; unique_app_destr_tac.
      repeat (rewrite map_app in *; rewrite concat_app in * ).
      rewrite in_app_iff in *.
      inversion_clear Hin as [Hin0 | Hin0]; inversion_clear Hin' as [Hin1 | Hin1]; auto.
      * rewrite <- map_map in Hin1; rewrite concat_map in Hin1; rewrite map_map in Hin1.
        eapply split_comatches_into_replace_generate; eauto.
      * apply replace_matches_reflects_comatch_names in Hin0.
        rewrite <- map_map with (f := snd) (l := ls) in Hin1;
          rewrite <- flat_map_concat_map with (l := map snd ls) in Hin1;
          apply generate_cfuns_reflects_comatch_names_flat in Hin1;
          rewrite flat_map_concat_map in Hin1;
          rewrite map_map in Hin1.
        match goal with
        | [ H: Forall _ _ |- _ ] =>
          rewrite Forall_forall in H; eapply H; solve [eauto]
        end.
      * apply generate_cfuns_reflects_comatch_names in Hin1.
        rewrite <- map_map in Hin0; rewrite map_map with (g := snd) in Hin0; simpl in Hin0;
          rewrite <- map_map with (f := snd) in Hin0;
          rewrite map_map in Hin0;
          apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names _)) in Hin0;
          rewrite map_map in Hin0.
        match goal with
        | [ H: Forall _ _ |- _ ] =>
          rewrite Forall_forall in H; eapply H; solve [eauto]
        end.
  - repeat (rewrite map_app in *; rewrite concat_app in * ).
    inversion_clear H as [|_x __x Hn Hunique].
    unique_app_destr_full_tac.
    apply uniqueness_app.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0; specialize (Hunique0 qn Hin); apply Hunique0.
      rewrite <- map_map.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_cfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique1; rewrite Forall_forall in Hunique1; specialize (Hunique1 qn Hin); apply Hunique1.
      rewrite <- map_map.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + clear - Hunique_f.
      rewrite Forall_forall; intros qn Hin Hnin.
      induction es; try solve [inversion Hin]; simpl in *.
      repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
      rewrite <- Forall_app_iff in Hunique_f; inversion_clear Hunique_f as [Hunique Hx].
      rewrite in_app_iff in Hin.
      rename Hin into Hin'; inversion_clear Hin' as [Hin | Hin]; auto.
      apply generate_cfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_cfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_cfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      rewrite Forall_forall in Hunique; specialize (Hunique qn Hin); apply Hunique.
      rewrite <- map_map.
      apply Hlem'; intros; apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    rewrite <- uniqueness_app_rewrite in H; inversion_clear H; inversion_clear H1.
    apply uniqueness_app; auto.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_cfuns_reflects_comatch_names in Hin.
    pose proof (fun qn e => generate_cfuns_reflects_comatch_names tn e qn) as Hlem.
    rewrite Forall_forall in H2; specialize (H2 qn Hin); apply H2; auto.
Qed.

Lemma new_comatch_names_unique : forall p tn,
  comatch_names_unique
    (map (fun x : Name * expr => (fst x, replace_matches_by_cfun_calls tn (snd x)))
       (program_fun_bods p))
    (map
       (fun x : QName * list (ScopedName * expr) =>
        (fst x,
        map
          (fun y : ScopedName * expr => (fst y, replace_matches_by_cfun_calls tn (snd y)))
          (snd x))) (program_cfun_bods_g p)
          ++ new_cfun_bods_l p tn)
    (map
       (fun x : QName * list (ScopedName * expr) =>
        (fst x,
        map
          (fun y : ScopedName * expr => (fst y, replace_matches_by_cfun_calls tn (snd y)))
          (snd x))) (program_gfun_bods_g p)
          ++ []).
Proof.
  intros p tn.
  unfold comatch_names_unique.
  rewrite app_nil_r.
  repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
  reassoc_list_to_right.
  match goal with
  | [  |- unique (?l1 ++ ?l2 ++ ?l3 ++ ?l4) ] =>
    reassoc (l1 ++ l2 ++ l3 ++ l4) ((l1 ++ l2) ++ l3 ++ l4);
      apply unique_app_switch;
      reassoc ((l1 ++ l2) ++ l4 ++ l3) ((l1 ++ l2 ++ l4) ++ l3)
  end.

  apply uniqueness_app.
  - apply uniqueness_app_3way; repeat rewrite map_compose; simpl; try rewrite concat_map; repeat rewrite map_compose;
    let forall_fun_tac :=
        match goal with
        | [  |- Forall _ ?ls ] =>
          match ls with
          | concat (map _ ?bods) =>
            assert (H_sub: sublist ls (concat (map collect_comatch_names (map snd bods))))
          end
        end;
          [> apply sublist_concat';
           induction (program_fun_bods p); try apply Forall2_nil;
           simpl; apply Forall2_cons; try assumption;
           apply replace_matches_by_cfun_calls_no_new_comatches
          |];
          match goal with
          | [ H: sublist ?ss ?ts' |- Forall _ ?ss ] =>
            apply Forall_sublist with (ts := ts'); try assumption
          end; clear H_sub;
            match goal with
            | [  |- Forall ?P _ ] =>
              match P with
              | context [concat (map _ ?l)] =>
                assert (H: forall x, ~ In x (concat (concat (map (fun a => (map (fun a0 => collect_comatch_names (snd a0))
                                                                        (snd a)))
                                                            l)))
                                -> P x)
              end
            end;
            [> clear; intros x H H_in;
             match goal with
             | [ H: ~ In ?x ?ts, H_in: In ?x ?ss |- _ ] =>
               assert (H_in': In x ts);
               [> apply In_sublist with (sub := ss); [> | assumption]
               | apply H; assumption ]
             end;
             clear; apply sublist_concat';
             match goal with
             | [  |- Forall2 _ _ (concat (map _ ?bods)) ] =>
               induction bods
             end; try apply Forall2_nil; apply Forall2_app; try assumption;
             clear; match goal with
                    | [  |- Forall2 _ _ (map _ ?x) ] =>
                      induction x; try apply Forall2_nil; apply Forall2_cons; try assumption
                    end;
             apply replace_matches_by_cfun_calls_no_new_comatches
            |];

            simpl in H;
            match goal with
            | [ H: forall x, ~ In x ?ss -> ~ In x ?ts |- Forall _ ?ls ] =>
              apply Forall_impl with (P := fun x => ~ In x ss); try assumption
            end; clear H;
              pose proof (program_comatch_names_unique p) as H;
              apply comatch_names_unique_global_sublist in H;
              unfold comatch_names_unique in H;
              repeat rewrite map_app in H; repeat rewrite map_map in H; repeat rewrite concat_app in H;
                rewrite map_map;
                match goal with
                | [ H: unique (?x ++ _ ++ ?y) |- _ ] =>
                  assert (H': unique (x ++ y)); [> unique_sublist_tac |]; clear H; rename H' into H
                end +
                match goal with
                | [ H: unique (?x ++ ?y ++ _) |- _ ] =>
                  assert (H': unique (x ++ y)); [> unique_sublist_tac |]; clear H; rename H' into H
                end;
                apply uniqueness_app_not_in;
                match goal with
                | [ H: unique (?l ++ ?r) |- unique (?l ++ ?r') ] =>
                  assert (E: r' = r);
                    [> | rewrite E; assumption]
                end;
                rewrite concat_map; rewrite map_map; reflexivity
   in
     let unique_xfun_tac :=
         match goal with
         | [ |- unique (concat (concat (map (fun a => map ?f (map (fun y => (fst y, ?rep ?t (snd y))) (snd a)))
                                           ?bods))) ] =>
           apply uniqueness_sublist with (tot := (concat (concat (map (fun a => map (fun a0 => collect_comatch_names (snd a0))
                                                                                 (snd a))
                                                                      bods))))
         end;
           [> apply sublist_concat';
            match goal with
            | [  |- Forall2 _ _ (concat (map _ ?bods)) ] =>
              induction bods
            end; try apply Forall2_nil;
            simpl; apply Forall2_app; try assumption;
            rewrite map_map; clear;
            match goal with
            | [  |- Forall2 _ (map _ ?ls) (map _ ?ls) ] =>
              induction ls
            end; try apply Forall2_nil;
            simpl; apply Forall2_cons; try assumption;
            apply replace_matches_by_cfun_calls_no_new_comatches
           | pose proof (program_comatch_names_unique p);
             apply comatch_names_unique_global_sublist in H;
             unfold comatch_names_unique in H;
             repeat rewrite map_app in H;
             repeat rewrite concat_app in H;
             repeat rewrite map_map in H;
             rewrite <- map_map; rewrite <- concat_map;
             (idtac + rewrite app_assoc in H); unique_sublist_tac
           ]
           in
             [> | unique_xfun_tac | unique_xfun_tac | forall_fun_tac | forall_fun_tac | ].

  + apply uniqueness_sublist with (tot := concat (map (fun a => collect_comatch_names (snd a)) (program_fun_bods p))).
    * apply sublist_concat.
      induction (program_fun_bods p); try apply Forall_nil.
      apply Forall_cons; try assumption.
      apply replace_matches_by_cfun_calls_no_new_comatches.
    * pose proof (program_comatch_names_unique p) as H_unique.
      unfold comatch_names_unique in H_unique.
      match goal with
      | [ H: unique ?t |- unique ?s ] =>
        apply uniqueness_sublist with (tot := t)
      end; try assumption.
      repeat rewrite map_app.
      repeat rewrite concat_app.
      rewrite map_map. apply sublist_app_embed_l.

  + pose proof (program_comatch_names_unique p) as H;
      apply comatch_names_unique_global_sublist in H;
      unfold comatch_names_unique in H.
    repeat rewrite map_app in H. repeat rewrite concat_app in H.
    match goal with
    | [ H: unique ?bs |- Forall _ ?ls ] =>
      match ls with
      | context [?bods] =>
        match bods with
        | (?p_bods p) =>
          match bs with
          | context [concat ?bs'] =>
            match bs' with
            | context [p_bods p] =>
              clear H; assert (H_sub: sublist ls (concat bs'));
                [> apply sublist_concat';
                 induction (p_bods p); try apply Forall2_nil;
                 simpl; repeat rewrite map_app; apply Forall2_app; try assumption; unfold cfun_bod;
                 match goal with
                 | [  |- Forall2 _ _ (map _ (map _ ?x)) ] =>
                   induction x; try apply Forall2_nil
                 end; simpl; apply Forall2_cons; try assumption;
                 apply replace_matches_by_cfun_calls_no_new_comatches
                |]
            end
          end
        end
      end
    end.
    match goal with
    | [ H: sublist ?ss ?ts' |- Forall _ ?ss ] =>
      apply Forall_sublist with (ts := ts'); try assumption
    end; clear H_sub.
    match goal with
    | [  |- Forall ?P _ ] =>
      match P with
      | context [concat (map _ ?l)] =>
      assert (H: forall x, ~ In x (concat (concat (map (fun a => (map (fun a0 => collect_comatch_names (snd a0))
                                                                  (snd a)))
                                                  l)))
                        -> P x)
      end
    end;
    [> clear; intros x H H_in;
      match goal with
      | [ H: ~ In ?x ?ts, H_in: In ?x ?ss |- _ ] =>
        assert (H_in': In x ts);
          [> apply In_sublist with (sub := ss); [> | assumption]
          | apply H; assumption ]
      end;
      clear; apply sublist_concat';
      match goal with
      | [  |- Forall2 _ _ (concat (map _ ?bods)) ] =>
        induction bods
      end; try apply Forall2_nil; apply Forall2_app; try assumption;
      clear; match goal with
      | [  |- Forall2 _ _ (map _ ?x) ] =>
        induction x; try apply Forall2_nil; apply Forall2_cons; try assumption
      end;
      apply replace_matches_by_cfun_calls_no_new_comatches
     |].

    simpl in H.
    match goal with
    | [ H: forall x, ~ In x ?ss -> ~ In x ?ts |- Forall _ ?ls ] =>
      apply Forall_impl with (P := fun x => ~ In x ss); try assumption
    end; clear H.
    pose proof (program_comatch_names_unique p) as H;
      apply comatch_names_unique_global_sublist in H;
      unfold comatch_names_unique in H.
    repeat rewrite map_app in H; repeat rewrite map_map in H; repeat rewrite concat_app in H;
    rewrite map_map.
    match goal with
    | [ H: unique (_ ++ ?x ++ ?y) |- _ ] =>
      assert (H': unique (x ++ y)); [> unique_sublist_tac |]; clear H; rename H' into H
    end;
    apply uniqueness_app_not_in;
    match goal with
    | [ H: unique (?l ++ ?r) |- unique (?l ++ ?r') ] =>
      assert (E: r' = r);
        [> | rewrite E; assumption]
    end;
    rewrite concat_map; rewrite map_map; reflexivity.
 - pose proof (program_comatch_names_unique p) as H.
   apply comatch_names_unique_global_sublist in H.
   unfold comatch_names_unique in H.
   unfold new_cfun_bods_l.
   repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
   repeat rewrite map_map in *.
   repeat unique_app_destr_tac.
   apply uniqueness_app_3way.
   + clear - H0.
     induction (program_fun_bods p); auto; simpl in *.
     repeat (rewrite map_app; rewrite concat_app).
     unique_app_destr_tac.
     apply uniqueness_app; auto.
     * apply generate_cfuns_unique_comatches_propagates; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_cfuns_reflects_comatch_names in Hin.
       rewrite Forall_forall in H0_f; eapply H0_f; eauto.
       rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
       clear - Hnin; unfold fun_bod in *.
       induction (@map (Name * expr) expr snd f); auto.
       simpl in *. repeat (rewrite map_app in *; rewrite concat_app in * ).
       rewrite in_app_iff in *.
       inversion Hnin; auto.
   + clear - H3.
     induction (program_gfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; repeat rewrite flat_map_app in *; repeat rewrite concat_app in * ).
     unique_app_destr_tac.
     apply uniqueness_app; auto.
     * clear - H0. unfold gfun_bod_named in *. unfold gfun_bod in *.
       induction (@snd QName _ a); auto; simpl in *.
       repeat (rewrite map_app; rewrite concat_app).
       unique_app_destr_tac.
       apply uniqueness_app; auto.
       -- apply generate_cfuns_unique_comatches_propagates; auto.
       -- rewrite Forall_forall; intros qn Hin Hnin.
          rewrite Forall_forall in H0_f; eapply H0_f.
          ++ eapply (generate_cfuns_reflects_comatch_names tn _ qn); auto.
          ++ rewrite <- map_map.
             eapply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
             clear - Hnin.
             induction (map snd l); auto.
             simpl in *.
             repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
             rewrite in_app_iff; rewrite in_app_iff in Hnin.
             inversion_clear Hnin; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_cfuns_reflects_comatch_names_flat in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite map_map in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite Forall_forall in H3_f; eapply H3_f; eauto.
       rewrite <- map_map; rewrite <- flat_map_concat_map.
       apply generate_cfuns_reflects_comatch_names_flat in Hin; auto.
   + clear - H2.
     induction (program_cfun_bods_g p) as [| a g]; auto; simpl in *.
     repeat (repeat rewrite map_app in *; repeat rewrite flat_map_app in *; repeat rewrite concat_app in * ).
     unique_app_destr_tac.
     apply uniqueness_app; auto.
     * clear - H0. unfold cfun_bod_named in *. unfold cfun_bod in *.
       induction (@snd QName _ a); auto; simpl in *.
       repeat (rewrite map_app; rewrite concat_app).
       unique_app_destr_tac.
       apply uniqueness_app; auto.
       -- apply generate_cfuns_unique_comatches_propagates; auto.
       -- rewrite Forall_forall; intros qn Hin Hnin.
          rewrite Forall_forall in H0_f; eapply H0_f.
          ++ eapply (generate_cfuns_reflects_comatch_names tn _ qn); auto.
          ++ rewrite <- map_map.
             eapply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
             clear - Hnin.
             induction (map snd l); auto.
             simpl in *.
             repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
             rewrite in_app_iff; rewrite in_app_iff in Hnin.
             inversion_clear Hnin; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_cfuns_reflects_comatch_names_flat in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite map_map in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite Forall_forall in H2_f; eapply H2_f; eauto.
       rewrite <- map_map; rewrite <- flat_map_concat_map.
       apply generate_cfuns_reflects_comatch_names_flat in Hin; auto.
   + clear - H_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H_f.
     * clear H_f Hnin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
       unfold fun_bod in *.
       induction (@map _ expr snd (program_fun_bods p)); eauto; simpl in *.
       repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
       rewrite in_app_iff in *.
       inversion_clear Hin; auto.
     * rewrite in_app_iff; right. unfold cfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_cfuns_reflects_comatch_names_flat tn); auto. repeat rewrite flat_map_concat_map in *; auto.
   + clear - H_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H_f.
     * clear H_f Hnin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
       unfold fun_bod in *.
       induction (@map _ expr snd (program_fun_bods p)); eauto; simpl in *.
       repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
       rewrite in_app_iff in *.
       inversion_clear Hin; auto.
     * rewrite in_app_iff; left. unfold cfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_cfuns_reflects_comatch_names_flat tn); auto. repeat rewrite flat_map_concat_map in *; auto.
   + clear - H1_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H1_f.
     * clear H1_f Hin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_cfuns_reflects_comatch_names tn e qn)).
       rewrite <- flat_map_concat_map with (l := program_cfun_bods_g p).
       unfold cfun_bod_named in *; unfold cfun_bod in *.
       induction (@map _ expr snd (flat_map snd (program_cfun_bods_g p))); eauto; simpl in *.
       repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin); eauto.
       rewrite in_app_iff in *.
       inversion_clear Hnin; auto.
     * unfold cfun_bod_named in *; unfold cfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_cfuns_reflects_comatch_names_flat tn).
       repeat rewrite flat_map_concat_map in *; auto.
 - unfold new_cfun_bods_l. repeat rewrite map_map; simpl.
   repeat rewrite concat_map; repeat (rewrite map_map; simpl).
   rewrite Forall_forall; intros qn Hin Hnin.
   repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
   repeat rewrite in_app_iff in *.
   rename Hin into Hin'; rename Hnin into Hnin';
     inversion_clear Hin' as [Hin|[Hin|Hin]]; inversion_clear Hnin' as [Hnin|[Hnin|Hnin]].
   + rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) (f := snd) in Hin.
     assert (unique (flat_map collect_comatch_names (map snd (program_fun_bods p)))).
     { pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
       rewrite flat_map_concat_map.
       repeat rewrite map_app in H; repeat rewrite concat_app in H.
       unique_sublist_tac.
     }
     unfold fun_bod in *.
     induction (@map _ expr snd (program_fun_bods p)); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion_clear Hin; inversion_clear Hnin; auto;
     unique_app_destr_tac; auto.
     * eapply split_comatches_into_replace_generate; eauto.
       split; eauto. clear - H1.
       induction (generate_cfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_matches_reflects_comatch_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_cfuns_reflects_comatch_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_cfuns_reflects_comatch_names tn).
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite map_map in H1; auto.
   + pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := fs
       in assert (unique (l ++ ggs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) in Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hnin. rewrite <- flat_map_concat_map. apply (generate_cfuns_reflects_comatch_names_flat tn).
     unfold gfun_bod_named in *. unfold gfun_bod in *.
     rewrite flat_map_concat_map with (f := snd) in Hnin.
     induction (map snd (concat (@map _ (list (ScopedName * expr)) snd (program_gfun_bods_g p)))); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *; inversion_clear Hnin; auto.
     left. repeat rewrite map_map in H; rewrite concat_map; rewrite map_map; auto.
   + pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := fs
       in assert (unique (l ++ cgs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) in Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hnin. rewrite <- flat_map_concat_map. apply (generate_cfuns_reflects_comatch_names_flat tn).
     unfold cfun_bod_named in *. unfold cfun_bod in *.
     rewrite flat_map_concat_map with (f := snd) in Hnin.
     induction (map snd (concat (@map _ (list (ScopedName * expr)) snd (program_cfun_bods_g p)))); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *; inversion_clear Hnin; auto.
     left. repeat rewrite map_map in H; rewrite concat_map; rewrite map_map; auto.
   + pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := fs
       in assert (unique (l ++ cgs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_cfuns_reflects_comatch_names_flat tn) in Hnin.
     rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)).
     induction (program_cfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion Hin; auto; left.
     rewrite map_map in H; simpl in H.
     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) (f := snd) in H; auto.
   + pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := cgs
       in assert (unique (l ++ ggs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map in Hin. rewrite <- concat_map in Hin. rewrite <- map_map in Hin.
     rewrite concat_map in Hin. rewrite <- map_map with (f := snd) in Hin.
     rewrite map_map in Hin.
     rewrite (map_ext _ _ (map_map _ _)) in Hin.
     simpl in Hin. rewrite (map_ext _ _ (fun x => eq_sym (map_map _ _ x))) in Hin.
     rewrite <- map_map with (f := map snd) in Hin.
     rewrite <- concat_map in Hin. rewrite map_map in Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hin.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_cfuns_reflects_comatch_names_flat tn) in Hnin.
     rewrite <- concat_map in Hin; repeat rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); clear H0; auto.
   + rewrite <- map_map in Hin. rewrite <- concat_map in Hin.
     rewrite <- map_map with (f := snd) (g := map (fun y => (fst y, replace_matches_by_cfun_calls tn (snd y)))) in Hin.
     rewrite <- concat_map in Hin; repeat rewrite <- flat_map_concat_map in Hin; rewrite flat_map_concat_map in Hin.
     rewrite map_map in Hin; simpl in Hin. rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) (f := snd) in Hin.
     assert (unique (flat_map collect_comatch_names (map snd (flat_map snd (program_cfun_bods_g p))))).
     { pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
       rewrite flat_map_concat_map.
       repeat (repeat rewrite map_app in H; repeat rewrite concat_app in H).
       rewrite flat_map_concat_map. unique_sublist_tac.
     }
     unfold cfun_bod in *.
     induction (@map _ expr snd (flat_map snd (program_cfun_bods_g p))); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion_clear Hin; inversion_clear Hnin; auto;
     unique_app_destr_tac; auto.
     * eapply split_comatches_into_replace_generate; eauto.
       split; eauto. clear - H1.
       induction (generate_cfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_matches_reflects_comatch_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_cfuns_reflects_comatch_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_cfuns_reflects_comatch_names tn).
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite map_map in H1; auto.
   + pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := fs
       in assert (unique (l ++ ggs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_cfuns_reflects_comatch_names_flat tn) in Hnin.
     rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)).
     induction (program_gfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion Hin; auto; left.
     rewrite map_map in H; simpl in H.
     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) (f := snd) in H; auto.
   + rewrite <- map_map in Hin. rewrite <- concat_map in Hin.
     rewrite <- map_map with (f := snd) (g := map (fun y => (fst y, replace_matches_by_cfun_calls tn (snd y)))) in Hin.
     rewrite <- concat_map in Hin; repeat rewrite <- flat_map_concat_map in Hin; rewrite flat_map_concat_map in Hin.
     rewrite map_map in Hin; simpl in Hin. rewrite <- map_map with (g := fun x => collect_comatch_names (replace_matches_by_cfun_calls tn x)) (f := snd) in Hin.
     assert (unique (flat_map collect_comatch_names (map snd (flat_map snd (program_gfun_bods_g p))))).
     { pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
       rewrite flat_map_concat_map.
       repeat (repeat rewrite map_app in H; repeat rewrite concat_app in H).
       rewrite flat_map_concat_map. unique_sublist_tac.
     }
     unfold gfun_bod in *.
     induction (@map _ expr snd (flat_map snd (program_gfun_bods_g p))); auto; simpl in *.
     repeat (rewrite map_app in *; repeat rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion_clear Hin; inversion_clear Hnin; auto;
     unique_app_destr_tac; auto.
     * eapply split_comatches_into_replace_generate; eauto.
       split; eauto. clear - H1.
       induction (generate_cfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_matches_reflects_comatch_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_cfuns_reflects_comatch_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_cfuns_reflects_comatch_names tn).
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite map_map in H1; auto.
   + pose proof (program_comatch_names_unique p); unfold comatch_names_unique in *.
     repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
     reassoc_list_to_right_hyp H.
     match type of H with
     | unique (?fs ++ ?cgs ++ ?cls ++ ?ggs ++ ?gls) =>
       let l := cgs
       in assert (unique (l ++ ggs));
         [> repeat unique_app_destr_tac; apply uniqueness_app; auto;
          match goal with
          | [ H: Forall _ l |- _ ] =>
            rewrite Forall_forall in *; intros qn' Hin' Hnin';
            apply (H qn'); auto; In_sublist_tac
          end
          |]
     end; clear H.
     apply uniqueness_app_not_in in H0.
     rewrite <- map_map in Hin. rewrite <- concat_map in Hin. rewrite <- map_map in Hin.
     rewrite concat_map in Hin. rewrite <- map_map with (f := snd) in Hin.
     rewrite map_map in Hin.
     rewrite (map_ext _ _ (map_map _ _)) in Hin.
     simpl in Hin. rewrite (map_ext _ _ (fun x => eq_sym (map_map _ _ x))) in Hin.
     rewrite <- map_map with (f := map snd) in Hin.
     rewrite <- concat_map in Hin. rewrite map_map in Hin.
     apply (in_map_concat _ _ _ _ (replace_matches_reflects_comatch_names tn)) in Hin.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_cfuns_reflects_comatch_names_flat tn) in Hnin.
     rewrite <- concat_map in Hin; repeat rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); clear H0; auto.
Qed.


(* Note this assumes that the input program contains no functions annotated as local.
   (If there are local consumer functions, this just returns the original program.)
 *)
Definition lift_match_to_program (p : program) (tn : TypeName) : program :=
match Nat.eq_dec (length (skeleton_cfun_sigs_l (program_skeleton p))) O with
| left eq2 =>
let Uniq := new_cfun_sigs_names_unique p tn eq2 in
match Nat.eq_dec (length (skeleton_gfun_sigs_l (lift_match_to_skeleton p tn Uniq))) O with
| left eq =>
{|
      (* Skeleton *)
      program_skeleton := lift_match_to_skeleton p tn (new_cfun_sigs_names_unique p tn eq2);
      (* Ordinary functions *)
      program_fun_bods := map (fun x => (fst x, replace_matches_by_cfun_calls tn (snd x))) (program_fun_bods p);
      program_has_all_fun_bods := new_has_all_funbods p tn Uniq (program_has_all_fun_bods p);
      program_fun_bods_typecheck := new_funbods_typecheck p tn Uniq (program_fun_bods_typecheck p);
      (* Consumer functions *)
      program_cfun_bods_g := map (fun x => (fst x, map (fun y => (fst y, replace_matches_by_cfun_calls tn (snd y))) (snd x))) (program_cfun_bods_g p);
      program_has_all_cfun_bods_g := new_has_all_cfunbods_g p tn Uniq (program_has_all_cfun_bods_g p);
      program_cfun_bods_typecheck_g := new_cfunbods_g_typecheck p tn Uniq (program_cfun_bods_typecheck_g p);
      program_cfun_bods_l := new_cfun_bods_l p tn;
      program_has_all_cfun_bods_l := new_has_all_cfunbods_l p tn Uniq eq2;
      program_cfun_bods_typecheck_l := new_cfun_bods_l_typecheck p tn Uniq eq2;
      (* Generator functions *)
      program_gfun_bods_g := map (fun x => (fst x, map (fun y => (fst y, replace_matches_by_cfun_calls tn (snd y))) (snd x))) (program_gfun_bods_g p);
      program_has_all_gfun_bods_g := new_has_all_gfunbods_g p tn Uniq (program_has_all_gfun_bods_g p);
      program_gfun_bods_typecheck_g := new_gfunbods_g_typecheck p tn Uniq (program_gfun_bods_typecheck_g p);
      program_gfun_bods_l := [];
      program_has_all_gfun_bods_l := new_has_all_gfunbods_l p tn Uniq eq;
      program_gfun_bods_typecheck_l := Forall_nil _;
      (* Uniqueness conditions *)
      program_match_names_unique := new_match_names_unique p tn;
      program_comatch_names_unique := new_comatch_names_unique p tn;
   |}
| _ => p
end
| _ => p
end.

