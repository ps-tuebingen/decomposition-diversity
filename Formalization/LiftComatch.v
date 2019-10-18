(**************************************************************************************************)
(* Total Constructor/Destructorization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: LiftComatch.v                                                                            *)
(*                                                                                                *)
(**************************************************************************************************)
Require Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.

Require Import Names.
Require Import AST.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import BodyTypeDefs.
Require Import ProgramDef.
Require Import UtilsProgram.
Require Import GenericLemmas.
Require Import GenericTactics.
Require Import Typechecker.
Require Import UtilsTypechecker.
Require Import Sublist.
Require Import Unique.
Require Import Subterm.

(* Replace the first occurrances of all comatches of a given codata type by a gfun call *)
Fixpoint replace_comatches_by_gfun_calls (tn : TypeName) (e : expr) : expr :=
    match e with
  | E_Var x => E_Var x
  | E_Constr sn args => E_Constr sn (map (replace_comatches_by_gfun_calls tn) args)
  | E_DestrCall sn e' args => E_DestrCall sn (replace_comatches_by_gfun_calls tn e') (map (replace_comatches_by_gfun_calls tn) args)
  | E_FunCall n args => E_FunCall n (map (replace_comatches_by_gfun_calls tn) args)
  | E_GenFunCall sn args => E_GenFunCall sn (map (replace_comatches_by_gfun_calls tn) args)
  | E_ConsFunCall sn e' args => E_ConsFunCall sn (replace_comatches_by_gfun_calls tn e') (map (replace_comatches_by_gfun_calls tn) args)
  | E_Match qn' e bs cases rtype =>
    E_Match qn'
            (replace_comatches_by_gfun_calls tn e)
            (map (fun exp_typ => (replace_comatches_by_gfun_calls tn (fst exp_typ), snd exp_typ)) bs)
            (map (fun sn_exp => (fst sn_exp, replace_comatches_by_gfun_calls tn (snd sn_exp))) cases)
            rtype
  | E_CoMatch qn bs cocases =>
    if (eq_TypeName tn (fst qn))
    then E_GenFunCall (local qn) (map (fun b => (replace_comatches_by_gfun_calls tn (fst b))) bs)
    else E_CoMatch qn
                   (map (fun exp_typ => (replace_comatches_by_gfun_calls tn (fst exp_typ), snd exp_typ)) bs)
                   (map (fun sn_exp => (fst sn_exp, replace_comatches_by_gfun_calls tn (snd sn_exp))) cocases)
  | E_Let e1 e2 => E_Let (replace_comatches_by_gfun_calls tn e1) (replace_comatches_by_gfun_calls tn e2)
  end.

(* Generate the set of new gfun_sigs and gfun_bods for a given expression *)
Fixpoint generate_gfuns_from_expr (tn : TypeName) (e : expr) : list (gfun_sig * gfun_bod_named) :=
  match e with
  | E_Var x => []
  | E_Constr _ args => concat (map (generate_gfuns_from_expr tn) args)
  | E_DestrCall _ e args => (generate_gfuns_from_expr tn e) ++ (concat (map (generate_gfuns_from_expr tn) args))
  | E_FunCall _ args => concat (map (generate_gfuns_from_expr tn) args)
  | E_GenFunCall _ args => concat (map (generate_gfuns_from_expr tn) args)
  | E_ConsFunCall _ e args => (generate_gfuns_from_expr tn e) ++ (concat (map (generate_gfuns_from_expr tn) args))
  | E_Match _ e bs cases _ =>
    (generate_gfuns_from_expr tn e)
      ++ (concat (map (fun exp_typ => generate_gfuns_from_expr tn (fst exp_typ)) bs))
      ++ (concat (map (fun sn_exp => generate_gfuns_from_expr tn (snd sn_exp)) cases))
  | E_CoMatch qn bs cocases =>
    (if (eq_TypeName tn (fst qn))
     then let sig : gfun_sig := (qn, map snd bs) in
          let bod : gfun_bod := map (fun sn_exp => (fst sn_exp, replace_comatches_by_gfun_calls tn (snd sn_exp))) cocases  in
          [(sig, (qn, bod))]
     else [])
      ++ (concat (map (fun exp_typ => generate_gfuns_from_expr tn (fst exp_typ)) bs))
      ++ (concat (map (fun sn_exp => generate_gfuns_from_expr tn (snd sn_exp)) cocases))
  | E_Let e1 e2 => (generate_gfuns_from_expr tn e1) ++ (generate_gfuns_from_expr tn e2)
  end.

Lemma lift_cocomatch_subst: forall (e e' : expr) (tn : TypeName) (n : nat),
    replace_comatches_by_gfun_calls tn (substitute' n e e') =
    substitute' n (replace_comatches_by_gfun_calls tn e)
                (replace_comatches_by_gfun_calls tn e').
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
  - f_equal; auto.
    repeat rewrite map_map.
    clear - H0.
    induction es; auto; inversion_clear H0; simpl; f_equal; auto.
    destruct a; simpl in *; f_equal; auto.
  - name_destruct_tac; simpl; f_equal; auto.
    + clear - H0; induction es; auto; simpl; inversion_clear H0; f_equal; auto.
      destruct a; simpl; auto.
    + clear - H0; induction es; auto; simpl; inversion_clear H0; f_equal; auto.
      destruct a; simpl; f_equal; auto.
Qed.

Ltac concat_map_induction_tac :=
  match goal with
  | [ H : Forall ?P ?ls |- Forall ?P' (concat (map ?f ?ls)) ] =>
    induction ls; try apply Forall_nil;
    inversion H; subst; clear H;
    apply Forall_app; auto
  end.

Ltac generate_gfuns_from_expr_names_match_tac :=
  intros tn e; induction e using expr_strong_ind; simpl; try apply Forall_nil;
  try apply Forall_app; try auto;
  try concat_map_induction_tac.

Lemma generate_gfuns_from_expr_names_match : forall (tn : TypeName) (e : expr),
    Forall (fun sig_bod => (fst (fst sig_bod)) = (fst (snd (sig_bod)))) (generate_gfuns_from_expr tn e).
Proof.
  generate_gfuns_from_expr_names_match_tac.
  - repeat apply Forall_app; try auto.
    + clear - H0. induction es; simpl; try apply Forall_nil.
      inversion H0; subst; clear H0.
      apply Forall_app; try auto.
    + clear - H.  induction ls; simpl; try apply Forall_nil.
      inversion H; subst; clear H.
      apply Forall_app; try auto.
  - destruct (eq_TypeName tn (fst n)); try apply Forall_nil.
    apply Forall_cons; try apply Forall_nil. reflexivity.
  - apply Forall_app; try auto.
    + clear - H0. induction es; simpl; try apply Forall_nil.
      inversion H0; subst; clear H0.
      apply Forall_app; try auto.
    + clear - H.  induction ls; simpl; try apply Forall_nil.
      inversion H; subst; clear H.
      apply Forall_app; try auto.
Qed.


(* Property holds of expression e, if e does not contain comatches on given codata type. *)
Definition contains_no_comatches (tn : TypeName) (e : expr) : Prop :=
  filter (fun x => eq_TypeName tn (fst x)) (collect_comatch_names e) = [].

Lemma replace_comatches_by_gfun_calls_removes_all_comatches : forall (e : expr) (tn : TypeName),
    contains_no_comatches tn (replace_comatches_by_gfun_calls tn e).
Proof.
  intros e tn.
  unfold contains_no_comatches.
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
         - clear IHe; rewrite filter_app.
           do 2 (rewrite filter_concat).
           repeat rewrite map_map.
           induction es; simpl.
           + induction ls; try reflexivity; simpl.
             inversion H; subst. unfold snd at 1. rewrite H3; simpl.
             apply IHls; assumption.
           + inversion H0; subst. unfold fst at 2. rewrite H3; simpl.
             apply IHes; assumption.
         - name_destruct_tac.
           + clear H; induction es; try reflexivity.
             simpl. inversion_clear H0. rewrite filter_app.
             unfold fst at 2; unfold QName in *; rewrite H.
             simpl. apply IHes; assumption.
           + simpl. rewrite E__name. rewrite concat_app. rewrite filter_app.
             induction es; simpl.
             * induction ls; try reflexivity; simpl.
               inversion_clear H. rewrite filter_app.
               unfold snd at 1; unfold QName in *; rewrite H1; simpl.
               apply IHls; assumption.
             * inversion_clear H0. rewrite filter_app.
               unfold fst at 2; unfold QName in *; rewrite H1; simpl.
               apply IHes; assumption.
         - rewrite IHe2; auto.
Qed.

Lemma generate_gfuns_from_expr_contains_no_comatches : forall (e : expr) (tn : TypeName),
    Forall (fun sig_bod => Forall (fun sn_exp => contains_no_comatches tn (snd sn_exp)) (snd(snd sig_bod))) (generate_gfuns_from_expr tn e).
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
  - apply replace_comatches_by_gfun_calls_removes_all_comatches.
  - IH_auto_tac.
Qed.



(**************************************************************************************************)
(* ** Construct the new program with lifted codata type                                           *)
(*                                                                                                *)
(**************************************************************************************************)

Lemma new_gfun_sigs_from_expr_in_cdts : forall (sk : skeleton) (tn : TypeName) (e : expr),
    (exists ctxt t, (sk / ctxt |- e : t)) ->
    gfun_sigs_in_cdts (skeleton_cdts sk) (map fst (generate_gfuns_from_expr tn e)).
Proof.
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
    destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst.
    repeat rewrite map_app. repeat apply Forall_app.
    + clear - IHe  H6. apply IHe. exists ctxt. exists (fst n). assumption.
    + clear - H1 H11. generalize dependent bindings_types. induction bindings_exprs; intros; try apply Forall_nil.
      inversion H11; subst. simpl in *. rewrite map_app. inversion H1; subst. apply Forall_app.
      * apply H2. exists ctxt. exists t. assumption.
      * apply IHbindings_exprs; assumption.
    + clear - H14 H0.
      generalize dependent (map (fun ctor : ScopedName * list TypeName => snd ctor ++ bindings_types) ctorlist).
      generalize dependent (repeat t (length ls)). induction ls; intros; try apply Forall_nil.
      simpl. rewrite map_app. inversion H0; subst.
      inversion H14; subst.
      apply Forall_app.
      * apply H2. destruct a; simpl in *. exists ctx. exists t0. assumption.
      * eapply IHls; try assumption. apply H8.
  - (* E_Comatch *)
    destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst.
    destruct (eq_TypeName tn (fst n)) eqn:E.
    + name_eq_tac. simpl. apply Forall_cons.
      * simpl in *. clear - H8. pose proof (lookup_dtors_in_cdts _ _ _ H8).
        assumption.
      * rewrite map_app. apply Forall_app.
        -- clear - H1 H5. generalize dependent bindings_types. induction bindings_exprs; intros; try apply Forall_nil.
           inversion H5; subst. simpl in *. rewrite map_app. inversion H1; subst. apply Forall_app.
           ++ apply H2. exists ctxt. exists t. assumption.
           ++ apply IHbindings_exprs; assumption.
        -- clear - H11 H0.
           generalize dependent (map (fun dtor : ScopedName * list TypeName * TypeName => snd (fst dtor) ++ bindings_types) dtorlist).
           generalize dependent (map snd dtorlist).
           induction ls; intros; try apply Forall_nil.
           simpl. rewrite map_app. inversion H0; subst.
           inversion H11; subst.
           apply Forall_app.
           ++ apply H2. destruct a; simpl in *. exists ctx. exists t. assumption.
           ++ eapply IHls; try assumption. apply H8.
    + simpl. rewrite map_app. apply Forall_app.
      * clear - H1 H5. generalize dependent bindings_types. induction bindings_exprs; intros; try apply Forall_nil.
         inversion H5; subst. simpl in *. rewrite map_app. inversion H1; subst. apply Forall_app.
         -- apply H2. exists ctxt. exists t. assumption.
         -- apply IHbindings_exprs; assumption.
      * clear - H11 H0.
         generalize dependent (map (fun dtor : ScopedName * list TypeName * TypeName => snd (fst dtor) ++ bindings_types) dtorlist).
         generalize dependent (map snd dtorlist).
         induction ls; intros; try apply Forall_nil.
         simpl. rewrite map_app. inversion H0; subst.
         inversion H11; subst.
         apply Forall_app.
         -- apply H2. destruct a; simpl in *. exists ctx. exists t. assumption.
         -- eapply IHls; try assumption. apply H8.
  - (* E_Let *)
    rewrite map_app. destruct H as [ctxt [t H_typecheck]]. inversion H_typecheck; subst.
    apply Forall_app.
    + apply IHe1. exists ctxt. exists t1. assumption.
    + apply IHe2. exists (t1 :: ctxt). exists t. assumption.
Qed.

Definition new_gfuns_from_funs (p : program) (tn : TypeName) : list (gfun_sig * gfun_bod_named) :=
  let funbods : list expr := map snd (program_fun_bods p) in
  concat (map (generate_gfuns_from_expr tn) funbods).

Lemma new_gfun_sigs_from_funs_in_cdts : forall (p : program) (tn : TypeName),
    gfun_sigs_in_cdts (skeleton_cdts (program_skeleton p)) (map fst (new_gfuns_from_funs p tn)).
Proof.
  intros p tn. unfold gfun_sigs_in_cdts. unfold new_gfuns_from_funs.
  pose proof (program_fun_bods_typecheck p).
  induction (program_fun_bods p); try apply Forall_nil.
 simpl. rewrite map_app. inversion H; subst. apply Forall_app.
  - apply new_gfun_sigs_from_expr_in_cdts. clear - H2. destruct H2 as [n [args [t [_ H_typecheck]]]].
    exists args. exists t. assumption.
  - apply IHf. inversion H; subst. assumption.
Qed.


Definition new_gfuns_from_gfuns (p : program) (tn : TypeName) : list (gfun_sig * gfun_bod_named) :=
  let gfuncases : list (ScopedName * expr) := concat (map snd (program_gfun_bods_g p)) in
  let gfunbods : list expr := map snd gfuncases in
  concat (map (generate_gfuns_from_expr tn) gfunbods).

Lemma new_gfun_sigs_from_gfuns_in_cdts : forall (p : program) (tn : TypeName),
    gfun_sigs_in_cdts (skeleton_cdts (program_skeleton p)) (map fst (new_gfuns_from_gfuns p tn)).
Proof.
  intros p tn. unfold gfun_sigs_in_cdts. unfold new_gfuns_from_gfuns.
  pose proof (program_gfun_bods_typecheck_g p).
  induction (program_gfun_bods_g p); simpl; try apply Forall_nil.
  inversion H; subst.
  repeat rewrite map_app. rewrite concat_app. rewrite map_app. apply Forall_app.
  - clear - H2. destruct a as [a_qn a_bod]; simpl in *. destruct H2 as [qn [args [_ H_typecheck]]].
    inversion H_typecheck; subst. clear - H8.
    generalize dependent (map (fun dtor : ScopedName * list TypeName * TypeName => snd (fst dtor) ++ bindings_types) dtorlist).
    generalize dependent (map snd dtorlist).
    induction a_bod; intros; try apply Forall_nil; simpl.
    rewrite map_app. inversion H8; subst.
    apply Forall_app.
    + clear - H3.
      apply new_gfun_sigs_from_expr_in_cdts. exists ctx. exists t. assumption.
    + eapply IHa_bod. apply H5.
  - apply IHg. assumption.
Qed.

Definition new_gfuns_from_cfuns (p : program) (tn : TypeName) : list (gfun_sig * gfun_bod_named) :=
  let cfuncases : list (ScopedName * expr) := concat (map snd (program_cfun_bods_g p)) in
  let cfunbods : list expr := map snd cfuncases in
  concat (map (generate_gfuns_from_expr tn) cfunbods).

Lemma new_gfun_sigs_from_cfuns_in_cdts : forall (p : program) (tn : TypeName),
    gfun_sigs_in_cdts (skeleton_cdts (program_skeleton p)) (map fst (new_gfuns_from_cfuns p tn)).
Proof.
  intros p tn. unfold gfun_sigs_in_cdts. unfold new_gfuns_from_cfuns.
  pose proof (program_cfun_bods_typecheck_g p).
  induction (program_cfun_bods_g p); try apply Forall_nil.
  inversion H; subst; simpl.
  repeat rewrite map_app. rewrite concat_app. rewrite map_app. apply Forall_app.
  - clear - H2. destruct a as [a_qn a_bod]; simpl in *.  destruct H2 as [qn [args [t [_ H_typecheck]]]].
    inversion H_typecheck; subst. clear - H12.
    generalize dependent (map (fun ctor : ScopedName * list TypeName => snd ctor ++ bindings_types) ctorlist).
    generalize dependent (repeat t (length a_bod)).
    induction a_bod; intros; try apply Forall_nil. simpl. rewrite map_app. inversion H12; subst.
    apply Forall_app.
    + clear - H3. apply new_gfun_sigs_from_expr_in_cdts.  exists ctx. exists t0. assumption.
    + eapply IHa_bod. apply H5.
  - apply IHc. assumption.
Qed.

Definition new_gfuns (p : program) (tn : TypeName) : list (gfun_sig * gfun_bod_named) :=
       (new_gfuns_from_funs p tn)
    ++ (new_gfuns_from_gfuns p tn)
    ++ (new_gfuns_from_cfuns p tn).

(**************************************************************************************************)
(* ** Construct the skeleton                                                                      *)
(*                                                                                                *)
(**************************************************************************************************)
Definition new_gfun_sigs (p : program) (tn : TypeName) : list gfun_sig :=
  (skeleton_gfun_sigs_l (program_skeleton p))
    ++ (map fst (new_gfuns p tn)).

Lemma new_gfun_sigs_in_cdts : forall (p : program) (tn : TypeName),
    gfun_sigs_in_cdts (skeleton_cdts (program_skeleton p)) (new_gfun_sigs p tn).
Proof.
  intros p tn; unfold new_gfun_sigs;  apply Forall_app.
  - apply (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)).
  - unfold new_gfuns. repeat rewrite map_app. repeat apply Forall_app.
    + apply new_gfun_sigs_from_funs_in_cdts.
    + apply new_gfun_sigs_from_gfuns_in_cdts.
    + apply new_gfun_sigs_from_cfuns_in_cdts.
Qed.

Remark generate_gfuns_collect_comatches : forall tn a,
  map (fun x => fst (fst x)) (generate_gfuns_from_expr tn a) =
    filter (fun x => eq_TypeName tn (fst x)) (collect_comatch_names a).
Proof with auto.
intros.
set (g:=(fun x => filter (fun x0 => eq_TypeName tn (fst x0)) (collect_comatch_names x))).
set (g2:=(fun x : expr * TypeName => filter (fun x0 => eq_TypeName tn (fst x0)) (collect_comatch_names (fst x)))).
set (g3:=(fun x : ScopedName * expr => filter (fun x0 => eq_TypeName tn (fst x0)) (collect_comatch_names (snd x)))).
induction a using expr_strong_ind;
 try (simpl; rewrite concat_map; rewrite map_map; rewrite Forall_forall in H;
  rewrite filter_concat; rewrite map_map; rewrite map_ext_in with (g:=g); auto);
 try (simpl; rewrite filter_app; rewrite map_app; f_equal; auto;
  rewrite concat_map; rewrite map_map; rewrite Forall_forall in H;
  rewrite filter_concat; rewrite map_map; rewrite map_ext_in with (g:=g))...
- simpl. rewrite filter_app. rewrite map_app. f_equal; auto. rewrite <- concat_app. rewrite concat_map.
  rewrite map_app. rewrite map_map. rewrite map_map.
  rewrite filter_concat. rewrite map_app. rewrite map_map. f_equal.
  rewrite Forall_forall in *. f_equal.
  + rewrite map_ext_in with (g:=g2)...
    intros. destruct a0. simpl. apply H0. change e with (fst (e,t)). apply in_map...
  + rewrite map_map. rewrite map_ext_in with (g:=g3)...
    intros. destruct a0. simpl. apply H. change e with (snd (s,e)). apply in_map...
- rewrite Forall_forall in *. case_eq (eq_TypeName tn (fst n)); intros.
  + simpl. rewrite H1. simpl. f_equal. rewrite <- concat_app. rewrite concat_map.
    rewrite filter_concat. f_equal.
    rewrite map_app. rewrite map_app. rewrite map_map. rewrite map_map. f_equal.
    * rewrite map_map. rewrite map_ext_in with (g:=g2)...
      intros. destruct a. simpl. apply H0. change e with (fst (e,t)). apply in_map...
    * rewrite map_map. rewrite map_ext_in with (g:=g3)...
      intros. destruct a. simpl. apply H. change e with (snd (s,e)). apply in_map...
  + simpl. rewrite H1. simpl. rewrite <- concat_app. rewrite concat_map.
    rewrite filter_concat. f_equal.
    rewrite map_app. rewrite map_app. rewrite map_map. rewrite map_map. f_equal.
    * rewrite map_map. rewrite map_ext_in with (g:=g2)...
      intros. destruct a. simpl. apply H0. change e with (fst (e,t)). apply in_map...
    * rewrite map_map. rewrite map_ext_in with (g:=g3)...
      intros. destruct a. simpl. apply H. change e with (snd (s,e)). apply in_map...
Qed.

Lemma new_gfun_sigs_names_unique : forall (p : program) (tn : TypeName),
    length (skeleton_gfun_sigs_l (program_skeleton p)) = O ->
    gfun_sigs_names_unique (new_gfun_sigs p tn).
Proof with apply generate_gfuns_collect_comatches.
intros. unfold new_gfun_sigs. case_eq (skeleton_gfun_sigs_l (program_skeleton p)); intros.
- simpl. unfold new_gfuns. pose proof (program_comatch_names_unique p).
  apply comatch_names_unique_global_sublist in H1.
  unfold comatch_names_unique in H1. unfold gfun_sigs_names_unique.
  unfold new_gfuns_from_funs. unfold new_gfuns_from_gfuns. unfold new_gfuns_from_cfuns.
  rewrite map_app in H1. rewrite map_app in H1.
  rewrite concat_app in H1. rewrite concat_app in H1. apply unique_app_switch in H1.
  do 2 (rewrite <- concat_app in H1).
  rewrite <- map_app in H1. rewrite <- map_app in H1.
  do 2 (rewrite <- concat_app). rewrite <- map_app. rewrite <- map_app.
  rewrite map_map. rewrite concat_map. rewrite map_map.
  apply filter_unique with (f:=(fun x => eq_TypeName tn (fst x))) in H1.
  rewrite filter_concat in H1. rewrite map_map in H1.
  set (g:=fun x => filter (fun x0 => eq_TypeName tn (fst x0)) (collect_comatch_names x)).
  rewrite map_ext with (g:=g); auto...
- apply (f_equal (length (A:=_))) in H0. rewrite H in H0. simpl in H0. discriminate.
Qed.

Definition lift_comatch_to_skeleton (p : program) (tn : TypeName)
    (Uniq : gfun_sigs_names_unique (new_gfun_sigs p tn)) : skeleton :=
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
      skeleton_cfun_sigs_l := skeleton_cfun_sigs_l old_skeleton;
      skeleton_cfun_sigs_in_dts_l := skeleton_cfun_sigs_in_dts_l old_skeleton;
      skeleton_cfun_sigs_names_unique_l := skeleton_cfun_sigs_names_unique_l old_skeleton;
      (* Generator functions *)
      skeleton_gfun_sigs_g := skeleton_gfun_sigs_g old_skeleton;
      skeleton_gfun_sigs_in_cdts_g := skeleton_gfun_sigs_in_cdts_g old_skeleton;
      skeleton_gfun_sigs_names_unique_g := skeleton_gfun_sigs_names_unique_g old_skeleton;
      (* Only interesting part: =====> *)
      skeleton_gfun_sigs_l := new_gfun_sigs p tn;
      skeleton_gfun_sigs_in_cdts_l := new_gfun_sigs_in_cdts p tn;
      skeleton_gfun_sigs_names_unique_l := Uniq
      (* <===== *)
    |}.

Lemma subterm_generate_gfun : forall sk ctx tn e n bindings_exprs bindings_types ls,
  subterm (E_CoMatch n (combine bindings_exprs bindings_types) ls) e ->
  eq_TypeName tn (fst n) = true ->
  sk // ctx ||- bindings_exprs :: bindings_types ->
  In (n, bindings_types) (map fst (generate_gfuns_from_expr tn e)).
Proof.
intros. set (e' := E_CoMatch n (combine bindings_exprs bindings_types) ls) in *.
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
  + simpl. rewrite map_app. apply in_or_app. left. apply IHsubterm. auto.
  + simpl. rewrite map_app. apply in_or_app. right. rewrite map_app. apply in_or_app. left.
    rewrite concat_map. rewrite <- flat_map_concat_map. rewrite <- map_map.
    rewrite in_flat_map. exists (generate_gfuns_from_expr tn e2). split; auto.
    rewrite in_map_iff. exists e2. split; auto.
  + simpl. rewrite map_app. apply in_or_app. right. rewrite map_app. apply in_or_app. right.
    rewrite concat_map. rewrite <- flat_map_concat_map. rewrite <- map_map.
    rewrite in_flat_map. exists (generate_gfuns_from_expr tn e2). split; auto.
    rewrite in_map_iff. exists e2. split; auto.
  + simpl. rewrite map_app. apply in_or_app. right. rewrite map_app. apply in_or_app. left.
    rewrite concat_map. rewrite <- flat_map_concat_map. rewrite <- map_map.
    rewrite in_flat_map. exists (generate_gfuns_from_expr tn e2). split; auto.
    rewrite in_map_iff. exists e2. split; auto.
  + simpl. rewrite map_app. apply in_or_app. right. rewrite map_app. apply in_or_app. right.
    rewrite concat_map. rewrite <- flat_map_concat_map. rewrite <- map_map.
    rewrite in_flat_map. exists (generate_gfuns_from_expr tn e2). split; auto.
    rewrite in_map_iff. exists e2. split; auto.
  + simpl. rewrite map_app. apply in_or_app. left. apply IHsubterm. auto.
  + simpl. rewrite map_app. apply in_or_app. right. apply IHsubterm. auto.
Qed.

Lemma lift_comatch_to_skeleton_preserves_typing : forall (p : program) (ctxt : ctxt) (e : expr) (t tn : TypeName) Uniq,
    ((program_skeleton p) / ctxt |- e : t) ->
    term_in_original_prog e p ->
    (lift_comatch_to_skeleton p tn Uniq) / ctxt |- (replace_comatches_by_gfun_calls tn e) : t.
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
  - assert (Forall (fun a => term_in_original_prog a p) ls) as Sub. { eapply subterm_term_in_original_prog_GenFunCall; eauto. } rewrite Forall_forall in Sub.
    inversion H0; subst.
    + apply T_GlobalGenFunCall with (argts := argts)...
    + apply T_LocalGenFunCall with (argts := argts)...
      unfold lift_comatch_to_skeleton; simpl. unfold new_gfun_sigs.
      apply in_or_app. left...
  - inversion H1; subst. simpl.
    assert (Forall (fun a => term_in_original_prog a p) bindings_exprs) as Sub.
    { eapply subterm_term_in_original_prog_Match_bs; eauto. symmetry. rewrite <- Nat.eqb_eq. eapply listTypeDeriv_lemma; eauto. }
    rewrite Forall_forall in Sub.
    assert (term_in_original_prog e p) as Sub'. { eapply subterm_term_in_original_prog_Match_e0; eauto. }
    apply T_Match with (bindings_exprs := map (replace_comatches_by_gfun_calls tn0) bindings_exprs) (bindings_types := bindings_types) (ctorlist := ctorlist)...
    + rewrite <- map_combine_fst. apply Forall_map.
      rewrite Forall_forall in *. intros. pose proof (H15 _ H3).
      destruct x. destruct p0. simpl. assumption.
    + assert (Forall (fun a => term_in_original_prog a p) (map snd ls)) as Sub2. { eapply subterm_term_in_original_prog_Match_cases; eauto. } rewrite Forall_forall in Sub2.
      pose proof (listTypeDeriv'_lemma (program_skeleton p) (map snd ls) (repeat t (length ls)) (map
        (fun ctor : ScopedName * list TypeName =>
         snd ctor ++ bindings_types) ctorlist) H16) as H_length;
      rewrite PeanoNat.Nat.eqb_eq in H_length; rewrite map_length;
      clear -H16 H Sub2;
      generalize dependent (repeat t (length ls));
      generalize dependent (map (fun ctor : ScopedName * list TypeName => snd ctor ++ bindings_types) ctorlist);
      induction ls;intros;  destruct l; try (solve [inversion H_length]);
      try (inversion H16; subst; apply ListTypeDeriv'_Nil);
      inversion H16; subst; clear H16;
      inversion H; subst; clear H;
      simpl; apply ListTypeDeriv'_Cons.
      * apply H2; try apply H6. apply Sub2. simpl. left. auto.
      * apply IHls; auto. intros. apply Sub2. simpl. right. auto.
  - inversion H1; subst. simpl. case_eq (eq_TypeName tn (fst n)); intro eqTn.
    + apply T_LocalGenFunCall with (argts:=bindings_types)...
      (* Only interesting case *)
      * simpl. unfold new_gfun_sigs. apply in_or_app. right.
        unfold new_gfuns. repeat (rewrite map_app).
        destruct H2; [|destruct H2]; rewrite Exists_exists in H2; destruct H2 as [x [xIn xSub]].
        -- apply in_or_app. left. unfold new_gfuns_from_funs.
           rewrite concat_map. rewrite map_map. rewrite map_map.
           rewrite <- flat_map_concat_map. rewrite in_flat_map.
           exists x. split; auto. eapply subterm_generate_gfun; eauto.
        -- apply in_or_app. right. apply in_or_app. right. unfold new_gfuns_from_cfuns.
           rewrite concat_map. rewrite map_map. rewrite map_map.
           rewrite <- flat_map_concat_map. rewrite in_flat_map.
           rewrite Exists_exists in xSub. destruct xSub.
           exists x0. destruct H2. split.
           ++ rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x. split; auto.
           ++ eapply subterm_generate_gfun; eauto.
        -- apply in_or_app. right. apply in_or_app. left. unfold new_gfuns_from_gfuns.
           rewrite concat_map. rewrite map_map. rewrite map_map.
           rewrite <- flat_map_concat_map. rewrite in_flat_map.
           rewrite Exists_exists in xSub. destruct xSub.
           exists x0. destruct H2. split.
           ++ rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x. split; auto.
           ++ eapply subterm_generate_gfun; eauto.
      * assert (Forall (fun a => term_in_original_prog a p) bindings_exprs) as Sub.
        { eapply subterm_term_in_original_prog_CoMatch_bs; eauto. symmetry. rewrite <- Nat.eqb_eq. eapply listTypeDeriv_lemma; eauto. }
        rewrite Forall_forall in Sub.
        rewrite map_ext with (g:=fst) in H0; auto.
        clear - H7 H0 Sub;
        pose proof (listTypeDeriv_lemma (program_skeleton p) ctxt bindings_exprs bindings_types H7) as H_length;
        rewrite PeanoNat.Nat.eqb_eq in H_length; generalize dependent bindings_types;
        induction bindings_exprs;intros;  destruct bindings_types; try (solve [inversion H_length]);
        try apply ListTypeDeriv_Nil;
        inversion H7; subst; clear H7;
        inversion H0; subst; clear H0;
        apply ListTypeDeriv_Cons; try auto using in_eq, in_cons.
    + assert (Forall (fun a => term_in_original_prog a p) bindings_exprs) as Sub.
      { eapply subterm_term_in_original_prog_CoMatch_bs; eauto. symmetry. rewrite <- Nat.eqb_eq. eapply listTypeDeriv_lemma; eauto. }
      rewrite Forall_forall in Sub.
      apply T_CoMatch with (bindings_exprs := map (replace_comatches_by_gfun_calls tn) bindings_exprs) (bindings_types := bindings_types) (dtorlist := dtorlist)...
      * rewrite <- map_combine_fst. apply Forall_map.
        rewrite Forall_forall in *. intros. pose proof (H12 _ H3).
        destruct x. destruct p0. simpl. assumption.
      * assert (Forall (fun a => term_in_original_prog a p) (map snd ls)) as Sub2. { eapply subterm_term_in_original_prog_CoMatch_cocases; eauto. } rewrite Forall_forall in Sub2.
        pose proof (listTypeDeriv'_lemma (program_skeleton p) (map snd ls) (map snd dtorlist) (map
          (fun dtor : ScopedName * list TypeName * TypeName =>
           snd (fst dtor) ++ bindings_types) dtorlist) H13) as H_length;
        rewrite PeanoNat.Nat.eqb_eq in H_length;
        clear -H13 H Sub2;
        generalize dependent (map snd dtorlist);
        generalize dependent (map (fun dtor : ScopedName * list TypeName * TypeName => snd (fst dtor) ++ bindings_types) dtorlist);
        induction ls;intros;  destruct l; try (solve [inversion H_length]);
        try (inversion H13; subst; apply ListTypeDeriv'_Nil);
        inversion H13; subst; clear H13;
        inversion H; subst; clear H;
        simpl; apply ListTypeDeriv'_Cons.
        -- apply H2; try apply H6. apply Sub2. simpl. left. auto.
        -- apply IHls; auto. intros. apply Sub2. simpl. right. auto.
  - inversion H; subst.
    assert (term_in_original_prog e1 p) as Sub1. { eapply subterm_term_in_original_prog_Let_e1; eauto. }
    assert (term_in_original_prog e2 p) as Sub2. { eapply subterm_term_in_original_prog_Let_e2; eauto. }
    apply T_Let with (t1 := t1)...
Qed.

Corollary new_funbods_typecheck : forall p tn Uniq,
  fun_bods_typecheck (program_skeleton p) (program_fun_bods p) ->
  fun_bods_typecheck (lift_comatch_to_skeleton p tn Uniq)
    (map (fun x : Name * expr => (fst x, replace_comatches_by_gfun_calls tn (snd x))) (program_fun_bods p)).
Proof.
intros. unfold fun_bods_typecheck in *. rewrite Forall_forall in *. intros.
rewrite in_map_iff in H0. destruct H0. destruct H0.
pose proof (H x0 H1). destruct H2. destruct H2. destruct H2. exists x1. exists x2. exists x3.
destruct H2. split.
- unfold UtilsSkeleton.lookup_fun_sig in *. simpl.
  inversion H0; subst. simpl. assumption.
- inversion H0; subst. apply lift_comatch_to_skeleton_preserves_typing; auto.
  unfold term_in_original_prog. left. rewrite Exists_exists. exists x0. split; auto. apply Sub_Refl.
Qed.

Require Import Coq.omega.Omega.

Corollary new_cfunbods_g_typecheck : forall p tn Uniq,
  cfun_bods_g_typecheck (program_skeleton p) (program_cfun_bods_g p) ->
  cfun_bods_g_typecheck (lift_comatch_to_skeleton p tn Uniq)
    (map (fun x : QName * list (ScopedName * expr) =>
      (fst x, map (fun y : ScopedName * expr => (fst y, replace_comatches_by_gfun_calls tn (snd y)))
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
    * apply lift_comatch_to_skeleton_preserves_typing; auto.
      unfold term_in_original_prog. right. left. rewrite Exists_exists. exists (q, l). split; auto.
      rewrite Exists_exists. simpl. exists a.
      assert (In a l). { clear -H0. destruct H0. rewrite H. apply in_or_app. right. simpl. left. auto. }
      split; auto. apply Sub_Refl.
    * apply IHl0; auto. destruct H0. exists (x ++ [a]). rewrite <- app_assoc. simpl. auto.
Qed.

Corollary new_gfunbods_g_typecheck : forall p tn Uniq,
  gfun_bods_g_typecheck (program_skeleton p) (program_gfun_bods_g p) ->
  gfun_bods_g_typecheck (lift_comatch_to_skeleton p tn Uniq)
    (map (fun x : QName * list (ScopedName * expr) =>
      (fst x, map (fun y : ScopedName * expr => (fst y, replace_comatches_by_gfun_calls tn (snd y)))
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
    * apply lift_comatch_to_skeleton_preserves_typing; auto.
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
  has_all_fun_bods (skeleton_fun_sigs (lift_comatch_to_skeleton p tn Uniq))
    (map (fun x : Name * expr => (fst x, replace_comatches_by_gfun_calls tn (snd x)))
       (program_fun_bods p)).
Proof.
intros. simpl. unfold has_all_fun_bods in *. rewrite map_map. simpl. auto.
Qed.

Fact new_has_all_cfunbods_g : forall p tn Uniq,
  has_all_cfun_bods (skeleton_cfun_sigs_g (program_skeleton p)) (program_cfun_bods_g p) ->
  has_all_cfun_bods (skeleton_cfun_sigs_g (lift_comatch_to_skeleton p tn Uniq))
    (map (fun x : QName * list (ScopedName * expr) =>
      (fst x, map (fun y : ScopedName * expr => (fst y, replace_comatches_by_gfun_calls tn (snd y)))
                  (snd x)))
      (program_cfun_bods_g p)).
Proof.
intros. simpl. unfold has_all_cfun_bods in *. rewrite map_map. simpl. auto.
Qed.

Fact new_has_all_cfunbods_l : forall p tn Uniq,
 length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn Uniq)) = 0 ->
 has_all_cfun_bods (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn Uniq)) [].
Proof.
intros. unfold has_all_cfun_bods.
case_eq (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn Uniq)); intros; auto.
rewrite H0 in H. simpl in H. discriminate.
Qed.

Fact new_has_all_gfunbods_g : forall p tn Uniq,
  has_all_gfun_bods (skeleton_gfun_sigs_g (program_skeleton p)) (program_gfun_bods_g p) ->
  has_all_gfun_bods (skeleton_gfun_sigs_g (lift_comatch_to_skeleton p tn Uniq))
    (map (fun x : QName * list (ScopedName * expr) =>
      (fst x, map (fun y : ScopedName * expr => (fst y, replace_comatches_by_gfun_calls tn (snd y)))
                  (snd x)))
      (program_gfun_bods_g p)).
Proof.
intros. simpl. unfold has_all_gfun_bods in *. rewrite map_map. simpl. auto.
Qed.

Definition new_gfun_bods_l (p : program) (tn : TypeName) : gfun_bods :=
  map snd (flat_map (generate_gfuns_from_expr tn) (map snd (program_fun_bods p)))
  ++ map snd (flat_map (generate_gfuns_from_expr tn) (map snd (flat_map snd (program_gfun_bods_g p))))
  ++ map snd (flat_map (generate_gfuns_from_expr tn) (map snd (flat_map snd (program_cfun_bods_g p)))).

Fact new_has_all_gfunbods_l : forall p tn Uniq,
  length (skeleton_gfun_sigs_l (program_skeleton p)) = O ->
  has_all_gfun_bods (skeleton_gfun_sigs_l (lift_comatch_to_skeleton p tn Uniq)) (new_gfun_bods_l p tn).
Proof.
intros. simpl. unfold has_all_gfun_bods. unfold new_gfun_sigs.
assert (skeleton_gfun_sigs_l (program_skeleton p) = []).
{ destruct (skeleton_gfun_sigs_l (program_skeleton p)); auto. simpl in H. discriminate. }
rewrite H0. clear H H0. simpl. unfold new_gfuns. unfold new_gfun_bods_l.
repeat (rewrite map_app). repeat f_equal.
- unfold new_gfuns_from_funs. rewrite <- flat_map_concat_map.
  generalize (map snd (program_fun_bods p)). induction l; auto.
  simpl. repeat (rewrite map_app). rewrite IHl. f_equal. clear.
  unfold fun_bod in a. pose proof (generate_gfuns_from_expr_names_match tn a).
  induction H; auto. simpl. f_equal; auto.
- unfold new_gfuns_from_gfuns. repeat (rewrite <- flat_map_concat_map).
  unfold gfun_bod. generalize (map snd (flat_map snd (program_gfun_bods_g p))). induction l; auto.
  simpl. repeat (rewrite map_app). rewrite IHl. f_equal. clear.
  pose proof (generate_gfuns_from_expr_names_match tn a).
  induction H; auto. simpl. f_equal; auto.
- unfold new_gfuns_from_cfuns. repeat (rewrite <- flat_map_concat_map).
  unfold cfun_bod. generalize (map snd (flat_map snd (program_cfun_bods_g p))). induction l; auto.
  simpl. repeat (rewrite map_app). rewrite IHl. f_equal. clear.
  pose proof (generate_gfuns_from_expr_names_match tn a).
  induction H; auto. simpl. f_equal; auto.
Qed.

Lemma term_in_original_prog_name_eq : forall p tn (x0 : gfun_sig * gfun_bod_named) (x : expr) s e s0 (l : list TypeName) t,
  In x0 (generate_gfuns_from_expr tn x) ->
  In (s, e, (s0, l, t))
      (combine (snd (snd x0))
         (filter
            (fun x : ScopedName * list TypeName * TypeName =>
             let (y, _) := x in
             let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd x0))))
            (skeleton_dtors (program_skeleton p)))) ->
  term_in_original_prog x p ->
  s = s0.
Proof.
intros p tn x0 x s e s0 l t xIn H H0.
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
  apply in_app_or in xIn. destruct xIn; [| apply in_app_or in H3; destruct H3].
  + pose proof (subterm_term_in_original_prog_Match_e0 _ _ _ _ _ _ _ H0). auto.
  + pose proof (subterm_term_in_original_prog_Match_bs _ _ _ _ _ _ _ Len H0).
    rewrite Forall_forall in H2.
    rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
    destruct H3. destruct H3. apply H2 with (x:=fst x1); auto.
    * rewrite in_map_iff. eexists. split; eauto. destruct x1. auto.
    * rewrite Forall_forall in H4. apply H4. rewrite <- map_fst_combine with (l2:=es2); auto.
      rewrite in_map_iff. exists x1. split; auto.
  + pose proof (subterm_term_in_original_prog_Match_cases _ _ _ _ _ _ _ H0).
    rewrite Forall_forall in H1.
    rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
    destruct H3. destruct H3. apply H1 with (x:=snd x1); auto.
    * rewrite in_map_iff. eexists. split; eauto. destruct x1. auto.
    * rewrite Forall_forall in H4. apply H4. apply in_map. auto.
- assert (exists es1 es2, length es1 = length es2 /\ es = combine es1 es2) as CombineEq.
  { clear. exists (fst (split es)). exists (snd (split es)). split.
    - rewrite split_length_l. rewrite split_length_r. auto.
    - symmetry. pose proof (split_combine es). destruct (split es). auto.
  }
  destruct CombineEq as [es1 [es2 [Len Eq]]]. subst.
  case_eq (eq_TypeName tn (fst n)); intros.
  + rewrite H3 in xIn. apply in_app_or in xIn.
    destruct xIn; [| apply in_app_or in H4; destruct H4].
    * unfold In in H4. destruct H4; [| exfalso; auto]. rewrite <- H4 in H. clear - H H0.
      simpl in H. apply term_in_original_prog_typechecks in H0. do 2 (destruct H0).
      inversion H0; subst. unfold lookup_dtors in H8.
      case_eq (filter (eq_TypeName (fst n)) (skeleton_cdts (program_skeleton p))); intros;
       rewrite H1 in H8; try discriminate.
      inversion H8; subst. rewrite Forall_forall in H10.
      rewrite <- map_fst_f_combine in H. rewrite in_map_iff in H. do 2 (destruct H).
      pose proof (H10 _ H2). destruct x0. destruct p0. destruct p1. destruct p0.
      inversion H; subst. auto.
    * pose proof (subterm_term_in_original_prog_CoMatch_bs _ _ _ _ _ Len H0).
      rewrite Forall_forall in H2.
      rewrite <- flat_map_concat_map in H4. rewrite in_flat_map in H4.
      destruct H4. destruct H4. apply H2 with (x:=fst x); auto.
      -- rewrite in_map_iff. eexists. split; eauto. destruct x. auto.
      -- rewrite Forall_forall in H5. apply H5. rewrite <- map_fst_combine with (l2:=es2); auto.
         rewrite in_map_iff. exists x. split; auto.
    * pose proof (subterm_term_in_original_prog_CoMatch_cocases _ _ _ _ _ H0).
      rewrite Forall_forall in H1.
      rewrite <- flat_map_concat_map in H4. rewrite in_flat_map in H4.
      destruct H4. destruct H4. apply H1 with (x:=snd x); auto.
      -- rewrite in_map_iff. eexists. split; eauto. destruct x. auto.
      -- rewrite Forall_forall in H5. apply H5. apply in_map. auto.
  + rewrite H3 in xIn. apply in_app_or in xIn.
    destruct xIn; [| apply in_app_or in H4; destruct H4].
    * inversion H4.
    * pose proof (subterm_term_in_original_prog_CoMatch_bs _ _ _ _ _ Len H0).
      rewrite Forall_forall in H2.
      rewrite <- flat_map_concat_map in H4. rewrite in_flat_map in H4.
      destruct H4. destruct H4. apply H2 with (x:=fst x); auto.
      -- rewrite in_map_iff. eexists. split; eauto. destruct x. auto.
      -- rewrite Forall_forall in H5. apply H5. rewrite <- map_fst_combine with (l2:=es2); auto.
         rewrite in_map_iff. exists x. split; auto.
    * pose proof (subterm_term_in_original_prog_CoMatch_cocases _ _ _ _ _ H0).
      rewrite Forall_forall in H1.
      rewrite <- flat_map_concat_map in H4. rewrite in_flat_map in H4.
      destruct H4. destruct H4. apply H1 with (x:=snd x); auto.
      -- rewrite in_map_iff. eexists. split; eauto. destruct x. auto.
      -- rewrite Forall_forall in H5. apply H5. apply in_map. auto.
- apply in_app_or in xIn. destruct xIn.
  + apply IHx1; auto. eapply subterm_term_in_original_prog_Let_e1. eauto.
  + apply IHx2; auto. eapply subterm_term_in_original_prog_Let_e2. eauto.
Qed.

Corollary term_in_fun_bod_name_eq : forall p tn (x0 : gfun_sig * gfun_bod_named) (x : expr) s e s0 (l : list TypeName) t,
  In x0 (generate_gfuns_from_expr tn x) ->
  In (s, e, (s0, l, t))
      (combine (snd (snd x0))
         (filter
            (fun x : ScopedName * list TypeName * TypeName =>
             let (y, _) := x in
             let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd x0))))
            (skeleton_dtors (program_skeleton p)))) ->
  (exists x' : expr, subterm x x' /\ In x' (map snd (program_fun_bods p))) ->
  s = s0.
Proof.
intros p tn x0 x s e s0 l t xIn H H0.
assert (term_in_original_prog x p).
{ unfold term_in_original_prog. left. rewrite Exists_exists.
  destruct H0. destruct H0. rewrite in_map_iff in H1. destruct H1. destruct H1. subst.
  exists x2. split; auto.
}
eapply term_in_original_prog_name_eq; eauto.
Qed.

Corollary term_in_gfun_bod_name_eq : forall p  tn (x0 : gfun_sig * gfun_bod_named) (x : expr) s e s0 (l : list TypeName) t,
  In x0 (generate_gfuns_from_expr tn x) ->
  In (s, e, (s0, l, t))
      (combine (snd (snd x0))
         (filter
            (fun x : ScopedName * list TypeName * TypeName =>
             let (y, _) := x in
             let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd x0))))
            (skeleton_dtors (program_skeleton p)))) ->
  (exists x' : expr, subterm x x' /\ In x' (map snd (flat_map snd (program_gfun_bods_g p)))) ->
  s = s0.
Proof.
intros p tn x0 x s e s0 l t xIn H H0.
assert (term_in_original_prog x p).
{ unfold term_in_original_prog. right. right. rewrite Exists_exists.
  destruct H0. destruct H0. rewrite in_map_iff in H1. destruct H1. destruct H1. subst.
  rewrite in_flat_map in H2. destruct H2. destruct H1.
  exists x1. split; auto. rewrite Exists_exists. exists x2. split; auto.
}
eapply term_in_original_prog_name_eq; eauto.
Qed.

Lemma term_in_cfun_bod_name_eq : forall p  tn (x0 : gfun_sig * gfun_bod_named) (x : expr) s e s0 (l : list TypeName) t,
  In x0 (generate_gfuns_from_expr tn x) ->
  In (s, e, (s0, l, t))
      (combine (snd (snd x0))
         (filter
            (fun x : ScopedName * list TypeName * TypeName =>
             let (y, _) := x in
             let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd x0))))
            (skeleton_dtors (program_skeleton p)))) ->
  (exists x' : expr, subterm x x' /\ In x' (map snd (flat_map snd (program_cfun_bods_g p)))) ->
  s = s0.
Proof.
intros p tn x0 x s e s0 l t xIn H H0.
assert (term_in_original_prog x p).
{ unfold term_in_original_prog. right. left. rewrite Exists_exists.
  destruct H0. destruct H0. rewrite in_map_iff in H1. destruct H1. destruct H1. subst.
  rewrite in_flat_map in H2. destruct H2. destruct H1.
  exists x1. split; auto. rewrite Exists_exists. exists x2. split; auto.
}
eapply term_in_original_prog_name_eq; eauto.
Qed.

Lemma generates_from_comatch : forall p tn (x0 : gfun_sig * gfun_bod_named) (e : expr) info,
  term_in_original_prog e p ->
  In x0 (generate_gfuns_from_expr tn e) ->
  (In info
       (flat_map (generate_gfuns_from_expr tn)
          (map snd (program_fun_bods p)) ++
        flat_map (generate_gfuns_from_expr tn)
          (map snd (flat_map snd (program_gfun_bods_g p))) ++
        flat_map (generate_gfuns_from_expr tn)
          (map snd (flat_map snd (program_cfun_bods_g p)))) /\
    fst info = fst x0) ->
  exists (x' : list expr) (sn : Name) (bs_es : list expr),
    length bs_es = length (snd (fst info)) /\
    map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd x0)) /\
    term_in_original_prog
      (E_CoMatch (fst (fst (snd x0)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd x0))) x')) p.
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
  apply in_app_or in H0. destruct H0; [|apply in_app_or in H0; destruct H0].
  + apply IHe; auto. eapply subterm_term_in_original_prog_Match_e0; eauto.
  + rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
    rewrite Forall_forall in H3. apply H3 with (x:=fst x); auto.
    * apply in_map. auto.
    * pose proof (subterm_term_in_original_prog_Match_bs _ _ _ _ _ _ _ Len H).
      rewrite Forall_forall in H5. apply H5. destruct x. simpl. eapply in_combine_l. eauto.
  + rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
    rewrite Forall_forall in H2. apply H2 with (x:=snd x); auto.
    * apply in_map. auto.
    * pose proof (subterm_term_in_original_prog_Match_cases _ _ _ _ _ _ _ H).
      rewrite Forall_forall in H5. apply H5. apply in_map. auto.
- assert (exists es1 es2, length es1 = length es2 /\ es = combine es1 es2) as CombineEq.
  { clear. exists (fst (split es)). exists (snd (split es)). split.
    - rewrite split_length_l. rewrite split_length_r. auto.
    - symmetry. pose proof (split_combine es). destruct (split es). auto.
  }
  destruct CombineEq as [es1 [es2 [Len Eq]]].
  case_eq (eq_TypeName tn (fst n)); intros.
  + rewrite H4 in H0. apply in_app_or in H0. destruct H0; [|apply in_app_or in H0; destruct H0].
    * inversion H0; [|exfalso; auto]. rewrite <- H5. simpl.
      exists (map snd ls). exists (snd n). exists (map fst es).
      assert (snd (fst info) = map snd es).
      { inversion H5; subst. simpl in *. clear - H H1. destruct H1. rewrite H1. auto. }
      split; try split.
      -- rewrite H6. rewrite map_length. rewrite map_length. auto.
      -- rewrite map_map. rewrite map_map. simpl. auto.
      -- destruct n. simpl in *. rewrite H6. rewrite map_map. simpl.
         rewrite <- combine_fst_snd. rewrite <- combine_fst_snd. auto.
    * rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
      rewrite Forall_forall in H3. apply H3 with (x:=fst x); auto.
      -- apply in_map. auto.
      -- subst. pose proof (subterm_term_in_original_prog_CoMatch_bs _ _ _ _ _ Len H).
         rewrite Forall_forall in H6. apply H6. destruct x. simpl. eapply in_combine_l. eauto.
    * rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
      rewrite Forall_forall in H2. apply H2 with (x:=snd x); auto.
      -- apply in_map. auto.
      -- subst. pose proof (subterm_term_in_original_prog_CoMatch_cocases _ _ _ _ _ H).
         rewrite Forall_forall in H6. apply H6. destruct x. apply in_map. auto.
  + rewrite H4 in H0. apply in_app_or in H0. destruct H0; [|apply in_app_or in H0; destruct H0].
    * inversion H0.
    * rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
      rewrite Forall_forall in H3. apply H3 with (x:=fst x); auto.
      -- apply in_map. auto.
      -- subst. pose proof (subterm_term_in_original_prog_CoMatch_bs _ _ _ _ _ Len H).
         rewrite Forall_forall in H6. apply H6. destruct x. simpl. eapply in_combine_l. eauto.
    * rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. destruct H0. destruct H0.
      rewrite Forall_forall in H2. apply H2 with (x:=snd x); auto.
      -- apply in_map. auto.
      -- subst. pose proof (subterm_term_in_original_prog_CoMatch_cocases _ _ _ _ _ H).
         rewrite Forall_forall in H6. apply H6. destruct x. apply in_map. auto.
- apply in_app_or in H0. destruct H0.
  + apply IHe1; auto. eapply subterm_term_in_original_prog_Let_e1; eauto.
  + apply IHe2; auto. eapply subterm_term_in_original_prog_Let_e2; eauto.
Qed.


Lemma fun_generates_from_comatch :
forall p tn (x0 : gfun_sig * gfun_bod_named) (x1 : Name * fun_bod) info,
  In x1 (program_fun_bods p) ->
  In x0 (generate_gfuns_from_expr tn (snd x1)) ->
  In info
           (flat_map (generate_gfuns_from_expr tn)
              (map snd (program_fun_bods p)) ++
            flat_map (generate_gfuns_from_expr tn)
              (map snd (flat_map snd (program_gfun_bods_g p))) ++
            flat_map (generate_gfuns_from_expr tn)
              (map snd (flat_map snd (program_cfun_bods_g p)))) ->
  fst info = fst x0 ->
  exists (x' : list expr) (sn : Name) (bs_es : list expr),
    length bs_es = length (snd (fst info)) /\
    map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd x0)) /\
    term_in_original_prog
      (E_CoMatch (fst (fst (snd x0)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd x0))) x')) p.
Proof.
intros. destruct x1. simpl in *. apply generates_from_comatch with (e:=f); auto.
unfold term_in_original_prog. left. rewrite Exists_exists. exists (n,f). split; auto.
apply Sub_Refl.
Qed.

Lemma gfun_generates_from_comatch :
forall p tn (x0 : gfun_sig * gfun_bod_named) (x1 : ScopedName * expr) info,
  In x1 (flat_map snd (program_gfun_bods_g p)) ->
  In x0 (generate_gfuns_from_expr tn (snd x1)) ->
  In info
           (flat_map (generate_gfuns_from_expr tn)
              (map snd (program_fun_bods p)) ++
            flat_map (generate_gfuns_from_expr tn)
              (map snd (flat_map snd (program_gfun_bods_g p))) ++
            flat_map (generate_gfuns_from_expr tn)
              (map snd (flat_map snd (program_cfun_bods_g p)))) ->
  fst info = fst x0 ->
  exists (x' : list expr) (sn : Name) (bs_es : list expr),
    length bs_es = length (snd (fst info)) /\
    map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd x0)) /\
    term_in_original_prog
      (E_CoMatch (fst (fst (snd x0)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd x0))) x')) p.
Proof.
intros. rewrite in_flat_map in H. destruct H. destruct H. apply generates_from_comatch with (e:=snd x1); auto.
unfold term_in_original_prog. right. right. rewrite Exists_exists. exists x. split; auto.
rewrite Exists_exists. exists x1. split; auto. apply Sub_Refl.
Qed.

Lemma cfun_generates_from_comatch :
forall p tn (x0 : gfun_sig * gfun_bod_named) (x1 : ScopedName * expr) info,
  In x1 (flat_map snd (program_cfun_bods_g p)) ->
  In x0 (generate_gfuns_from_expr tn (snd x1)) ->
  In info
           (flat_map (generate_gfuns_from_expr tn)
              (map snd (program_fun_bods p)) ++
            flat_map (generate_gfuns_from_expr tn)
              (map snd (flat_map snd (program_gfun_bods_g p))) ++
            flat_map (generate_gfuns_from_expr tn)
              (map snd (flat_map snd (program_cfun_bods_g p)))) ->
  fst info = fst x0 ->
  exists (x' : list expr) (sn : Name) (bs_es : list expr),
    length bs_es = length (snd (fst info)) /\
    map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd x0)) /\
    term_in_original_prog
      (E_CoMatch (fst (fst (snd x0)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd x0))) x')) p.
Proof.
intros. rewrite in_flat_map in H. destruct H. destruct H. apply generates_from_comatch with (e:=snd x1); auto.
unfold term_in_original_prog. right. left. rewrite Exists_exists. exists x. split; auto.
rewrite Exists_exists. exists x1. split; auto. apply Sub_Refl.
Qed.

Fact info_in_fun_bods : forall p tn x0 info,
  In x0 (program_fun_bods p) ->
  In info (generate_gfuns_from_expr tn (snd x0)) ->
  In info
    (flat_map (generate_gfuns_from_expr tn) (map snd (program_fun_bods p)) ++
     flat_map (generate_gfuns_from_expr tn)
       (map snd (flat_map snd (program_gfun_bods_g p))) ++
     flat_map (generate_gfuns_from_expr tn)
       (map snd (flat_map snd (program_cfun_bods_g p)))).
Proof.
intros. apply in_or_app. left. rewrite in_flat_map. destruct x0. simpl in *.
exists f. apply (in_map snd) in H. simpl in H. split; auto.
Qed.

Fact info_in_gfun_bods : forall p tn x0 info,
  In x0 (flat_map snd (program_gfun_bods_g p)) ->
  In info (generate_gfuns_from_expr tn (snd x0)) ->
  In info
    (flat_map (generate_gfuns_from_expr tn) (map snd (program_fun_bods p)) ++
     flat_map (generate_gfuns_from_expr tn)
       (map snd (flat_map snd (program_gfun_bods_g p))) ++
     flat_map (generate_gfuns_from_expr tn)
       (map snd (flat_map snd (program_cfun_bods_g p)))).
Proof.
intros. apply in_or_app. right. apply in_or_app. left.
rewrite in_flat_map. destruct x0. simpl in *.
exists e. apply (in_map snd) in H. simpl in H. split; auto.
Qed.

Fact info_in_cfun_bods : forall p tn x0 info,
  In x0 (flat_map snd (program_cfun_bods_g p)) ->
  In info (generate_gfuns_from_expr tn (snd x0)) ->
  In info
    (flat_map (generate_gfuns_from_expr tn) (map snd (program_fun_bods p)) ++
     flat_map (generate_gfuns_from_expr tn)
       (map snd (flat_map snd (program_gfun_bods_g p))) ++
     flat_map (generate_gfuns_from_expr tn)
       (map snd (flat_map snd (program_cfun_bods_g p)))).
Proof.
intros. apply in_or_app. right. apply in_or_app. right.
rewrite in_flat_map. destruct x0. simpl in *.
exists e. apply (in_map snd) in H. simpl in H. split; auto.
Qed.

Fact unique_sig_lookup : forall (l : list (QName * list TypeName)) sig,
  In sig l ->
  unique (map fst l) ->
  find (fun sig0 : QName * list TypeName => eq_QName (fst sig) (fst sig0)) l =
    Some sig.
Proof.
intros. induction l; inversion H.
- rewrite H1. simpl. rewrite eq_QName_refl. auto.
- simpl. inversion H0; subst. case_eq (eq_QName (fst sig) (fst a)); intros.
  + rewrite eq_QName_eq in H2. apply (in_map fst) in H1. rewrite H2 in H1. exfalso. apply H4. auto.
  + apply IHl; auto.
Qed.

Corollary new_gfun_bods_l_typecheck: forall p tn Uniq,
  length (skeleton_gfun_sigs_l (program_skeleton p)) = O ->
  gfun_bods_l_typecheck (lift_comatch_to_skeleton p tn Uniq) (new_gfun_bods_l p tn).
Proof.
intros. unfold gfun_bods_l_typecheck. rewrite Forall_forall. intros.
pose proof (new_has_all_gfunbods_l p tn Uniq H) as Aux. simpl in Aux.
unfold has_all_gfun_bods in Aux.
exists (fst x).
pose proof H0 as AllInfo. unfold new_gfun_bods_l in AllInfo. repeat (rewrite <- map_app in AllInfo).
rewrite in_map_iff in AllInfo. destruct AllInfo as [info [infoEq infoIn]]. subst.
exists (snd (fst info)).
unfold lookup_gfun_sig_l. unfold lookup_gfun_sig_x. simpl. split.
- pose proof (skeleton_gfun_sigs_names_unique_l (lift_comatch_to_skeleton p tn Uniq)). simpl in H1.
  unfold gfun_sigs_names_unique in H1.
  apply (in_map fst) in H0. unfold gfun_bod in *. rewrite <- Aux in H0.
  assert (In (fst info) (new_gfun_sigs p tn)).
  { clear - infoIn H. unfold new_gfun_sigs. case_eq (skeleton_gfun_sigs_l (program_skeleton p)); intros.
    - simpl. unfold new_gfuns. apply in_map.
      unfold new_gfuns_from_funs. unfold new_gfuns_from_gfuns. unfold new_gfuns_from_cfuns.
      repeat (rewrite <- flat_map_concat_map). auto.
    - apply (f_equal (length (A:=_))) in H0. rewrite H in H0. simpl in H0. discriminate.
  }
  assert (fst (snd info) = fst (fst info)).
  { clear - H Aux infoIn. unfold new_gfun_sigs in Aux. case_eq (skeleton_gfun_sigs_l (program_skeleton p)); intros.
    - rewrite H0 in Aux. simpl in Aux. unfold new_gfuns in Aux. unfold new_gfun_bods_l in Aux.
      unfold new_gfuns_from_funs in Aux. unfold new_gfuns_from_gfuns in Aux. unfold new_gfuns_from_cfuns in Aux.
      repeat (rewrite <- flat_map_concat_map in Aux). repeat (rewrite <- map_app in Aux).
      rewrite combine_fst_snd in infoIn.
      apply (in_map (fun x => (fst (fst x),snd x))) in infoIn.
      rewrite map_fst_f_combine in infoIn.
      apply (in_map (fun x => (fst x, fst (snd x)))) in infoIn.
      rewrite map_snd_f_combine in infoIn.
      unfold gfun_bods in *. unfold gfun_bod in *.
      unfold cfun_bods in *. unfold cfun_bod in *.
      rewrite Aux in infoIn. simpl in infoIn.
      evar (q_dummy : QName). pose proof (In_nth _ _ (q_dummy, q_dummy) infoIn).
      do 2 (destruct H1). destruct info. simpl in *. destruct g. destruct g0. simpl in *.
      rewrite combine_nth in H2.
      + inversion H2. auto.
      + rewrite map_length. rewrite map_length. auto.
    - apply (f_equal (length (A:=_))) in H0. rewrite H in H0. simpl in H0. discriminate.
  }
  unfold gfun_bod in *. rewrite H3. rewrite <- surjective_pairing. apply unique_sig_lookup; auto.
- eapply T_CoMatch with (bindings_exprs := map fst (index_list 0 (snd (fst info)))) (bindings_types := snd (fst info)).
  + clear. destruct info. simpl. destruct g. simpl. generalize 0. induction l; intros; auto.
    simpl. f_equal. apply IHl.
  + apply index_list_typechecks with (r := []); reflexivity.
  + unfold lift_comatch_to_skeleton. unfold lookup_dtors. simpl.
    case_eq (filter (eq_TypeName (fst (fst (snd info)))) (skeleton_cdts (program_skeleton p))); intros.
    2: { unfold gfun_bod in *. rewrite H1. eauto. }
    pose proof (in_map fst _ _ H0).
    unfold gfun_bod in *. pose proof H2 as H3. rewrite <- Aux in H3.
    unfold new_gfun_sigs in H3.
    assert (skeleton_gfun_sigs_l (program_skeleton p) = []).
    { case_eq (skeleton_gfun_sigs_l (program_skeleton p)); intros; auto. rewrite H4 in H. simpl in H. discriminate. }
    rewrite H4 in H3. simpl in H3. unfold new_gfuns in H3. rewrite map_app in H3. rewrite map_app in H3.
    apply in_app_or in H3. destruct H3; [| repeat (rewrite map_app in H3); apply in_app_or in H3; destruct H3];
    [pose proof (new_gfun_sigs_from_funs_in_cdts p tn)
    |pose proof (new_gfun_sigs_from_gfuns_in_cdts p tn)
    |pose proof (new_gfun_sigs_from_cfuns_in_cdts p tn)];
    unfold gfun_sigs_in_cdts in H5;
    rewrite in_map_iff in H3; destruct H3; destruct H3; rewrite Forall_forall in H5;
    pose proof (H5 _ H6); unfold QName in H3; rewrite H3 in H7;
    assert (eq_TypeName (fst (fst x)) (fst (fst x)) = true); try apply eq_TypeName_refl;
    pose proof (conj H7 H8); rewrite <- H3 in H9; rewrite <- filter_In in H9; apply in_split in H9;
    destruct H9; destruct H9; unfold gfun_bod in *; unfold QName in *;
    rewrite <- H3 in H1; rewrite H9 in H1; symmetry in H1; apply app_cons_not_nil in H1;
    exfalso; auto.
  + clear -H0. rewrite Forall_forall. intros. destruct x. destruct p0. destruct p1. destruct p0.
    unfold new_gfun_bods_l in H0.
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
      assert (exists x' sn bs_es, length bs_es = length (snd (fst info)) /\ map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd info)) /\
        term_in_original_prog (E_CoMatch (fst (fst (snd info)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd info))) x')) p) as Aux0.
      { rewrite in_map_iff in H. do 2 (destruct H). rewrite <- H in H1.
        eapply fun_generates_from_comatch; eauto.
        eapply info_in_fun_bods; eauto.
      }
      destruct Aux0 as [x2 Aux0].
      assert (Forall (fun e => term_in_original_prog e p) x2 /\ map (replace_comatches_by_gfun_calls tn) x2 = map snd (snd (snd info))) as Aux'.
      { destruct Aux0. do 2 (destruct H2). destruct H3. split; auto.
        erewrite <- map_snd_combine;
        [ eapply subterm_term_in_original_prog_CoMatch_cocases |]; eauto.
        apply (f_equal (length (A:=_))) in H3. rewrite map_length; do 2 (rewrite map_length in H3); auto.
      }
      assert (exists x', Forall (fun e => term_in_original_prog e p) x' /\ map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd info))).
      { exists x2. auto. }
      assert (exists ctx tn sn bs_es, length bs_es = length (snd (fst info)) /\
        program_skeleton p / ctx |- (E_CoMatch (fst (fst (snd info)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd info))) x2)) : tn).
      { destruct Aux0 as [snAux [bs_esAux [Len [Aux1 Aux2]]]];
        apply term_in_original_prog_typechecks in Aux2; destruct Aux2 as [ctx [t Typ']];
        exists ctx; exists t; exists snAux; exists bs_esAux; split; auto.
      }
      destruct H3 as [ctxSub [tnSub [snSub [bs_esSub [LenEq TypSub]]]]]. inversion TypSub; subst.
      apply (f_equal (map snd)) in H6; rewrite map_snd_combine in H6; auto.
      rewrite map_snd_combine in H6; [| symmetry; apply Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto]. subst.
      assert (dtorlist = (filter
               (fun x2 : ScopedName * list TypeName * TypeName =>
               let (y, _) := x2 in
               let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd info))))
               (skeleton_dtors (program_skeleton p)))).
      { clear - H10. unfold lookup_dtors in H10.
        destruct (filter (eq_TypeName (fst (fst (fst (snd info)), snSub))) (skeleton_cdts (program_skeleton p))); try discriminate.
        inversion H10; auto.
      }
      unfold gfun_bod in *. rewrite <- H3.
      clear H3; pose proof Aux' as H3. destruct H3 as [H3_1 H3_2].
      unfold gfun_bod in *; rewrite <- H3_2; clear - H3_1 H3_2 H13; generalize H13.
      generalize (map (fun dtor => snd (fst dtor) ++ snd (fst info)) dtorlist). generalize (map snd dtorlist);
      unfold gfun_bod_named in *; unfold gfun_sig in *; unfold gfun_bod in *.
      assert (length (map fst (snd (snd info))) = length x2).
      { apply (f_equal (length (A:=_))) in H3_2; repeat (rewrite map_length in * ); auto. }
      generalize H. generalize H3_1. generalize (map fst (snd (snd info))). clear. induction x2; intros.
      -- rewrite combine_empty_r in H13; inversion H13; subst. apply ListTypeDeriv'_Nil.
      -- destruct l; try inversion H. simpl in H13.
         inversion H13; subst. simpl. apply ListTypeDeriv'_Cons.
         ++ apply lift_comatch_to_skeleton_preserves_typing; auto.
            rewrite Forall_forall in H3_1. apply H3_1. apply in_eq.
         ++ apply IHx2 with (l:=l); auto.
            rewrite Forall_forall in *. intros. apply H3_1. apply in_cons. auto.
    * rewrite in_flat_map in H; destruct H; destruct H.
      pose proof (program_gfun_bods_typecheck_g p) as Typ.
      unfold fun_bods_typecheck in Typ.
      assert (exists x' sn bs_es, length bs_es = length (snd (fst info)) /\ map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd info)) /\
        term_in_original_prog (E_CoMatch (fst (fst (snd info)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd info))) x')) p) as Aux0.
      { rewrite in_map_iff in H. do 2 (destruct H). rewrite <- H in H1.
        eapply gfun_generates_from_comatch; eauto.
        eapply info_in_gfun_bods; eauto.
      }
      destruct Aux0 as [x2 Aux0].
      assert (Forall (fun e => term_in_original_prog e p) x2 /\ map (replace_comatches_by_gfun_calls tn) x2 = map snd (snd (snd info))) as Aux'.
      { destruct Aux0. do 2 (destruct H2). destruct H3. split; auto.
        erewrite <- map_snd_combine;
        [ eapply subterm_term_in_original_prog_CoMatch_cocases |]; eauto.
        apply (f_equal (length (A:=_))) in H3. rewrite map_length; do 2 (rewrite map_length in H3); auto.
      }
      assert (exists x', Forall (fun e => term_in_original_prog e p) x' /\ map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd info))).
      { exists x2. auto. }
      assert (exists ctx tn sn bs_es, length bs_es = length (snd (fst info)) /\
        program_skeleton p / ctx |- (E_CoMatch (fst (fst (snd info)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd info))) x2)) : tn).
      { destruct Aux0 as [snAux [bs_esAux [Len [Aux1 Aux2]]]];
        apply term_in_original_prog_typechecks in Aux2; destruct Aux2 as [ctx [t Typ']];
        exists ctx; exists t; exists snAux; exists bs_esAux; split; auto.
      }
      destruct H3 as [ctxSub [tnSub [snSub [bs_esSub [LenEq TypSub]]]]]. inversion TypSub; subst.
      apply (f_equal (map snd)) in H6; rewrite map_snd_combine in H6; auto.
      rewrite map_snd_combine in H6; [| symmetry; apply Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto]. subst.
      assert (dtorlist = (filter
               (fun x2 : ScopedName * list TypeName * TypeName =>
               let (y, _) := x2 in
               let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd info))))
               (skeleton_dtors (program_skeleton p)))).
      { clear - H10. unfold lookup_dtors in H10.
        destruct (filter (eq_TypeName (fst (fst (fst (snd info)), snSub))) (skeleton_cdts (program_skeleton p))); try discriminate.
        inversion H10; auto.
      }
      unfold gfun_bod in *. rewrite <- H3.
      clear H3; pose proof Aux' as H3. destruct H3 as [H3_1 H3_2].
      unfold gfun_bod in *; rewrite <- H3_2; clear - H3_1 H3_2 H13; generalize H13.
      generalize (map (fun dtor => snd (fst dtor) ++ snd (fst info)) dtorlist). generalize (map snd dtorlist);
      unfold gfun_bod_named in *; unfold gfun_sig in *; unfold gfun_bod in *.
      assert (length (map fst (snd (snd info))) = length x2).
      { apply (f_equal (length (A:=_))) in H3_2; repeat (rewrite map_length in * ); auto. }
      generalize H. generalize H3_1. generalize (map fst (snd (snd info))). clear. induction x2; intros.
      -- rewrite combine_empty_r in H13; inversion H13; subst. apply ListTypeDeriv'_Nil.
      -- destruct l; try inversion H. simpl in H13.
         inversion H13; subst. simpl. apply ListTypeDeriv'_Cons.
         ++ apply lift_comatch_to_skeleton_preserves_typing; auto.
            rewrite Forall_forall in H3_1. apply H3_1. apply in_eq.
         ++ apply IHx2 with (l:=l); auto.
            rewrite Forall_forall in *. intros. apply H3_1. apply in_cons. auto.
    * rewrite in_flat_map in H; destruct H; destruct H.
      pose proof (program_gfun_bods_typecheck_g p) as Typ.
      unfold fun_bods_typecheck in Typ.
      assert (exists x' sn bs_es, length bs_es = length (snd (fst info)) /\ map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd info)) /\
        term_in_original_prog (E_CoMatch (fst (fst (snd info)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd info))) x')) p) as Aux0.
      { rewrite in_map_iff in H. do 2 (destruct H). rewrite <- H in H1.
        eapply cfun_generates_from_comatch; eauto.
        eapply info_in_cfun_bods; eauto.
      }
      destruct Aux0 as [x2 Aux0].
      assert (Forall (fun e => term_in_original_prog e p) x2 /\ map (replace_comatches_by_gfun_calls tn) x2 = map snd (snd (snd info))) as Aux'.
      { destruct Aux0. do 2 (destruct H2). destruct H3. split; auto.
        erewrite <- map_snd_combine;
        [ eapply subterm_term_in_original_prog_CoMatch_cocases |]; eauto.
        apply (f_equal (length (A:=_))) in H3. rewrite map_length; do 2 (rewrite map_length in H3); auto.
      }
      assert (exists x', Forall (fun e => term_in_original_prog e p) x' /\ map (replace_comatches_by_gfun_calls tn) x' = map snd (snd (snd info))).
      { exists x2. auto. }
      assert (exists ctx tn sn bs_es, length bs_es = length (snd (fst info)) /\
        program_skeleton p / ctx |- (E_CoMatch (fst (fst (snd info)), sn) (combine bs_es (snd (fst info))) (combine (map fst (snd (snd info))) x2)) : tn).
      { destruct Aux0 as [snAux [bs_esAux [Len [Aux1 Aux2]]]];
        apply term_in_original_prog_typechecks in Aux2; destruct Aux2 as [ctx [t Typ']];
        exists ctx; exists t; exists snAux; exists bs_esAux; split; auto.
      }
      destruct H3 as [ctxSub [tnSub [snSub [bs_esSub [LenEq TypSub]]]]]. inversion TypSub; subst.
      apply (f_equal (map snd)) in H6; rewrite map_snd_combine in H6; auto.
      rewrite map_snd_combine in H6; [| symmetry; apply Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto]. subst.
      assert (dtorlist = (filter
               (fun x2 : ScopedName * list TypeName * TypeName =>
               let (y, _) := x2 in
               let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst (snd info))))
               (skeleton_dtors (program_skeleton p)))).
      { clear - H10. unfold lookup_dtors in H10.
        destruct (filter (eq_TypeName (fst (fst (fst (snd info)), snSub))) (skeleton_cdts (program_skeleton p))); try discriminate.
        inversion H10; auto.
      }
      unfold gfun_bod in *. rewrite <- H3.
      clear H3; pose proof Aux' as H3. destruct H3 as [H3_1 H3_2].
      unfold gfun_bod in *; rewrite <- H3_2; clear - H3_1 H3_2 H13; generalize H13.
      generalize (map (fun dtor => snd (fst dtor) ++ snd (fst info)) dtorlist). generalize (map snd dtorlist);
      unfold gfun_bod_named in *; unfold gfun_sig in *; unfold gfun_bod in *.
      assert (length (map fst (snd (snd info))) = length x2).
      { apply (f_equal (length (A:=_))) in H3_2; repeat (rewrite map_length in * ); auto. }
      generalize H. generalize H3_1. generalize (map fst (snd (snd info))). clear. induction x2; intros.
      -- rewrite combine_empty_r in H13; inversion H13; subst. apply ListTypeDeriv'_Nil.
      -- destruct l; try inversion H. simpl in H13.
         inversion H13; subst. simpl. apply ListTypeDeriv'_Cons.
         ++ apply lift_comatch_to_skeleton_preserves_typing; auto.
            rewrite Forall_forall in H3_1. apply H3_1. apply in_eq.
         ++ apply IHx2 with (l:=l); auto.
            rewrite Forall_forall in *. intros. apply H3_1. apply in_cons. auto.
Unshelve. destruct info. destruct g. exact q.
Qed.

Lemma replace_comatches_by_gfun_calls_no_new_matches: forall (tn : TypeName) (e : expr),
    sublist (collect_match_names (replace_comatches_by_gfun_calls tn e))
            (collect_match_names e).
Proof.
  intros tn e.
  induction e using expr_strong_ind; simpl; repeat rewrite map_map;
    try solve [ try (apply sublist_app; try assumption);
                apply sublist_concat; assumption]; simpl.
  - apply sublist_nil.
  - apply sublist_cons.
    apply sublist_app; try assumption.
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
  - destruct n as [tn' n']. simpl.
    name_destruct_tac; simpl.
    + rewrite map_map.
      match goal with
      | [ |- sublist (concat (map _ ?l)) (concat (map _ ?l ++ map _ _)) ] =>
        induction l;
          [> try apply sublist_nil
          | apply sublist_app; try (inversion H0; assumption);
            IH_tac Forall_tail_tac
          ]
      end.
    + repeat rewrite map_map. simpl. repeat rewrite concat_app.
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
Qed.

(********************************************************************)
(*** lemmas for uniqueness of matches ***)
(********************************************************************)


Ltac liftcomatch_destruct_hin_app_tac :=
  try match goal with
      | [ Hin: In _ _ |- _ ] =>
        repeat (rewrite map_app in Hin; rewrite concat_app in Hin);
        repeat rewrite in_app_iff in Hin
      end.

Lemma replace_comatches_reflects_match_names:
  forall (tn : TypeName) (qn : QName) (e : expr),
    In qn (collect_match_names (replace_comatches_by_gfun_calls tn e)) ->
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
  - inversion_clear Hin; [> left; solve [auto] | right].
    repeat rewrite in_app_iff; repeat rewrite in_app_iff in H1.
    inversion_clear H1 as [Hin | [Hin | Hin]]; [> left | right; left | right; right ]; auto.
    + induction es; auto; simpl in *.
      rewrite in_app_iff in Hin; rewrite in_app_iff.
      inversion_clear H0.
      inversion_clear Hin; [> left | right ]; auto.
    + induction ls; auto; simpl in *.
      rewrite in_app_iff in Hin; rewrite in_app_iff.
      inversion_clear H.
      inversion_clear Hin; [> left | right ]; auto.
  - left; induction es; auto; simpl in *.
    inversion H0; rewrite in_app_iff; rewrite in_app_iff in Hin; inversion Hin; auto.
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

Ltac liftcomatch_generate_gfuns_reflects_match_names_list_tac :=
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
          liftcomatch_destruct_hin_app_tac;
          rewrite in_app_iff;
          inversion Hin; [> left | right]; auto
  end.

Lemma generate_gfuns_reflects_match_names: forall (tn : TypeName) (e : expr) (qn : QName),
    In qn (concat
             (map (fun x : ScopedName * expr => collect_match_names (snd x))
                  (concat
                     (map (fun x : gfun_sig * gfun_bod_named => snd (snd x))
                          (generate_gfuns_from_expr tn e))))) ->
    In qn (collect_match_names e).
Proof.
  intros tn e qn H.
  induction e using expr_strong_ind; simpl in *; auto;
    try liftcomatch_destruct_hin_app_tac;
    try (rewrite in_app_iff;
    match goal with
      | [ Hin: _ \/ _ |- _ ] =>
        inversion Hin; [> left; solve [auto] | right; auto ]
      end);
    try solve [liftcomatch_generate_gfuns_reflects_match_names_list_tac].

  - right; rewrite concat_app; repeat rewrite in_app_iff.
    inversion H as [Hin | [Hin | Hin]];
      [> left; auto | right; left | right; right]; try liftcomatch_generate_gfuns_reflects_match_names_list_tac.
  - inversion_clear H as [Hin | [Hin | Hin ]].
    + name_destruct_tac; simpl in *; try contradiction.
      rewrite app_nil_r in Hin; rewrite map_map in Hin; simpl in Hin.
      rewrite concat_app; rewrite in_app_iff; right.
      induction ls; auto; simpl in *.
      rewrite in_app_iff in Hin; rewrite in_app_iff.
      inversion_clear Hin as [Hin' | Hin']; [> left | right ].
      * eapply replace_comatches_reflects_match_names; eauto.
      * apply IHls; auto. Forall_tail_tac.
    + rewrite concat_app; rewrite in_app_iff; left.
      liftcomatch_generate_gfuns_reflects_match_names_list_tac.
    + rewrite concat_app; rewrite in_app_iff; right.
      liftcomatch_generate_gfuns_reflects_match_names_list_tac.
Qed.

Lemma generate_gfuns_reflects_match_names_flat: forall (tn : TypeName) (g : list expr) (qn : QName),
    In qn
       (concat
          (map (fun x : ScopedName * expr => collect_match_names (snd x))
               (concat
                  (map (fun x : gfun_sig * gfun_bod_named => snd (snd x))
                       (flat_map (generate_gfuns_from_expr tn) g))))) ->
    In qn (flat_map collect_match_names g).
Proof.
  intros tn g qn H.
  induction g; auto; simpl in *.
  repeat (rewrite map_app in H; rewrite concat_app in H).
  rewrite in_app_iff in *.
  inversion H; auto; left.
  apply (generate_gfuns_reflects_match_names tn); auto.
Qed.

Local Hint Resolve -> In_app_iff.
Section split_matches_into_replace_generate_sec.

Lemma split_matches_into_replace_generate: forall (tn : TypeName) (e : expr) (qn : QName),
    unique (collect_match_names e) ->
    ~ (In qn (collect_match_names (replace_comatches_by_gfun_calls tn e)) /\
       In qn (concat (map collect_match_names (concat (map (fun x => (map snd (snd (snd x)))) (generate_gfuns_from_expr tn e)))))).
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
    + apply replace_comatches_reflects_match_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
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
        apply (in_map_concat _ _ qn ls (replace_comatches_reflects_match_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_match_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_gfuns_reflects_match_names tn).
        induction (generate_gfuns_from_expr tn a); auto; simpl in *.
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
             apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin_rep0)
            || apply (replace_comatches_reflects_match_names tn) in Hin_rep0;
            rewrite <- map_map with (g := map snd) in Hin_gen0;
            rewrite <- concat_map in Hin_gen0;
            rewrite map_map in Hin_gen0;
            (rewrite <- flat_map_concat_map with (l := ls) in Hin_gen0;
             apply (generate_gfuns_reflects_match_names_flat tn) in Hin_gen0;
             rewrite flat_map_concat_map in Hin_gen0)
            || apply generate_gfuns_reflects_match_names in Hin_gen0;
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
          try (eapply replace_comatches_reflects_match_names; eauto).
        rewrite <- flat_map_concat_map;
          apply (generate_gfuns_reflects_match_names_flat tn);
          rewrite flat_map_concat_map.
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * eapply Hunique1_f; eauto;
          try (apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)); rewrite map_map in Hin_rep1; eauto).
        apply (generate_gfuns_reflects_match_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_comatches_reflects_match_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
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
        apply (in_map_concat _ _ qn ls (replace_comatches_reflects_match_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_match_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_gfuns_reflects_match_names tn).
        induction (generate_gfuns_from_expr tn a); auto; simpl in *.
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
             apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin_rep0)
            || apply (replace_comatches_reflects_match_names tn) in Hin_rep0;
            rewrite <- map_map with (g := map snd) in Hin_gen0;
            rewrite <- concat_map in Hin_gen0;
            rewrite map_map in Hin_gen0;
            (rewrite <- flat_map_concat_map with (l := ls) in Hin_gen0;
             apply (generate_gfuns_reflects_match_names_flat tn) in Hin_gen0;
             rewrite flat_map_concat_map in Hin_gen0)
            || apply generate_gfuns_reflects_match_names in Hin_gen0;
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
          try (eapply replace_comatches_reflects_match_names; eauto).
        rewrite <- flat_map_concat_map;
          apply (generate_gfuns_reflects_match_names_flat tn);
          rewrite flat_map_concat_map.
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * eapply Hunique1_f; eauto;
          try (apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)); rewrite map_map in Hin_rep1; eauto).
        apply (generate_gfuns_reflects_match_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_comatches_reflects_match_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
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
        apply (in_map_concat _ _ qn ls (replace_comatches_reflects_match_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_match_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_gfuns_reflects_match_names tn).
        induction (generate_gfuns_from_expr tn a); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion H2; [> left | right ]; auto.
        rewrite <- map_map; auto.
      }
  - inversion_clear Hin_rep as [Hin_rep' | Hin_rep'].
    + subst. inversion_clear Hunique.
      clear - Hin_gen H1; apply H1; clear H1.
      repeat (repeat rewrite map_app in * ; rewrite concat_app in * ).
      repeat rewrite in_app_iff in *.
      inversion_clear Hin_gen as [Hin | [Hin | Hin]]; [> left | right; left | right; right].
      * apply (generate_gfuns_reflects_match_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * rewrite <- map_map.
        apply (in_map_concat _ _ _ _ (fun e qn => generate_gfuns_reflects_match_names tn qn e)).
        rewrite map_map.
        clear - Hin; induction es; auto; simpl in *.
        repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
        rewrite in_app_iff in *; inversion Hin; [> left | right ]; auto.
        clear - H; induction (generate_gfuns_from_expr tn (fst a)); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *; inversion H; auto; left.
        rewrite <- map_map; auto.
      * rewrite <- map_map with (f := snd) in Hin.
        rewrite <- flat_map_concat_map with (l := map snd ls) in Hin.
        rewrite <- map_map with (g := map snd) in Hin.
        rewrite <- concat_map in Hin; rewrite map_map in Hin.
        apply (generate_gfuns_reflects_match_names_flat tn) in Hin.
        rewrite flat_map_concat_map in  Hin; rewrite map_map in Hin; auto.
    + repeat (rewrite map_app in *; rewrite concat_app in * ).
      inversion_clear Hunique as [|_x __x Hnin Hunique0].
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
                      | context [replace_comatches_by_gfun_calls] => H
                      end
                    end
        in let Hing := match goal with
                    | [ H: In _ ?lst |- _ ] =>
                      match lst with
                      | context [generate_gfuns_from_expr] => H
                      end
                    end
           in
           try apply replace_comatches_reflects_match_names in Hinr;
             try (rewrite map_map in Hinr; simpl in Hinr;
                  rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) in Hinr;
                  apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hinr);

             rewrite <- map_map with (g := map snd) in Hing;
             rewrite <- concat_map in Hing;
             rewrite map_map in Hing;
             try apply generate_gfuns_reflects_match_names in Hing;
             try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                  rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                  apply generate_gfuns_reflects_match_names_flat in Hing;
                  rewrite flat_map_concat_map in Hing);
        repeat rewrite map_map in *;
        match goal with
        | [ Hin: In ?qn ?lst, Hf: Forall _ ?lst |- _ ] =>
          rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
        end.
      * repeat rewrite map_map in *; simpl in *.
        clear - Hin_gen1 Hin_rep'1 H0 Hunique0.
        induction es; auto; simpl in *; inversion_clear H0.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        repeat match goal with
               | [ H: _ \/ _ |- _ ] =>
                 let H1 := fresh H
                 in inversion_clear H as [H1 | H1]
               end.
        -- apply H; auto; unique_sublist_tac.
        -- let Hinr := match goal with
                       | [ H: In _ ?lst |- _ ] =>
                         match lst with
                         | context [replace_comatches_by_gfun_calls] => H
                         end
                       end
           in let Hing := match goal with
                          | [ H: In _ ?lst |- _ ] =>
                            match lst with
                            | context [generate_gfuns_from_expr] => H
                            end
                          end
              in
                rewrite <- map_map with (g := map snd) in Hing;
                rewrite <- concat_map in Hing;
                rewrite map_map in Hing;
                try apply generate_gfuns_reflects_match_names in Hing;
                try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                     rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                     apply generate_gfuns_reflects_match_names_flat in Hing;
                     rewrite flat_map_concat_map in Hing).
           rewrite <- map_map in Hin_rep'0;
             rewrite <- map_map with (f := fst) in Hin_rep'0;
             rewrite map_map in Hin_rep'0.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin_rep'0.
           rewrite map_map in Hin_rep'0;
             apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0; eapply Hunique0; eauto.
        -- let Hinr := match goal with
                       | [ H: In _ ?lst |- _ ] =>
                         match lst with
                         | context [replace_comatches_by_gfun_calls] => H
                         end
                       end
           in let Hing := match goal with
                          | [ H: In _ ?lst |- _ ] =>
                            match lst with
                            | context [generate_gfuns_from_expr] => H
                            end
                          end
              in
              try apply replace_comatches_reflects_match_names in Hinr;
                try (rewrite map_map in Hinr; simpl in Hinr;
                     rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) in Hinr;
                     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hinr);

                rewrite <- map_map with (g := map snd) in Hing;
                rewrite <- concat_map in Hing;
                rewrite map_map in Hing;
                try apply generate_gfuns_reflects_match_names in Hing;
                try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                     rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                     apply generate_gfuns_reflects_match_names_flat in Hing;
                     rewrite flat_map_concat_map in Hing).
           rewrite map_map in Hin_gen0.
           apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0;
             eapply Hunique0; eauto.
        -- apply IHes; auto. unique_sublist_tac.
      * repeat rewrite map_map in *; simpl in *.
        clear - Hin_gen1 Hin_rep'1 H Hunique3.
        induction ls; auto; simpl in *; inversion_clear H.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        repeat match goal with
               | [ H: _ \/ _ |- _ ] =>
                 let H1 := fresh H
                 in inversion_clear H as [H1 | H1]
               end.
        -- apply H0; auto; unique_sublist_tac.
        -- let Hinr := match goal with
                       | [ H: In _ ?lst |- _ ] =>
                         match lst with
                         | context [replace_comatches_by_gfun_calls] => H
                         end
                       end
           in let Hing := match goal with
                          | [ H: In _ ?lst |- _ ] =>
                            match lst with
                            | context [generate_gfuns_from_expr] => H
                            end
                          end
              in
                rewrite <- map_map with (g := map snd) in Hing;
                rewrite <- concat_map in Hing;
                rewrite map_map in Hing;
                try apply generate_gfuns_reflects_match_names in Hing;
                try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                     rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                     apply generate_gfuns_reflects_match_names_flat in Hing;
                     rewrite flat_map_concat_map in Hing).
           rewrite <- map_map in Hin_rep'0;
             rewrite <- map_map with (f := snd) in Hin_rep'0;
             rewrite map_map in Hin_rep'0.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin_rep'0.
           rewrite map_map in Hin_rep'0;
             apply uniqueness_app_not_in in Hunique3; rewrite Forall_forall in Hunique3; eapply Hunique3; eauto.
        -- let Hinr := match goal with
                       | [ H: In _ ?lst |- _ ] =>
                         match lst with
                         | context [replace_comatches_by_gfun_calls] => H
                         end
                       end
           in let Hing := match goal with
                          | [ H: In _ ?lst |- _ ] =>
                            match lst with
                            | context [generate_gfuns_from_expr] => H
                            end
                          end
              in
              try apply replace_comatches_reflects_match_names in Hinr;
                try (rewrite map_map in Hinr; simpl in Hinr;
                     rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) in Hinr;
                     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hinr);

                rewrite <- map_map with (g := map snd) in Hing;
                rewrite <- concat_map in Hing;
                rewrite map_map in Hing;
                try apply generate_gfuns_reflects_match_names in Hing;
                try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                     rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                     apply generate_gfuns_reflects_match_names_flat in Hing;
                     rewrite flat_map_concat_map in Hing).
           rewrite map_map in Hin_gen0.
           apply uniqueness_app_not_in in Hunique3; rewrite Forall_forall in Hunique3;
             eapply Hunique3; eauto.
        -- apply IHls; auto. unique_sublist_tac.
  - name_destruct_tac; simpl in *;
      repeat (rewrite map_app in *; rewrite concat_app in * );
      repeat (rewrite in_app_iff in * ).
    + inversion_clear Hin_gen as [Hin_gen' | [Hin_gen' | Hin_gen']].
      * rewrite map_map with (g := snd) in Hin_gen'; simpl in Hin_gen'.
        rewrite <- map_map with (g := replace_comatches_by_gfun_calls tn) in Hin_rep, Hin_gen';
          rewrite map_map in Hin_rep, Hin_gen'.
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin_rep;
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin_gen'.
        rewrite map_map in Hin_rep, Hin_gen'.
        apply uniqueness_app_not_in in Hunique; rewrite Forall_forall in Hunique; eapply Hunique; eauto.
      * clear H.
        rewrite <- map_map with (f := fst) in Hin_rep, Hin_gen'.
        rewrite map_map in Hin_rep.
        match type of Hunique with
        | unique (?l ++ ?r) =>
          let H := fresh Hunique in
          assert (H: unique l); [> unique_sublist_tac | clear Hunique ]
        end.
        rewrite <- map_map in Hunique0.
          unfold fst in *; induction (map (fun x: expr * TypeName => let (y,_) := x in y) es);
            auto; simpl in *.
        inversion_clear H0; repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion_clear Hin_rep; inversion_clear Hin_gen'; auto.
        -- apply H; auto. unique_sublist_tac.
        -- apply replace_comatches_reflects_match_names in H0.
           unfold gfun_bod_named in *; unfold gfun_bod in *.
           rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H2.
           rewrite <- concat_map in H2; rewrite map_map in H2.
           apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
           apply (in_map_concat _ _ qn _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
           clear - H2.
           epose proof (map_map (generate_gfuns_from_expr tn)).
           repeat match goal with
                  | [  |- context [map (fun x => ?f (@?g x)) ?ls] ] =>
                      rewrite <- (map_map g f)
                  end.
           repeat match goal with
                  | [  |- context [concat (map (concat (A:=?B)) (map ?f ?ls))] ] =>
                    rewrite (@map_concat_switch' _ B);
                      rewrite <- concat_map
                  end.
           rewrite map_map; auto.
        -- rewrite <- map_map with (g := map snd) in H2.
           rewrite <- concat_map in H2; rewrite map_map in H2.
           apply (generate_gfuns_reflects_match_names tn) in H2.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H0.
           apply uniqueness_app_not_in in Hunique0.
           rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
        -- apply IHl; auto. unique_sublist_tac.
      * let lst_gen := match type of Hin_gen' with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end
        in rewrite <- map_map with (l := lst_gen) in Hin_gen';
        rewrite <- flat_map_concat_map with (l := map _ lst_gen) in Hin_gen';
        unfold gfun_bod_named in *; unfold gfun_bod in *;
        rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in Hin_gen';
        rewrite <- concat_map in Hin_gen';
        rewrite map_map in Hin_gen';
        apply (generate_gfuns_reflects_match_names_flat tn) in Hin_gen';
        let lst_rep := match type of Hin_gen' with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end in idtac.
        rewrite <- map_map with (g := replace_comatches_by_gfun_calls tn) in Hin_rep; rewrite map_map in Hin_rep.
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin_rep.
        rewrite flat_map_concat_map in Hin_gen'; rewrite map_map in Hin_rep, Hin_gen'.
        apply uniqueness_app_not_in in Hunique; rewrite Forall_forall in Hunique; eapply Hunique; eauto.
    + inversion_clear Hin_rep; inversion_clear Hin_gen;
      rewrite map_map in H1; simpl in H1;
        rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := fst) in H1 ||
                                                                                                                        rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in H1.
      * clear H; rewrite <- map_map with (f := fst) in H2.
        match type of Hunique with
        | unique (?l ++ ?r) =>
          let H := fresh Hunique in
          assert (H: unique l); [> unique_sublist_tac | clear Hunique ]
        end.
        rewrite <- map_map in Hunique0.
          unfold fst in *; induction (map (fun x: expr * TypeName => let (y,_) := x in y) es);
            auto; simpl in *.
        inversion_clear H0; repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion_clear H1; inversion_clear H2; auto.
        -- apply H; auto. unique_sublist_tac.
        -- apply replace_comatches_reflects_match_names in H0.
           unfold gfun_bod_named in *; unfold gfun_bod in *.
           rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H1.
           rewrite <- concat_map in H1; rewrite map_map in H1.
           apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
           apply (in_map_concat _ _ qn _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
           clear - H1.
           epose proof (map_map (generate_gfuns_from_expr tn)).
           repeat match goal with
                  | [  |- context [map (fun x => ?f (@?g x)) ?ls] ] =>
                      rewrite <- (map_map g f)
                  end.
           repeat match goal with
                  | [  |- context [concat (map (concat (A:=?B)) (map ?f ?ls))] ] =>
                    rewrite (@map_concat_switch' _ B);
                      rewrite <- concat_map
                  end.
           rewrite map_map; auto.
        -- rewrite <- map_map with (g := map snd) in H1.
           rewrite <- concat_map in H1; rewrite map_map in H1.
           apply (generate_gfuns_reflects_match_names tn) in H1.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H0.
           apply uniqueness_app_not_in in Hunique0.
           rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
        -- apply IHl; auto. unique_sublist_tac.
      * let lst_gen := match type of H2 with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end
        in rewrite <- map_map with (l := lst_gen) in H2;
        rewrite <- flat_map_concat_map with (l := map _ lst_gen) in H2;
        unfold gfun_bod_named in *; unfold gfun_bod in *;
        rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H2;
        rewrite <- concat_map in H2;
        rewrite map_map in H2;
        apply (generate_gfuns_reflects_match_names_flat tn) in H2;
        let lst_rep := match type of H2 with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end in
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H1.
        rewrite flat_map_concat_map in H2; rewrite map_map in H1, H2.
        apply uniqueness_app_not_in in Hunique; rewrite Forall_forall in Hunique; eapply Hunique; eauto.
      * let lst_gen := match type of H2 with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end
        in rewrite <- map_map with (l := lst_gen) in H2;
        rewrite <- flat_map_concat_map with (l := map _ lst_gen) in H2;
        unfold gfun_bod_named in *; unfold gfun_bod in *;
        rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H2;
        rewrite <- concat_map in H2;
        rewrite map_map in H2;
        apply (generate_gfuns_reflects_match_names_flat tn) in H2;
        let lst_rep := match type of H2 with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end in
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H1.
        rewrite flat_map_concat_map in H2; rewrite map_map in H1, H2.
        apply uniqueness_app_not_in in Hunique; rewrite Forall_forall in Hunique; eapply Hunique; eauto.
      * clear H0; rewrite <- map_map with (f := snd) in H2.
        match type of Hunique with
        | unique (?l ++ ?r) =>
          let H := fresh Hunique in
          assert (H: unique r); [> unique_sublist_tac | clear Hunique ]
        end.
        rewrite <- map_map in Hunique0.
          unfold snd in Hunique0, H2 at 4, H1; induction (map (fun x: ScopedName * expr => let (_,y) := x in y) ls);
            auto; simpl in *.
        inversion_clear H; repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion_clear H1; inversion_clear H2; auto.
        -- apply H0; auto. unique_sublist_tac.
        -- apply replace_comatches_reflects_match_names in H.
           unfold gfun_bod_named in *; unfold gfun_bod in *.
           rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H1.
           rewrite <- concat_map in H1; rewrite map_map in H1.
           apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
           apply (in_map_concat _ _ qn _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
           clear - H1.
           epose proof (map_map (generate_gfuns_from_expr tn)).
           repeat match goal with
                  | [  |- context [map (fun x => ?f (@?g x)) ?ls] ] =>
                      rewrite <- (map_map g f)
                  end.
           repeat match goal with
                  | [  |- context [concat (map (concat (A:=?B)) (map ?f ?ls))] ] =>
                    rewrite (@map_concat_switch' _ B);
                      rewrite <- concat_map
                  end.
           rewrite map_map; auto.
        -- rewrite <- map_map with (g := map snd) in H1.
           rewrite <- concat_map in H1; rewrite map_map in H1.
           apply (generate_gfuns_reflects_match_names tn) in H1.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H.
           apply uniqueness_app_not_in in Hunique0.
           rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
        -- apply IHl; auto. unique_sublist_tac.
  - repeat (rewrite map_app in Hin_gen; rewrite concat_app in Hin_gen).
    rewrite in_app_iff in *.
    inversion_clear Hin_rep; inversion_clear Hin_gen.
    * apply IHe1; auto; unique_sublist_tac.
    * apply replace_comatches_reflects_match_names in H.
      rewrite <- map_map with (g := map snd) (f := fun x => snd (@snd gfun_sig (QName * list (ScopedName * expr)) x)) in H0;
        rewrite <- concat_map in H0; rewrite map_map in H0.
      apply (generate_gfuns_reflects_match_names tn _ qn) in H0.
      rewrite <- uniqueness_app_rewrite in Hunique.
      inversion Hunique as [Hx [Hxx Hxxx]].
      rewrite Forall_forall in Hxxx.
      apply (Hxxx qn); auto.
    * apply replace_comatches_reflects_match_names in H.
      rewrite <- map_map with (g := map snd) (f := fun x => snd (@snd gfun_sig (QName * list (ScopedName * expr)) x)) in H0;
        rewrite <- concat_map in H0; rewrite map_map in H0.
      apply (generate_gfuns_reflects_match_names tn _ qn) in H0.
      rewrite <- uniqueness_app_rewrite in Hunique.
      inversion Hunique as [Hx [Hxx Hxxx]].
      rewrite Forall_forall in Hxxx.
      apply (Hxxx qn); auto.
    * apply IHe2; auto; unique_sublist_tac.
      Unshelve. all: apply True.
Qed.

End split_matches_into_replace_generate_sec.

Lemma generate_gfuns_unique_matches_propagates: forall (tn : TypeName) (e : expr),
    unique (collect_match_names e) ->
    unique (concat (map (fun x : ScopedName * expr => collect_match_names (snd x))
                        (concat (map (fun x : gfun_sig * gfun_bod_named => snd (snd x)) (generate_gfuns_from_expr tn e))))).
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
    apply generate_gfuns_reflects_match_names in Hin.
    pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1.
    rewrite concat_map in Hnin at 1.
    rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_gfuns_from_expr tn)).
    unfold gfun_bod_named in *.
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
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      unfold gfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      unfold gfun_bod_named in *.
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
    apply generate_gfuns_reflects_match_names in Hin.
    pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1.
    rewrite concat_map in Hnin at 1.
    rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_gfuns_from_expr tn)).
    unfold gfun_bod_named in *.
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
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      unfold gfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      unfold gfun_bod_named in *.
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
    apply generate_gfuns_reflects_match_names in Hin.
    pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_gfuns_from_expr tn)).
    specialize Hlem' with (2 := Hnin).
    apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
    apply Hlem'; intros. apply Hlem.
    rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    inversion_clear H as [| _x __x Hnin_n Hunqiue]. rewrite concat_app in Hunqiue.
    repeat rewrite <- uniqueness_app_rewrite in Hunqiue.
    repeat (match goal with
            | [ Hx: _ /\ _ |- _ ] =>
              let H1 := fresh Hunique in
              let H2 := fresh Hunique in
              inversion_clear Hx as [H1 H2]
            end).
    apply uniqueness_app_3way; auto.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
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
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique1; rewrite Forall_forall in Hunique1; specialize (Hunique1 qn Hin); apply Hunique1.
      rewrite <- map_map.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + clear H0 H1 IHe Hnin_n Hunique1 Hunique0 Hunique Hunique4.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      rewrite Forall_forall in Hunique2; specialize (Hunique2 qn Hin); apply Hunique2.
      rewrite <- map_map.
      rewrite in_app_iff; left.
      apply Hlem'; intros; apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + clear H0 H1 IHe Hnin_n Hunique0 Hunique1 Hunique Hunique4.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      rewrite Forall_forall in Hunique2; specialize (Hunique2 qn Hin); apply Hunique2.
      rewrite in_app_iff; right.
      rewrite <- map_map.
      apply Hlem'; intros; apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + clear - Hunique4.
      rewrite Forall_forall; intros qn Hin Hnin.
      induction es; try solve [inversion Hin]; simpl in *.
      repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
      rewrite <- Forall_app_iff in Hunique4; inversion_clear Hunique4 as [Hunique Hx].
      rewrite in_app_iff in Hin.
      rename Hin into Hin'; inversion_clear Hin' as [Hin | Hin]; auto.
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      rewrite Forall_forall in Hunique; specialize (Hunique qn Hin); apply Hunique.
      rewrite <- map_map.
      apply Hlem'; intros; apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    rewrite concat_app in H.
    rewrite <- uniqueness_app_rewrite in H.
    repeat (match goal with
            | [ Hx: _ /\ _ |- _ ] =>
              let H1 := fresh Hunique in
              let H2 := fresh Hunique in
              inversion_clear Hx as [H1 H2]
            end).
    apply uniqueness_app_3way; auto.
    + name_destruct_tac; simpl; try apply Unique_nil.
      rewrite app_nil_r. rewrite map_map; simpl.
      clear - Hunique1.
      induction ls; try apply Unique_nil; simpl.
      simpl in Hunique1; rewrite <- uniqueness_app_rewrite in Hunique1.
      inversion_clear Hunique1 as [Hu1 [Hu2 Hu3]].
      apply uniqueness_app; auto.
      * generalize dependent (snd a); intros e Hunique Hf.
        pose proof (replace_comatches_by_gfun_calls_no_new_matches tn e).
        unique_sublist_tac.
      * rewrite Forall_forall; intros qn Hin Hnin.
        apply replace_comatches_reflects_match_names in Hin.
        rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hnin.
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hnin.
        rewrite Forall_forall in Hu3; eapply Hu3; eauto.
        rewrite map_map in Hnin; auto.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique; rewrite Forall_forall in Hunique; specialize (Hunique qn Hin); apply Hunique.
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
      apply generate_gfuns_reflects_match_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique1; rewrite Forall_forall in Hunique1; specialize (Hunique1 qn Hin); apply Hunique1.
      rewrite <- map_map.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + name_destruct_tac; simpl in *; try apply Forall_nil.
      rewrite app_nil_r.
      pose proof (uniqueness_app _ _ Hunique Hunique1 Hunique2) as Htmp; clear Hunique Hunique1 Hunique2.
      rename Htmp into Hunique.
      rewrite <- app_nil_l in Hunique; apply unique_app_switch in Hunique; rewrite app_nil_l in Hunique.
      apply uniqueness_app_not_in in Hunique.
      rewrite Forall_forall; intros qn Hin Hnin.
      induction ls; try solve [inversion Hin]; simpl in *.
      inversion_clear H0.
      repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
      rewrite <- Forall_app_iff in Hunique; inversion_clear Hunique as [Hunique' Hx].
      rewrite in_app_iff in Hin.
      rename Hin into Hin'; inversion_clear Hin' as [Hin | Hin]; auto.
      apply replace_comatches_reflects_match_names in Hin; auto.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      rewrite Forall_forall in Hunique'; specialize (Hunique' qn Hin); apply Hunique'.
      rewrite <- map_map.
      apply Hlem'; intros; apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + name_destruct_tac; simpl in *; try apply Forall_nil.
      rewrite app_nil_r.
      rewrite Forall_forall; simpl; intros qn Hin Hnin.
      rewrite map_map in Hin; simpl in Hin.
      rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hin.
      clear - Hunique1 Hin Hnin.
      induction ls; auto; simpl in *.
      unique_app_destr_tac.
      repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
      rewrite in_app_iff in *.
      inversion_clear Hnin; inversion_clear Hin; auto.
      * eapply split_matches_into_replace_generate; eauto; split; eauto.
        clear - H; induction (generate_gfuns_from_expr tn (snd a)); auto; simpl in *.
        rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
        inversion H; [> left | right ]; auto.
        rewrite <- map_map in H0; auto.
      * apply generate_gfuns_reflects_match_names in H.
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H0.
        rewrite Forall_forall in Hunique1_f; specialize (Hunique1_f qn).
        apply Hunique1_f; auto.
        rewrite map_map in H0; auto.
      * apply (replace_comatches_reflects_match_names tn) in H0.
        rewrite <- map_map with (l := ls) in H.
        rewrite Forall_forall in Hunique1_f; specialize (Hunique1_f qn); apply Hunique1_f; auto.
        clear - H.
        induction ls; auto; simpl in *.
        repeat (rewrite map_app in H; rewrite concat_app in H).
        rewrite in_app_iff in *.
        inversion_clear H; auto; left.
        apply generate_gfuns_reflects_match_names with (tn := tn); auto.
    + clear Hunique Hunique1; rename Hunique2 into Hunique.
      rewrite Forall_forall; intros qn Hin Hnin.
      induction es; try solve [inversion Hin]; simpl in *.
      inversion_clear H1.
      repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
      rewrite <- Forall_app_iff in Hunique; inversion_clear Hunique as [Hunique' Hx].
      rewrite in_app_iff in Hin.
      rename Hin into Hin'; inversion_clear Hin' as [Hin | Hin]; auto.
      apply generate_gfuns_reflects_match_names in Hin; auto.
      pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      rewrite Forall_forall in Hunique'; specialize (Hunique' qn Hin); apply Hunique'.
      rewrite <- map_map.
      apply Hlem'; intros; apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    rewrite <- uniqueness_app_rewrite in H; inversion_clear H; inversion_clear H1.
    apply uniqueness_app; auto.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_gfuns_reflects_match_names in Hin.
    pose proof (fun qn e => generate_gfuns_reflects_match_names tn e qn) as Hlem.
    rewrite Forall_forall in H2; specialize (H2 qn Hin); apply H2; auto.
Qed.


(********************************************************************)
(*** uniqueness of matches ***)
(********************************************************************)

Lemma new_match_names_unique : forall p tn,
  match_names_unique
    (map (fun x : Name * expr => (fst x, replace_comatches_by_gfun_calls tn (snd x)))
       (program_fun_bods p))
    (map
       (fun x : QName * list (ScopedName * expr) =>
        (fst x,
        map
          (fun y : ScopedName * expr => (fst y, replace_comatches_by_gfun_calls tn (snd y)))
          (snd x))) (program_cfun_bods_g p)
    ++ [])
    ((map
       (fun x : QName * list (ScopedName * expr) =>
        (fst x,
        map
          (fun y : ScopedName * expr => (fst y, replace_comatches_by_gfun_calls tn (snd y)))
          (snd x))) (program_gfun_bods_g p))
     ++ new_gfun_bods_l p tn).
Proof.
  intros p tn.
  unfold match_names_unique.
  rewrite app_nil_r.
  repeat rewrite map_app. repeat rewrite concat_app. repeat rewrite map_app. rewrite concat_app.
  match goal with
  | [  |- unique (?l1 ++ ?l2 ++ ?l3 ++ ?l4) ] =>
    reassoc (l1 ++ l2 ++ l3 ++ l4) ((l1 ++ l2 ++ l3) ++ l4)
  end.
  apply uniqueness_app.
  - apply uniqueness_app_3way; repeat rewrite map_compose; simpl; try rewrite concat_map; repeat rewrite map_compose;

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
           apply replace_comatches_by_gfun_calls_no_new_matches
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
             apply replace_comatches_by_gfun_calls_no_new_matches
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
     let unique_xfun_tac :=
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
            apply replace_comatches_by_gfun_calls_no_new_matches
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
             [> | unique_xfun_tac | unique_xfun_tac | forall_fun_tac | forall_fun_tac | ].

  + apply uniqueness_sublist with (tot := concat (map (fun a => collect_match_names (snd a)) (program_fun_bods p))).
    * apply sublist_concat.
      induction (program_fun_bods p); try apply Forall_nil.
      apply Forall_cons; try assumption.
      apply replace_comatches_by_gfun_calls_no_new_matches.
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
      apply match_names_unique_global_sublist in H; unfold match_names_unique in H.
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
                 apply replace_comatches_by_gfun_calls_no_new_matches
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
      apply replace_comatches_by_gfun_calls_no_new_matches
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
   unfold new_gfun_bods_l.
   repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
   repeat rewrite map_map in *.
   repeat unique_app_destr_tac.
   apply uniqueness_app_3way.
   + clear - H0.
     induction (program_fun_bods p); auto; simpl in *.
     repeat (rewrite map_app; rewrite concat_app).
     unique_app_destr_tac.
     apply uniqueness_app; auto.
     * apply generate_gfuns_unique_matches_propagates; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_gfuns_reflects_match_names in Hin.
       rewrite Forall_forall in H0_f; eapply H0_f; eauto.
       rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
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
       -- apply generate_gfuns_unique_matches_propagates; auto.
       -- rewrite Forall_forall; intros qn Hin Hnin.
          rewrite Forall_forall in H0_f; eapply H0_f.
          ++ eapply (generate_gfuns_reflects_match_names tn _ qn); auto.
          ++ rewrite <- map_map.
             eapply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
             clear - Hnin.
             induction (map snd l); auto.
             simpl in *.
             repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
             rewrite in_app_iff; rewrite in_app_iff in Hnin.
             inversion_clear Hnin; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_gfuns_reflects_match_names_flat in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite map_map in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite Forall_forall in H3_f; eapply H3_f; eauto.
       rewrite <- map_map; rewrite <- flat_map_concat_map.
       apply generate_gfuns_reflects_match_names_flat in Hin; auto.
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
       -- apply generate_gfuns_unique_matches_propagates; auto.
       -- rewrite Forall_forall; intros qn Hin Hnin.
          rewrite Forall_forall in H0_f; eapply H0_f.
          ++ eapply (generate_gfuns_reflects_match_names tn _ qn); auto.
          ++ rewrite <- map_map.
             eapply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
             clear - Hnin.
             induction (map snd l); auto.
             simpl in *.
             repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
             rewrite in_app_iff; rewrite in_app_iff in Hnin.
             inversion_clear Hnin; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_gfuns_reflects_match_names_flat in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite map_map in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite Forall_forall in H2_f; eapply H2_f; eauto.
       rewrite <- map_map; rewrite <- flat_map_concat_map.
       apply generate_gfuns_reflects_match_names_flat in Hin; auto.
   + clear - H_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H_f.
     * clear H_f Hnin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
       unfold fun_bod in *.
       induction (@map _ expr snd (program_fun_bods p)); eauto; simpl in *.
       repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
       rewrite in_app_iff in *.
       inversion_clear Hin; auto.
     * rewrite in_app_iff; right. unfold gfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_gfuns_reflects_match_names_flat tn); auto. repeat rewrite flat_map_concat_map in *; auto.
   + clear - H_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H_f.
     * clear H_f Hnin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
       unfold fun_bod in *.
       induction (@map _ expr snd (program_fun_bods p)); eauto; simpl in *.
       repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
       rewrite in_app_iff in *.
       inversion_clear Hin; auto.
     * rewrite in_app_iff; left. unfold gfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_gfuns_reflects_match_names_flat tn); auto. repeat rewrite flat_map_concat_map in *; auto.
   + clear - H1_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H1_f.
     * clear H1_f Hin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_match_names tn e qn)).
       rewrite <- flat_map_concat_map with (l := program_cfun_bods_g p).
       unfold cfun_bod_named in *; unfold cfun_bod in *.
       induction (@map _ expr snd (flat_map snd (program_cfun_bods_g p))); eauto; simpl in *.
       repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin); eauto.
       rewrite in_app_iff in *.
       inversion_clear Hnin; auto.
     * unfold gfun_bod_named in *; unfold gfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_gfuns_reflects_match_names_flat tn).
       repeat rewrite flat_map_concat_map in *; auto.
 - unfold new_gfun_bods_l. repeat rewrite map_map; simpl.
   repeat rewrite concat_map; repeat (rewrite map_map; simpl).
   rewrite Forall_forall; intros qn Hin Hnin.
   repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
   repeat rewrite in_app_iff in *.
   rename Hin into Hin'; rename Hnin into Hnin';
     inversion_clear Hin' as [Hin|[Hin|Hin]]; inversion_clear Hnin' as [Hnin|[Hnin|Hnin]].
   + rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hin.
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
       induction (generate_gfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_comatches_reflects_match_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_gfuns_reflects_match_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_gfuns_reflects_match_names tn).
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
     rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) in Hin.
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hnin. rewrite <- flat_map_concat_map. apply (generate_gfuns_reflects_match_names_flat tn).
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
     rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) in Hin.
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hnin. rewrite <- flat_map_concat_map. apply (generate_gfuns_reflects_match_names_flat tn).
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
     apply (generate_gfuns_reflects_match_names_flat tn) in Hnin.
     rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hin.
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)).
     induction (program_cfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion Hin; auto; left.
     rewrite map_map in H; simpl in H.
     rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in H; auto.
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
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_gfuns_reflects_match_names_flat tn) in Hnin.
     rewrite <- concat_map in Hin; repeat rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); clear H0; auto.
   + rewrite <- map_map in Hin. rewrite <- concat_map in Hin.
     rewrite <- map_map with (f := snd) (g := map (fun y => (fst y, replace_comatches_by_gfun_calls tn (snd y)))) in Hin.
     rewrite <- concat_map in Hin; repeat rewrite <- flat_map_concat_map in Hin; rewrite flat_map_concat_map in Hin.
     rewrite map_map in Hin; simpl in Hin. rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hin.
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
       induction (generate_gfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_comatches_reflects_match_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_gfuns_reflects_match_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_gfuns_reflects_match_names tn).
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
     apply (generate_gfuns_reflects_match_names_flat tn) in Hnin.
     rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hin.
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)).
     induction (program_gfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion Hin; auto; left.
     rewrite map_map in H; simpl in H.
     rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in H; auto.
   + rewrite <- map_map in Hin. rewrite <- concat_map in Hin.
     rewrite <- map_map with (f := snd) (g := map (fun y => (fst y, replace_comatches_by_gfun_calls tn (snd y)))) in Hin.
     rewrite <- concat_map in Hin; repeat rewrite <- flat_map_concat_map in Hin; rewrite flat_map_concat_map in Hin.
     rewrite map_map in Hin; simpl in Hin. rewrite <- map_map with (g := fun x => collect_match_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hin.
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
       induction (generate_gfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_comatches_reflects_match_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_gfuns_reflects_match_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_gfuns_reflects_match_names tn).
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
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_match_names tn)) in Hin.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_gfuns_reflects_match_names_flat tn) in Hnin.
     rewrite <- concat_map in Hin; repeat rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); clear H0; auto.
Qed.


(********************************************************************)
(*** lemmas for uniqueness of comatches ***)
(********************************************************************)

Lemma replace_comatches_by_gfun_calls_no_new_comatches: forall (tn : TypeName) (e : expr),
    sublist (collect_comatch_names (replace_comatches_by_gfun_calls tn e))
            (collect_comatch_names e).
Proof.
  intros tn e.
  induction e using expr_strong_ind; simpl; repeat rewrite map_map;
    try solve [ try (apply sublist_app; try assumption);
                apply sublist_concat; assumption]; simpl.
  - apply sublist_nil.
  - apply sublist_app; try assumption.
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
  - destruct n as [tn' n']. simpl.
    name_destruct_tac; simpl.
    + rewrite map_map.
      apply sublist_skip.
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
Qed.

Lemma replace_comatches_reflects_comatch_names:
  forall (tn : TypeName) (qn : QName) (e : expr),
    In qn (collect_comatch_names (replace_comatches_by_gfun_calls tn e)) ->
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
  - do 2 rewrite map_map in H1; simpl in H1.
    inversion_clear H1 as [Hin | Hin]; right; [> left | right].
    + clear H IHe.
      induction es; auto; simpl in *; inversion_clear H0.
      rewrite in_app_iff in Hin; rewrite in_app_iff.
      inversion Hin; [> left | right ]; auto.
    + clear H0 IHe.
      induction ls; auto; simpl in *; inversion_clear H.
      rewrite in_app_iff in Hin; rewrite in_app_iff.
      inversion Hin; [> left | right ]; auto.
  - right; left; induction es; auto; simpl in *.
    inversion H0; rewrite in_app_iff; rewrite in_app_iff in Hin; inversion Hin; auto.
  - inversion_clear Hin as [E | Hin']; auto.
    rewrite in_app_iff in *. right.
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

Ltac liftcomatch_generate_gfuns_reflects_comatch_names_list_tac :=
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
          liftcomatch_destruct_hin_app_tac;
          rewrite in_app_iff;
          inversion Hin; [> left | right]; auto
  end.

Lemma generate_gfuns_reflects_comatch_names: forall (tn : TypeName) (e : expr) (qn : QName),
    In qn (concat
             (map (fun x : ScopedName * expr => collect_comatch_names (snd x))
                  (concat
                     (map (fun x : gfun_sig * gfun_bod_named => snd (snd x))
                          (generate_gfuns_from_expr tn e))))) ->
    In qn (collect_comatch_names e).
Proof.
  intros tn e qn H.
  induction e using expr_strong_ind; simpl in *; auto;
    try liftcomatch_destruct_hin_app_tac;
    try (rewrite in_app_iff;
    match goal with
      | [ Hin: _ \/ _ |- _ ] =>
        inversion Hin; [> left; solve [auto] | right; auto ]
      end);
    try solve [liftcomatch_generate_gfuns_reflects_comatch_names_list_tac].

  - inversion_clear H2 as [Hin | Hin];
      rewrite concat_app; rewrite in_app_iff; (left + right);
      liftcomatch_generate_gfuns_reflects_comatch_names_list_tac.
  - right; rewrite concat_app; repeat rewrite in_app_iff.
    inversion H as [Hin | [Hin | Hin]];
    [> | left | right]; [> | liftcomatch_generate_gfuns_reflects_comatch_names_list_tac ..].
    name_destruct_tac; try solve [inversion Hin]; simpl in Hin; rewrite app_nil_r in Hin.
    rewrite map_map in Hin; simpl in Hin; right.
    rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hin.
    apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin.
    rewrite map_map in Hin; auto.
Qed.

Lemma generate_gfuns_reflects_comatch_names_flat: forall (tn : TypeName) (g : list expr) (qn : QName),
    In qn
       (concat
          (map (fun x : ScopedName * expr => collect_comatch_names (snd x))
               (concat
                  (map (fun x : gfun_sig * gfun_bod_named => snd (snd x))
                       (flat_map (generate_gfuns_from_expr tn) g))))) ->
    In qn (flat_map collect_comatch_names g).
Proof.
  intros tn g qn H.
  induction g; auto; simpl in *.
  repeat (rewrite map_app in H; rewrite concat_app in H).
  rewrite in_app_iff in *.
  inversion H; auto; left.
  apply (generate_gfuns_reflects_comatch_names tn); auto.
Qed.

Section split_comatches_into_replace_generate_sec.

Lemma split_comatches_into_replace_generate: forall (tn : TypeName) (e : expr) (qn : QName),
    unique (collect_comatch_names e) ->
    ~ (In qn (collect_comatch_names (replace_comatches_by_gfun_calls tn e)) /\
       In qn (concat (map collect_comatch_names (concat (map (fun x => (map snd (snd (snd x)))) (generate_gfuns_from_expr tn e)))))).
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
    + apply replace_comatches_reflects_comatch_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
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
        apply (in_map_concat _ _ qn ls (replace_comatches_reflects_comatch_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_comatch_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_gfuns_reflects_comatch_names tn).
        induction (generate_gfuns_from_expr tn a); auto; simpl in *.
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
             apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin_rep0)
            || apply (replace_comatches_reflects_comatch_names tn) in Hin_rep0;
            rewrite <- map_map with (g := map snd) in Hin_gen0;
            rewrite <- concat_map in Hin_gen0;
            rewrite map_map in Hin_gen0;
            (rewrite <- flat_map_concat_map with (l := ls) in Hin_gen0;
             apply (generate_gfuns_reflects_comatch_names_flat tn) in Hin_gen0;
             rewrite flat_map_concat_map in Hin_gen0)
            || apply generate_gfuns_reflects_comatch_names in Hin_gen0;
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
          try (eapply replace_comatches_reflects_comatch_names; eauto).
        rewrite <- flat_map_concat_map;
          apply (generate_gfuns_reflects_comatch_names_flat tn);
          rewrite flat_map_concat_map.
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * eapply Hunique1_f; eauto;
          try (apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)); rewrite map_map in Hin_rep1; eauto).
        apply (generate_gfuns_reflects_comatch_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_comatches_reflects_comatch_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
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
        apply (in_map_concat _ _ qn ls (replace_comatches_reflects_comatch_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_comatch_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_gfuns_reflects_comatch_names tn).
        induction (generate_gfuns_from_expr tn a); auto; simpl in *.
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
             apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin_rep0)
            || apply (replace_comatches_reflects_comatch_names tn) in Hin_rep0;
            rewrite <- map_map with (g := map snd) in Hin_gen0;
            rewrite <- concat_map in Hin_gen0;
            rewrite map_map in Hin_gen0;
            (rewrite <- flat_map_concat_map with (l := ls) in Hin_gen0;
             apply (generate_gfuns_reflects_comatch_names_flat tn) in Hin_gen0;
             rewrite flat_map_concat_map in Hin_gen0)
            || apply generate_gfuns_reflects_comatch_names in Hin_gen0;
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
          try (eapply replace_comatches_reflects_comatch_names; eauto).
        rewrite <- flat_map_concat_map;
          apply (generate_gfuns_reflects_comatch_names_flat tn);
          rewrite flat_map_concat_map.
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
      * eapply Hunique1_f; eauto;
          try (apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)); rewrite map_map in Hin_rep1; eauto).
        apply (generate_gfuns_reflects_comatch_names tn).
        rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - induction ls; auto; simpl in *.
    repeat (rewrite map_app in *; rewrite concat_app in * ).
    repeat (rewrite in_app_iff in * ).
    unique_app_destr_tac.
    inversion_clear H.
    inversion Hin_rep; inversion Hin_gen; auto.
    + apply replace_comatches_reflects_comatch_names in H.
      pose proof (in_map_concat _ _ qn ls (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
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
        apply (in_map_concat _ _ qn ls (replace_comatches_reflects_comatch_names tn)).
        induction ls; auto; simpl in *.
        rewrite in_app_iff in *. inversion H; [> left | right ]; auto.
      }
      assert (In qn (collect_comatch_names a));
        [> | rewrite Forall_forall in Hunique_f; eapply Hunique_f; eauto].
      { clear - H2.
        apply (generate_gfuns_reflects_comatch_names tn).
        induction (generate_gfuns_from_expr tn a); auto; simpl in *.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion H2; [> left | right ]; auto.
        rewrite <- map_map; auto.
      }
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
                      | context [replace_comatches_by_gfun_calls] => H
                      end
                    end
        in let Hing := match goal with
                    | [ H: In _ ?lst |- _ ] =>
                      match lst with
                      | context [generate_gfuns_from_expr] => H
                      end
                    end
           in
           try apply replace_comatches_reflects_comatch_names in Hinr;
             try (rewrite map_map in Hinr; simpl in Hinr;
                  rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) in Hinr;
                  apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hinr);

             rewrite <- map_map with (g := map snd) in Hing;
             rewrite <- concat_map in Hing;
             rewrite map_map in Hing;
             try apply generate_gfuns_reflects_comatch_names in Hing;
             try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                  rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                  apply generate_gfuns_reflects_comatch_names_flat in Hing;
                  rewrite flat_map_concat_map in Hing);
        repeat rewrite map_map in *;
        match goal with
        | [ Hin: In ?qn ?lst, Hf: Forall _ ?lst |- _ ] =>
          rewrite Forall_forall in Hf; eapply Hf; solve [eauto]
        end.
      * repeat rewrite map_map in *; simpl in *.
        clear - Hin_gen1 Hin_rep1 H0 Hunique2.
        induction es; auto; simpl in *; inversion_clear H0.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        repeat match goal with
               | [ H: _ \/ _ |- _ ] =>
                 let H1 := fresh H
                 in inversion_clear H as [H1 | H1]
               end.
        -- apply H; auto; unique_sublist_tac.
        -- let Hinr := match goal with
                       | [ H: In _ ?lst |- _ ] =>
                         match lst with
                         | context [replace_comatches_by_gfun_calls] => H
                         end
                       end
           in let Hing := match goal with
                          | [ H: In _ ?lst |- _ ] =>
                            match lst with
                            | context [generate_gfuns_from_expr] => H
                            end
                          end
              in
              try apply replace_comatches_reflects_comatch_names in Hinr;
                try (rewrite map_map in Hinr; simpl in Hinr;
                     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) in Hinr;
                     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hinr);

                rewrite <- map_map with (g := map snd) in Hing;
                rewrite <- concat_map in Hing;
                rewrite map_map in Hing;
                try apply generate_gfuns_reflects_comatch_names in Hing;
                try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                     rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                     apply generate_gfuns_reflects_comatch_names_flat in Hing;
                     rewrite flat_map_concat_map in Hing).
           rewrite map_map in Hin_gen0.
           apply uniqueness_app_not_in in Hunique2; rewrite Forall_forall in Hunique2;
             eapply Hunique2; eauto.
        -- let Hinr := match goal with
                       | [ H: In _ ?lst |- _ ] =>
                         match lst with
                         | context [replace_comatches_by_gfun_calls] => H
                         end
                       end
           in let Hing := match goal with
                          | [ H: In _ ?lst |- _ ] =>
                            match lst with
                            | context [generate_gfuns_from_expr] => H
                            end
                          end
              in
                rewrite <- map_map with (g := map snd) in Hing;
                rewrite <- concat_map in Hing;
                rewrite map_map in Hing;
                try apply generate_gfuns_reflects_comatch_names in Hing;
                try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                     rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                     apply generate_gfuns_reflects_comatch_names_flat in Hing;
                     rewrite flat_map_concat_map in Hing).
           rewrite <- map_map in Hin_rep0;
             rewrite <- map_map with (f := fst) in Hin_rep0;
             rewrite map_map in Hin_rep0.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin_rep0.
           rewrite map_map in Hin_rep0;
             apply uniqueness_app_not_in in Hunique2; rewrite Forall_forall in Hunique2; eapply Hunique2; eauto.
        -- apply IHes; auto. unique_sublist_tac.
      * repeat rewrite map_map in *; simpl in *.
        clear - Hin_gen1 Hin_rep1 H Hunique3.
        induction ls; auto; simpl in *; inversion_clear H.
        repeat (rewrite map_app in *; rewrite concat_app in * ).
        rewrite in_app_iff in *.
        repeat match goal with
               | [ H: _ \/ _ |- _ ] =>
                 let H1 := fresh H
                 in inversion_clear H as [H1 | H1]
               end.
        -- apply H0; auto; unique_sublist_tac.
        -- let Hinr := match goal with
                       | [ H: In _ ?lst |- _ ] =>
                         match lst with
                         | context [replace_comatches_by_gfun_calls] => H
                         end
                       end
           in let Hing := match goal with
                          | [ H: In _ ?lst |- _ ] =>
                            match lst with
                            | context [generate_gfuns_from_expr] => H
                            end
                          end
              in
              try apply replace_comatches_reflects_comatch_names in Hinr;
                try (rewrite map_map in Hinr; simpl in Hinr;
                     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) in Hinr;
                     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hinr);

                rewrite <- map_map with (g := map snd) in Hing;
                rewrite <- concat_map in Hing;
                rewrite map_map in Hing;
                try apply generate_gfuns_reflects_comatch_names in Hing;
                try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                     rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                     apply generate_gfuns_reflects_comatch_names_flat in Hing;
                     rewrite flat_map_concat_map in Hing).
           rewrite map_map in Hin_gen0.
           apply uniqueness_app_not_in in Hunique3; rewrite Forall_forall in Hunique3;
             eapply Hunique3; eauto.
        -- let Hinr := match goal with
                       | [ H: In _ ?lst |- _ ] =>
                         match lst with
                         | context [replace_comatches_by_gfun_calls] => H
                         end
                       end
           in let Hing := match goal with
                          | [ H: In _ ?lst |- _ ] =>
                            match lst with
                            | context [generate_gfuns_from_expr] => H
                            end
                          end
              in
                rewrite <- map_map with (g := map snd) in Hing;
                rewrite <- concat_map in Hing;
                rewrite map_map in Hing;
                try apply generate_gfuns_reflects_comatch_names in Hing;
                try (rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hing;
                     rewrite <- flat_map_concat_map with (f := generate_gfuns_from_expr tn) in Hing;
                     apply generate_gfuns_reflects_comatch_names_flat in Hing;
                     rewrite flat_map_concat_map in Hing).
           rewrite <- map_map in Hin_rep0;
             rewrite <- map_map with (f := snd) in Hin_rep0;
             rewrite map_map in Hin_rep0.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin_rep0.
           rewrite map_map in Hin_rep0;
             apply uniqueness_app_not_in in Hunique3; rewrite Forall_forall in Hunique3; eapply Hunique3; eauto.
        -- apply IHls; auto. unique_sublist_tac.
  - name_destruct_tac; simpl in *;
      repeat (rewrite map_app in *; rewrite concat_app in * );
      repeat (rewrite in_app_iff in * ).
    + inversion_clear Hin_gen as [Hin_gen' | [Hin_gen' | Hin_gen']].
      * rewrite map_map with (g := snd) in Hin_gen'; simpl in Hin_gen'.
        rewrite <- map_map with (g := replace_comatches_by_gfun_calls tn) in Hin_rep, Hin_gen';
          rewrite map_map in Hin_rep, Hin_gen'.
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin_rep;
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin_gen'.
        rewrite map_map in Hin_rep, Hin_gen'.
        inversion_clear Hunique.
        apply uniqueness_app_not_in in H2; rewrite Forall_forall in H2; eapply H2; eauto.
      * clear H.
        rewrite <- map_map with (f := fst) in Hin_rep, Hin_gen'.
        rewrite map_map in Hin_rep.
        inversion_clear Hunique as [|_x __x Hnin Hunique0].
        match type of Hunique0 with
        | unique (?l ++ ?r) =>
          let H := fresh Hunique in
          assert (H: unique l); [> unique_sublist_tac | clear Hunique0 ]
        end.
        rewrite <- map_map in Hunique.
          unfold fst in *; induction (map (fun x: expr * TypeName => let (y,_) := x in y) es);
            auto; simpl in *.
        inversion_clear H0; repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion_clear Hin_rep; inversion_clear Hin_gen'; auto.
        -- apply H; auto. unique_sublist_tac.
        -- apply replace_comatches_reflects_comatch_names in H0.
           unfold gfun_bod_named in *; unfold gfun_bod in *.
           rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H2.
           rewrite <- concat_map in H2; rewrite map_map in H2.
           apply uniqueness_app_not_in in Hunique; rewrite Forall_forall in Hunique; apply (Hunique qn); auto.
           apply (in_map_concat _ _ qn _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
           clear - H2.
           unshelve epose proof (map_map (generate_gfuns_from_expr tn)); [> exact True|].
           repeat match goal with
                  | [  |- context [map (fun x => ?f (@?g x)) ?ls] ] =>
                      rewrite <- (map_map g f)
                  end.
           repeat match goal with
                  | [  |- context [concat (map (concat (A:=?B)) (map ?f ?ls))] ] =>
                    rewrite (@map_concat_switch' _ B);
                      rewrite <- concat_map
                  end.
           rewrite map_map; auto.
        -- rewrite <- map_map with (g := map snd) in H2.
           rewrite <- concat_map in H2; rewrite map_map in H2.
           apply (generate_gfuns_reflects_comatch_names tn) in H2.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in H0.
           apply uniqueness_app_not_in in Hunique.
           rewrite Forall_forall in Hunique; apply (Hunique qn); auto.
        -- apply IHl; auto. unique_sublist_tac.
      * let lst_gen := match type of Hin_gen' with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end
        in rewrite <- map_map with (l := lst_gen) in Hin_gen';
        rewrite <- flat_map_concat_map with (l := map _ lst_gen) in Hin_gen';
        unfold gfun_bod_named in *; unfold gfun_bod in *;
        rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in Hin_gen';
        rewrite <- concat_map in Hin_gen';
        rewrite map_map in Hin_gen';
        apply (generate_gfuns_reflects_comatch_names_flat tn) in Hin_gen';
        let lst_rep := match type of Hin_gen' with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end in idtac.
        rewrite <- map_map with (g := replace_comatches_by_gfun_calls tn) in Hin_rep; rewrite map_map in Hin_rep.
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin_rep.
        rewrite flat_map_concat_map in Hin_gen'; rewrite map_map in Hin_rep, Hin_gen'.
        inversion_clear Hunique.
        apply uniqueness_app_not_in in H2; rewrite Forall_forall in H2; eapply H2; eauto.
    + inversion_clear Hin_rep as [H1 | [H1 | H1]]; inversion_clear Hin_gen;
      try (rewrite map_map in H1; simpl in H1;
        rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := fst) in H1 ||
                                                                                                                          rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in H1).
      * inversion_clear Hunique; subst.
        clear H0 H.
        rewrite <- map_map with (g := map snd) in H2;
          rewrite <- concat_map in H2; rewrite map_map in H2.
        rewrite <- map_map with (f := fst) in H2.
        rewrite <- flat_map_concat_map with (l := map fst es) in H2.
        apply generate_gfuns_reflects_comatch_names_flat in H2;
          rewrite flat_map_concat_map in H2; rewrite map_map in H2.
        apply H3; auto.
      * inversion_clear Hunique; subst.
        clear H0 H.
        rewrite <- map_map with (g := map snd) in H2;
          rewrite <- concat_map in H2; rewrite map_map in H2.
        rewrite <- map_map with (l := ls) in H2.
        rewrite <- flat_map_concat_map with (l := map snd ls) in H2.
        apply generate_gfuns_reflects_comatch_names_flat in H2;
          rewrite flat_map_concat_map in H2; rewrite map_map in H2.
        apply H3; auto.
      * clear H; rewrite <- map_map with (f := fst) in H2.
        inversion_clear Hunique as [|_x __x _ Hunique'].
        match type of Hunique' with
        | unique (?l ++ ?r) =>
          let H := fresh "Hunique0" in
          assert (H: unique l); [> unique_sublist_tac | clear Hunique' ]
        end.
        rewrite <- map_map in Hunique0.
          unfold fst in *; induction (map (fun x: expr * TypeName => let (y,_) := x in y) es);
            auto; simpl in *.
        inversion_clear H0; repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion_clear H1; inversion_clear H2; auto.
        -- apply H; auto. unique_sublist_tac.
        -- apply replace_comatches_reflects_comatch_names in H0.
           unfold gfun_bod_named in *; unfold gfun_bod in *.
           rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H1.
           rewrite <- concat_map in H1; rewrite map_map in H1.
           apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
           apply (in_map_concat _ _ qn _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
           clear - H1.
           epose proof (map_map (generate_gfuns_from_expr tn)).
           repeat match goal with
                  | [  |- context [map (fun x => ?f (@?g x)) ?ls] ] =>
                      rewrite <- (map_map g f)
                  end.
           repeat match goal with
                  | [  |- context [concat (map (concat (A:=?B)) (map ?f ?ls))] ] =>
                    rewrite (@map_concat_switch' _ B);
                      rewrite <- concat_map
                  end.
           rewrite map_map; auto.
        -- rewrite <- map_map with (g := map snd) in H1.
           rewrite <- concat_map in H1; rewrite map_map in H1.
           apply (generate_gfuns_reflects_comatch_names tn) in H1.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in H0.
           apply uniqueness_app_not_in in Hunique0.
           rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
        -- apply IHl; auto. unique_sublist_tac.
      * let lst_gen := match type of H2 with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end
        in rewrite <- map_map with (l := lst_gen) in H2;
        rewrite <- flat_map_concat_map with (l := map _ lst_gen) in H2;
        unfold gfun_bod_named in *; unfold gfun_bod in *;
        rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H2;
        rewrite <- concat_map in H2;
        rewrite map_map in H2;
        apply (generate_gfuns_reflects_comatch_names_flat tn) in H2;
        let lst_rep := match type of H2 with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end in
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in H1.
        rewrite flat_map_concat_map in H2; rewrite map_map in H1, H2.
        inversion_clear Hunique.
        apply uniqueness_app_not_in in H4; rewrite Forall_forall in H4; eapply H4; eauto.
      * let lst_gen := match type of H2 with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end
        in rewrite <- map_map with (l := lst_gen) in H2;
        rewrite <- flat_map_concat_map with (l := map _ lst_gen) in H2;
        unfold gfun_bod_named in *; unfold gfun_bod in *;
        rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H2;
        rewrite <- concat_map in H2;
        rewrite map_map in H2;
        apply (generate_gfuns_reflects_comatch_names_flat tn) in H2;
        let lst_rep := match type of H2 with
                   | context [?lst] =>
                     match lst with
                     | (_ _ _) => fail 1
                     | _ => match type of lst with
                           | list _ => lst
                           end
                     end
                       end in
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in H1.
        rewrite flat_map_concat_map in H2; rewrite map_map in H1, H2.
        inversion_clear Hunique.
        apply uniqueness_app_not_in in H4; rewrite Forall_forall in H4; eapply H4; eauto.
      * clear H0; rewrite <- map_map with (f := snd) in H2.
        inversion_clear Hunique as [| _x __x _ Hunique'].
        match type of Hunique' with
        | unique (?l ++ ?r) =>
          let H := fresh "Hunique0" in
          assert (H: unique r); [> unique_sublist_tac | clear Hunique' ]
        end.
        rewrite <- map_map in Hunique0.
          unfold snd in Hunique0, H2 at 4, H1; induction (map (fun x: ScopedName * expr => let (_,y) := x in y) ls);
            auto; simpl in *.
        inversion_clear H; repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
        rewrite in_app_iff in *.
        inversion_clear H1; inversion_clear H2; auto.
        -- apply H0; auto. unique_sublist_tac.
        -- apply replace_comatches_reflects_comatch_names in H.
           unfold gfun_bod_named in *; unfold gfun_bod in *.
           rewrite <- map_map with (f := fun x => snd (snd x)) (g := map snd) in H1.
           rewrite <- concat_map in H1; rewrite map_map in H1.
           apply uniqueness_app_not_in in Hunique0; rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
           apply (in_map_concat _ _ qn _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
           clear - H1.
           epose proof (map_map (generate_gfuns_from_expr tn)).
           repeat match goal with
                  | [  |- context [map (fun x => ?f (@?g x)) ?ls] ] =>
                      rewrite <- (map_map g f)
                  end.
           repeat match goal with
                  | [  |- context [concat (map (concat (A:=?B)) (map ?f ?ls))] ] =>
                    rewrite (@map_concat_switch' _ B);
                      rewrite <- concat_map
                  end.
           rewrite map_map; auto.
        -- rewrite <- map_map with (g := map snd) in H1.
           rewrite <- concat_map in H1; rewrite map_map in H1.
           apply (generate_gfuns_reflects_comatch_names tn) in H1.
           apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in H.
           apply uniqueness_app_not_in in Hunique0.
           rewrite Forall_forall in Hunique0; apply (Hunique0 qn); auto.
        -- apply IHl; auto. unique_sublist_tac.
  - repeat (rewrite map_app in Hin_gen; rewrite concat_app in Hin_gen).
    rewrite in_app_iff in *.
    inversion_clear Hin_rep; inversion_clear Hin_gen.
    * apply IHe1; auto; unique_sublist_tac.
    * apply replace_comatches_reflects_comatch_names in H.
      rewrite <- map_map with (g := map snd) (f := fun x => snd (@snd gfun_sig (QName * list (ScopedName * expr)) x)) in H0;
        rewrite <- concat_map in H0; rewrite map_map in H0.
      apply (generate_gfuns_reflects_comatch_names tn _ qn) in H0.
      rewrite <- uniqueness_app_rewrite in Hunique.
      inversion Hunique as [Hx [Hxx Hxxx]].
      rewrite Forall_forall in Hxxx.
      apply (Hxxx qn); auto.
    * apply replace_comatches_reflects_comatch_names in H.
      rewrite <- map_map with (g := map snd) (f := fun x => snd (@snd gfun_sig (QName * list (ScopedName * expr)) x)) in H0;
        rewrite <- concat_map in H0; rewrite map_map in H0.
      apply (generate_gfuns_reflects_comatch_names tn _ qn) in H0.
      rewrite <- uniqueness_app_rewrite in Hunique.
      inversion Hunique as [Hx [Hxx Hxxx]].
      rewrite Forall_forall in Hxxx.
      apply (Hxxx qn); auto.
    * apply IHe2; auto; unique_sublist_tac.
      Unshelve. all: apply True.
Qed.

End split_comatches_into_replace_generate_sec.

Lemma generate_gfuns_unique_comatches_propagates: forall (tn : TypeName) (e : expr),
    unique (collect_comatch_names e) ->
    unique (concat (map (fun x : ScopedName * expr => collect_comatch_names (snd x))
                        (concat (map (fun x : gfun_sig * gfun_bod_named => snd (snd x)) (generate_gfuns_from_expr tn e))))).
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
    apply generate_gfuns_reflects_comatch_names in Hin.
    pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1.
    rewrite concat_map in Hnin at 1.
    rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_gfuns_from_expr tn)).
    unfold gfun_bod_named in *.
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
      apply generate_gfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      unfold gfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      unfold gfun_bod_named in *.
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
    apply generate_gfuns_reflects_comatch_names in Hin.
    pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1.
    rewrite concat_map in Hnin at 1.
    rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_gfuns_from_expr tn)).
    unfold gfun_bod_named in *.
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
      apply generate_gfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      unfold gfun_bod_named in *.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1.
      rewrite concat_map in Hnin at 1.
      rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      unfold gfun_bod_named in *.
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
    apply generate_gfuns_reflects_comatch_names in Hin.
    pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
    epose proof in_concat_stuff as Hlem'.
    rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
    specialize (Hlem' (generate_gfuns_from_expr tn)).
    specialize Hlem' with (2 := Hnin).
    apply uniqueness_app_not_in in H; rewrite Forall_forall in H; specialize (H qn Hin); apply H.
    apply Hlem'; intros. apply Hlem.
    rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
  - repeat (rewrite map_app; rewrite concat_app).
    rewrite concat_app in H.
    rename H into Hunique.
    repeat unique_app_destr_tac.
    apply uniqueness_app_3way; auto.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique2; rewrite Forall_forall in Hunique2; specialize (Hunique2 qn Hin); apply Hunique2.
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
      apply generate_gfuns_reflects_comatch_names in Hin.
      pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
      epose proof in_concat_stuff as Hlem'.
      rewrite <- map_map in Hnin at 1; rewrite concat_map in Hnin at 1; rewrite map_map in Hnin at 1.
      specialize (Hlem' (generate_gfuns_from_expr tn)).
      rewrite <- map_map with (g := generate_gfuns_from_expr tn) in Hnin.
      specialize Hlem' with (2 := Hnin).
      apply uniqueness_app_not_in in Hunique3; rewrite Forall_forall in Hunique3; specialize (Hunique3 qn Hin); apply Hunique3.
      rewrite <- map_map.
      apply Hlem'; intros. apply Hlem.
      rewrite <- map_map; rewrite concat_map; rewrite map_map; auto.
    + unshelve epose proof (uniqueness_app _ _ Hunique0 Hunique2 _) as Htmp; clear Hunique0 Hunique2;
        [> rewrite Forall_forall in *; intros; intro Hin; eapply Hunique_f; eauto |].
      rename Htmp into Hunique.
      rewrite <- app_nil_l in Hunique; apply unique_app_switch in Hunique; rewrite app_nil_l in Hunique.
      apply uniqueness_app_not_in in Hunique.
      rewrite Forall_forall; intros qn Hin Hnin.
      clear - H1 Hunique Hin Hnin.
      apply generate_gfuns_reflects_comatch_names in Hin.
      rewrite <- map_map with (l := es) in Hnin;
      rewrite <- flat_map_concat_map with (l := map fst es) in Hnin;
      apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin;
      rewrite flat_map_concat_map in Hnin; rewrite map_map in Hnin.
      rewrite Forall_forall in Hunique; eapply Hunique; eauto.
    + unshelve epose proof (uniqueness_app _ _ Hunique0 Hunique3 _) as Htmp; clear Hunique0 Hunique2;
        [> rewrite Forall_forall in *; intros; intro Hin; eapply Hunique_f; eauto |].
      rename Htmp into Hunique.
      rewrite <- app_nil_l in Hunique; apply unique_app_switch in Hunique; rewrite app_nil_l in Hunique.
      apply uniqueness_app_not_in in Hunique.
      rewrite Forall_forall; intros qn Hin Hnin.
      clear - H1 Hunique Hin Hnin.
      apply generate_gfuns_reflects_comatch_names in Hin.
      rewrite <- map_map with (l := ls) in Hnin;
      rewrite <- flat_map_concat_map with (l := map snd ls) in Hnin;
      apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin;
      rewrite flat_map_concat_map in Hnin; rewrite map_map in Hnin.
      rewrite Forall_forall in Hunique; eapply Hunique; eauto.
    + clear - Hunique1_f.
      rewrite Forall_forall in *; intros qn Hes Hls.
      rewrite <- map_map with (l := ls) in Hls; rewrite <- map_map with (l := es) in Hes.
      rewrite <- flat_map_concat_map with (l := map snd ls) in Hls;
        rewrite <- flat_map_concat_map with (l := map fst es) in Hes.
      apply (generate_gfuns_reflects_comatch_names_flat tn) in Hls;
        apply (generate_gfuns_reflects_comatch_names_flat tn) in Hes.
      rewrite flat_map_concat_map in Hls, Hes; rewrite map_map in Hls, Hes.
      eapply Hunique1_f; eauto.
  - repeat (rewrite map_app; rewrite concat_app).
    inversion_clear H as [| _x __x Hnin_n Hunqiue]. rewrite concat_app in Hunqiue.
    unique_app_destr_tac.
    apply uniqueness_app_3way; auto.
    + name_destruct_tac; simpl; try apply Unique_nil.
      rewrite app_nil_r.
      rewrite map_map; simpl.
      clear - Hunqiue1 H0.
      induction ls; auto; simpl in *; inversion_clear H0; unique_app_destr_tac.
      apply uniqueness_app; auto; clear IHls.
      * generalize dependent (snd a); intros e Hunique Hf.
        pose proof (replace_comatches_by_gfun_calls_no_new_comatches tn e).
        unique_sublist_tac.
      * rewrite Forall_forall; intros qn Hin Hnin.
        apply replace_comatches_reflects_comatch_names in Hin.
        rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hnin.
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hnin.
        rewrite Forall_forall in Hunqiue1_f; eapply Hunqiue1_f; eauto.
        rewrite map_map in Hnin; auto.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_comatch_names in Hin.
      rewrite <- map_map with (l := es) in Hnin;
        rewrite <- flat_map_concat_map with (l := map fst es) in Hnin;
        apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin;
        rewrite flat_map_concat_map in Hnin;
        rewrite map_map in Hnin.
      unique_app_destr_tac. rewrite Forall_forall in Hunqiue0_f; eapply Hunqiue0_f; eauto.
    + match goal with
      | [ Hf: Forall _ (map _ ?lst), Huniquex: unique _ |- _ ] =>
        clear - Hf Huniquex;
        induction lst; inversion_clear Hf; auto; simpl;
          repeat (rewrite map_app; rewrite concat_app);
          simpl in Huniquex;
          apply uniqueness_app; [> solve [ IH_tac; unfold snd in *; unfold fst in *; unique_sublist_tac] .. | ]
      end.
      rewrite Forall_forall; intros qn Hin Hnin.
      apply generate_gfuns_reflects_comatch_names in Hin.
      rewrite <- map_map with (l := ls) in Hnin;
        rewrite <- flat_map_concat_map with (l := map snd ls) in Hnin;
        apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin;
        rewrite flat_map_concat_map in Hnin;
        rewrite map_map in Hnin.
      unique_app_destr_tac. rewrite Forall_forall in Hunqiue1_f; eapply Hunqiue1_f; eauto.
    + name_destruct_tac; simpl; [> | easy].
      rewrite app_nil_r.
      clear - Hunqiue_f.
      rewrite Forall_forall in *; intros qn Hin Hnin.
      rewrite <- map_map with (g := collect_comatch_names) in Hin;
        rewrite map_map with (g := snd) in Hin; simpl in *.
      rewrite <- map_map with (l := ls) in Hin; rewrite map_map in Hin.
      apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin.
      rewrite <- map_map with (l := es) in Hnin.
      rewrite <- flat_map_concat_map with (l := map fst es) in Hnin.
      apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin.
      rewrite flat_map_concat_map in Hnin; rewrite map_map in *.
      eapply Hunqiue_f; eauto.
    + name_destruct_tac; simpl; [> | easy].
      rewrite app_nil_r.
      rewrite Forall_forall; intros qn Hin_rep Hin_gen.
      clear - Hin_gen Hin_rep Hunqiue1 H0.
      induction ls; auto; simpl in *; inversion_clear H0; unique_app_destr_tac.
      repeat (rewrite map_app in *; rewrite concat_app in * ).
      rewrite in_app_iff in *.
      inversion_clear Hin_rep as [Hin_rep' | Hin_rep'];
        inversion_clear Hin_gen as [Hin_gen' | Hin_gen']; auto.
      * eapply split_comatches_into_replace_generate.
        -- eapply Hunqiue0.
        -- split; eauto.
           rewrite <- map_map with (g := map snd); rewrite <- concat_map; rewrite map_map; auto.
      * apply replace_comatches_reflects_comatch_names in Hin_rep'.
        rewrite <- map_map with (l := ls) in Hin_gen'.
        rewrite <- flat_map_concat_map with (l := map snd ls) in Hin_gen'.
        apply (generate_gfuns_reflects_comatch_names_flat tn) in Hin_gen';
          rewrite flat_map_concat_map in Hin_gen'.
        rewrite map_map in Hin_gen'.
        rewrite Forall_forall in Hunqiue1_f; eapply Hunqiue1_f; eauto.
      * rewrite <- map_map in Hin_rep'; rewrite map_map with (g := snd) in Hin_rep'; simpl in Hin_rep'.
        rewrite <- map_map with (f := snd) in Hin_rep'; rewrite map_map in Hin_rep'.
        apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin_rep'.
        rewrite map_map in Hin_rep'.
        apply (generate_gfuns_reflects_comatch_names tn) in Hin_gen'.
        rewrite Forall_forall in Hunqiue1_f; eapply Hunqiue1_f; eauto.

    + clear - Hunqiue_f.
      rewrite Forall_forall in *; intros qn Hnin Hin.
      rewrite <- map_map with (l := es) in Hnin;
        rewrite <- map_map with (l := ls) in Hin.
      rewrite <- flat_map_concat_map with (l := map fst es) in Hnin;
        rewrite <- flat_map_concat_map with (l := map snd ls) in Hin.
      apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin;
        apply (generate_gfuns_reflects_comatch_names_flat tn) in Hin.
      rewrite flat_map_concat_map in Hin, Hnin; rewrite map_map in *.
      eapply Hunqiue_f; eauto.
  - repeat (rewrite map_app; rewrite concat_app).
    rewrite <- uniqueness_app_rewrite in H; inversion_clear H; inversion_clear H1.
    apply uniqueness_app; auto.
    rewrite Forall_forall; intros qn Hin Hnin.
    apply generate_gfuns_reflects_comatch_names in Hin.
    pose proof (fun qn e => generate_gfuns_reflects_comatch_names tn e qn) as Hlem.
    rewrite Forall_forall in H2; specialize (H2 qn Hin); apply H2; auto.
Qed.

Lemma new_comatch_names_unique : forall p tn,
  comatch_names_unique
    (map (fun x : Name * expr => (fst x, replace_comatches_by_gfun_calls tn (snd x)))
       (program_fun_bods p))
    (map
       (fun x : QName * list (ScopedName * expr) =>
        (fst x,
        map
          (fun y : ScopedName * expr => (fst y, replace_comatches_by_gfun_calls tn (snd y)))
          (snd x))) (program_cfun_bods_g p)
    ++ [])
    (map
       (fun x : QName * list (ScopedName * expr) =>
        (fst x,
        map
          (fun y : ScopedName * expr => (fst y, replace_comatches_by_gfun_calls tn (snd y)))
          (snd x))) (program_gfun_bods_g p)
     ++ new_gfun_bods_l p tn).
Proof.
  intros p tn.
  unfold comatch_names_unique.
  rewrite app_nil_r.
  repeat rewrite map_app. repeat rewrite concat_app. repeat rewrite map_app. rewrite concat_app.
  match goal with
  | [  |- unique (?l1 ++ ?l2 ++ ?l3 ++ ?l4) ] =>
    reassoc (l1 ++ l2 ++ l3 ++ l4) ((l1 ++ l2 ++ l3) ++ l4)
  end.
  apply uniqueness_app.
  - apply uniqueness_app_3way; repeat rewrite map_compose; simpl; try rewrite concat_map; repeat rewrite map_compose;

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
           apply replace_comatches_by_gfun_calls_no_new_comatches
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
             apply replace_comatches_by_gfun_calls_no_new_comatches
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
               apply replace_comatches_by_gfun_calls_no_new_comatches
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
      [> | unique_xfun_tac | unique_xfun_tac | forall_fun_tac | forall_fun_tac | ].

  + apply uniqueness_sublist with (tot := concat (map (fun a => collect_comatch_names (snd a)) (program_fun_bods p))).
    * apply sublist_concat.
      induction (program_fun_bods p); try apply Forall_nil.
      apply Forall_cons; try assumption.
      apply replace_comatches_by_gfun_calls_no_new_comatches.
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
      apply comatch_names_unique_global_sublist in H; unfold comatch_names_unique in H.
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
                 apply replace_comatches_by_gfun_calls_no_new_comatches
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
      apply replace_comatches_by_gfun_calls_no_new_comatches
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
   unfold new_gfun_bods_l.
   repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
   repeat rewrite map_map in *.
   repeat unique_app_destr_tac.
   apply uniqueness_app_3way.
   + clear - H0.
     induction (program_fun_bods p); auto; simpl in *.
     repeat (rewrite map_app; rewrite concat_app).
     unique_app_destr_tac.
     apply uniqueness_app; auto.
     * apply generate_gfuns_unique_comatches_propagates; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_gfuns_reflects_comatch_names in Hin.
       rewrite Forall_forall in H0_f; eapply H0_f; eauto.
       rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
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
       -- apply generate_gfuns_unique_comatches_propagates; auto.
       -- rewrite Forall_forall; intros qn Hin Hnin.
          rewrite Forall_forall in H0_f; eapply H0_f.
          ++ eapply (generate_gfuns_reflects_comatch_names tn _ qn); auto.
          ++ rewrite <- map_map.
             eapply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
             clear - Hnin.
             induction (map snd l); auto.
             simpl in *.
             repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
             rewrite in_app_iff; rewrite in_app_iff in Hnin.
             inversion_clear Hnin; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_gfuns_reflects_comatch_names_flat in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite map_map in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite Forall_forall in H3_f; eapply H3_f; eauto.
       rewrite <- map_map; rewrite <- flat_map_concat_map.
       apply generate_gfuns_reflects_comatch_names_flat in Hin; auto.
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
       -- apply generate_gfuns_unique_comatches_propagates; auto.
       -- rewrite Forall_forall; intros qn Hin Hnin.
          rewrite Forall_forall in H0_f; eapply H0_f.
          ++ eapply (generate_gfuns_reflects_comatch_names tn _ qn); auto.
          ++ rewrite <- map_map.
             eapply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
             clear - Hnin.
             induction (map snd l); auto.
             simpl in *.
             repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin).
             rewrite in_app_iff; rewrite in_app_iff in Hnin.
             inversion_clear Hnin; auto.
     * rewrite Forall_forall; intros qn Hin Hnin.
       apply generate_gfuns_reflects_comatch_names_flat in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite map_map in Hnin; rewrite flat_map_concat_map in Hnin.
       rewrite Forall_forall in H2_f; eapply H2_f; eauto.
       rewrite <- map_map; rewrite <- flat_map_concat_map.
       apply generate_gfuns_reflects_comatch_names_flat in Hin; auto.
   + clear - H_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H_f.
     * clear H_f Hnin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
       unfold fun_bod in *.
       induction (@map _ expr snd (program_fun_bods p)); eauto; simpl in *.
       repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
       rewrite in_app_iff in *.
       inversion_clear Hin; auto.
     * rewrite in_app_iff; right. unfold gfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_gfuns_reflects_comatch_names_flat tn); auto. repeat rewrite flat_map_concat_map in *; auto.
   + clear - H_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H_f.
     * clear H_f Hnin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
       unfold fun_bod in *.
       induction (@map _ expr snd (program_fun_bods p)); eauto; simpl in *.
       repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
       rewrite in_app_iff in *.
       inversion_clear Hin; auto.
     * rewrite in_app_iff; left. unfold gfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_gfuns_reflects_comatch_names_flat tn); auto. repeat rewrite flat_map_concat_map in *; auto.
   + clear - H1_f. rewrite Forall_forall in *; intros qn Hin Hnin.
     eapply H1_f.
     * clear H1_f Hin. rewrite <- map_map.
       apply (in_map_concat _ _ _ _ (fun qn e => generate_gfuns_reflects_comatch_names tn e qn)).
       rewrite <- flat_map_concat_map with (l := program_cfun_bods_g p).
       unfold cfun_bod_named in *; unfold cfun_bod in *.
       induction (@map _ expr snd (flat_map snd (program_cfun_bods_g p))); eauto; simpl in *.
       repeat (rewrite map_app in Hnin; rewrite concat_app in Hnin); eauto.
       rewrite in_app_iff in *.
       inversion_clear Hnin; auto.
     * unfold gfun_bod_named in *; unfold gfun_bod in *.
       rewrite <- map_map. rewrite <- flat_map_concat_map.
       apply (generate_gfuns_reflects_comatch_names_flat tn).
       repeat rewrite flat_map_concat_map in *; auto.
 - unfold new_gfun_bods_l. repeat rewrite map_map; simpl.
   repeat rewrite concat_map; repeat (rewrite map_map; simpl).
   rewrite Forall_forall; intros qn Hin Hnin.
   repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
   repeat rewrite in_app_iff in *.
   rename Hin into Hin'; rename Hnin into Hnin';
     inversion_clear Hin' as [Hin|[Hin|Hin]]; inversion_clear Hnin' as [Hnin|[Hnin|Hnin]].
   + rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hin.
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
       induction (generate_gfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_comatches_reflects_comatch_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_gfuns_reflects_comatch_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_gfuns_reflects_comatch_names tn).
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
     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) in Hin.
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hnin. rewrite <- flat_map_concat_map. apply (generate_gfuns_reflects_comatch_names_flat tn).
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
     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) in Hin.
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hnin. rewrite <- flat_map_concat_map. apply (generate_gfuns_reflects_comatch_names_flat tn).
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
     apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin.
     rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hin.
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)).
     induction (program_cfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion Hin; auto; left.
     rewrite map_map in H; simpl in H.
     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in H; auto.
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
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin.
     rewrite <- concat_map in Hin; repeat rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); clear H0; auto.
   + rewrite <- map_map in Hin. rewrite <- concat_map in Hin.
     rewrite <- map_map with (f := snd) (g := map (fun y => (fst y, replace_comatches_by_gfun_calls tn (snd y)))) in Hin.
     rewrite <- concat_map in Hin; repeat rewrite <- flat_map_concat_map in Hin; rewrite flat_map_concat_map in Hin.
     rewrite map_map in Hin; simpl in Hin. rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hin.
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
       induction (generate_gfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_comatches_reflects_comatch_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_gfuns_reflects_comatch_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_gfuns_reflects_comatch_names tn).
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
     apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin.
     rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); auto.
     clear - Hin.
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)).
     induction (program_gfun_bods_g p); auto; simpl in *.
     repeat (repeat rewrite map_app in *; rewrite concat_app in * ).
     rewrite in_app_iff in *.
     inversion Hin; auto; left.
     rewrite map_map in H; simpl in H.
     rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in H; auto.
   + rewrite <- map_map in Hin. rewrite <- concat_map in Hin.
     rewrite <- map_map with (f := snd) (g := map (fun y => (fst y, replace_comatches_by_gfun_calls tn (snd y)))) in Hin.
     rewrite <- concat_map in Hin; repeat rewrite <- flat_map_concat_map in Hin; rewrite flat_map_concat_map in Hin.
     rewrite map_map in Hin; simpl in Hin. rewrite <- map_map with (g := fun x => collect_comatch_names (replace_comatches_by_gfun_calls tn x)) (f := snd) in Hin.
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
       induction (generate_gfuns_from_expr tn a); auto; simpl in *.
       rewrite map_app in *; rewrite concat_app in *; rewrite in_app_iff in *.
       inversion_clear H1; auto; left.
       rewrite <- map_map in H; auto.
     * apply replace_comatches_reflects_comatch_names in H0.
       rewrite <- map_map in H1. rewrite <- concat_map in H1.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       rewrite map_map in H1.
       apply (generate_gfuns_reflects_comatch_names_flat tn); auto.
     * apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in H0.
       rewrite flat_map_concat_map in H_f.
       rewrite Forall_forall in H_f; apply (H_f qn); auto.
       apply (generate_gfuns_reflects_comatch_names tn).
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
     apply (in_map_concat _ _ _ _ (replace_comatches_reflects_comatch_names tn)) in Hin.
     rewrite <- map_map in Hnin; rewrite <- concat_map in Hnin; rewrite map_map in Hnin.
     apply (generate_gfuns_reflects_comatch_names_flat tn) in Hnin.
     rewrite <- concat_map in Hin; repeat rewrite flat_map_concat_map in Hnin.
     rewrite Forall_forall in H0; apply (H0 qn); clear H0; auto.
Qed.


(* Note this assumes that the input program contains no functions annotated as local.
   (If there are local consumer functions, this just returns the original program.)
 *)
Definition lift_comatch_to_program (p : program) (tn : TypeName) : program :=
match Nat.eq_dec (length (skeleton_gfun_sigs_l (program_skeleton p))) O with
| left eq2 =>
let Uniq := new_gfun_sigs_names_unique p tn eq2 in
match Nat.eq_dec (length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn Uniq))) O with
| left eq =>
{|
      (* Skeleton *)
      program_skeleton := lift_comatch_to_skeleton p tn (new_gfun_sigs_names_unique p tn eq2);
      (* Ordinary functions *)
      program_fun_bods := map (fun x => (fst x, replace_comatches_by_gfun_calls tn (snd x))) (program_fun_bods p);
      program_has_all_fun_bods := new_has_all_funbods p tn Uniq (program_has_all_fun_bods p);
      program_fun_bods_typecheck := new_funbods_typecheck p tn Uniq (program_fun_bods_typecheck p);
      (* Consumer functions *)
      program_cfun_bods_g := map (fun x => (fst x, map (fun y => (fst y, replace_comatches_by_gfun_calls tn (snd y))) (snd x))) (program_cfun_bods_g p);
      program_has_all_cfun_bods_g := new_has_all_cfunbods_g p tn Uniq (program_has_all_cfun_bods_g p);
      program_cfun_bods_typecheck_g := new_cfunbods_g_typecheck p tn Uniq (program_cfun_bods_typecheck_g p);
      program_cfun_bods_l := [];
      program_has_all_cfun_bods_l := new_has_all_cfunbods_l p tn Uniq eq;
      program_cfun_bods_typecheck_l := Forall_nil _;
      (* Generator functions *)
      program_gfun_bods_g := map (fun x => (fst x, map (fun y => (fst y, replace_comatches_by_gfun_calls tn (snd y))) (snd x))) (program_gfun_bods_g p);
      program_has_all_gfun_bods_g := new_has_all_gfunbods_g p tn Uniq (program_has_all_gfun_bods_g p);
      program_gfun_bods_typecheck_g := new_gfunbods_g_typecheck p tn Uniq (program_gfun_bods_typecheck_g p);
      program_gfun_bods_l := new_gfun_bods_l p tn;
      program_has_all_gfun_bods_l := new_has_all_gfunbods_l p tn Uniq eq2;
      program_gfun_bods_typecheck_l := new_gfun_bods_l_typecheck p tn Uniq eq2;
      (* Uniqueness conditions *)
      program_match_names_unique := new_match_names_unique p tn;
      program_comatch_names_unique := new_comatch_names_unique p tn;
   |}
| _ => p
end
| _ => p
end.
