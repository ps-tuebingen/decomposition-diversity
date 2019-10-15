(* Standard library imports *)
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Import ListNotations.
(* Project related imports *)
Require Import LiftComatch.
Require Import DefuncI.
Require Import DefuncII.
Require Import DefuncIII.
Require Import BodyTypeDefs.
Require Import ProgramDef.
Require Import Typechecker.
Require Import UtilsTypechecker.
Require Import AST.
Require Import Names.
Require Import GenericLemmas.
Require Import OptionMonad.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import Subterm.
Require Import SwitchIndices.

(**************************************************************************************************)
(** * Defunctionalization Part IV:                                                                *)
(**                                                                                               *)
(** Chains comatch lifting and (core) defunctionalization                                         *)
(**************************************************************************************************)

(* Bridges the two definitions as used in LiftComatch and DefuncIII *)
Lemma no_comatches_bridge : forall tn e,
  contains_no_comatches tn e -> no_comatches tn e.
Proof with try discriminate; eauto.
intros. unfold no_comatches. intros. unfold contains_no_comatches in H.
induction e using expr_strong_ind.
- inversion H0; subst... inversion H2.
- rewrite Forall_forall in H1. inversion H0; subst... inversion H3; subst.
  apply H1 with (x:=e2)... clear - H H6. cbn in H. generalize dependent ls.
  induction ls; intros; [inversion H6|]. cbn in H. rewrite filter_app in H.
  destruct H6; subst.
  + match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    unfold QName in *. rewrite H0 in H...
  + apply IHls... match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    unfold QName in *. rewrite H1 in H. exfalso. symmetry in H. apply app_cons_not_nil in H...
- rewrite Forall_forall in H1. inversion H0; subst... inversion H3; subst.
  + apply IHe... match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    cbn in H. rewrite filter_app in H. unfold QName in *. rewrite H4 in H...
  + apply H1 with (x:=e2)... clear - H H6. cbn in H. generalize dependent ls.
    induction ls; intros; [inversion H6|]. cbn in H. rewrite filter_app in H.
    destruct H6; subst.
    * match goal with [|- ?lhs = _] => case_eq lhs; intros end...
      unfold QName in *. rewrite filter_app in H. rewrite H0 in H.
      exfalso. symmetry in H. apply app_cons_not_nil in H...
    * apply IHls... match goal with [|- ?lhs = _] => case_eq lhs; intros end...
      unfold QName in *. rewrite filter_app in H.
      case_eq (filter (fun x : TypeName * Name => eq_TypeName tn (fst x))
        (collect_comatch_names a)); intros.
      -- rewrite H2 in H. simpl in H. rewrite <- filter_app in H. rewrite H1 in H...
      -- rewrite H2 in H. exfalso. symmetry in H. rewrite <- app_comm_cons in H.
         apply app_cons_not_nil in H...
- rewrite Forall_forall in H1. inversion H0; subst... inversion H3; subst.
  apply H1 with (x:=e2)... clear - H H6. cbn in H. generalize dependent ls.
  induction ls; intros; [inversion H6|]. cbn in H. rewrite filter_app in H.
  destruct H6; subst.
  + match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    unfold QName in *. rewrite H0 in H...
  + apply IHls... match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    unfold QName in *. rewrite H1 in H. exfalso. symmetry in H. apply app_cons_not_nil in H...
- rewrite Forall_forall in H1. inversion H0; subst... inversion H3; subst.
  + apply IHe... match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    cbn in H. rewrite filter_app in H. unfold QName in *. rewrite H4 in H...
  + apply H1 with (x:=e2)... clear - H H6. cbn in H. generalize dependent ls.
    induction ls; intros; [inversion H6|]. cbn in H. rewrite filter_app in H.
    destruct H6; subst.
    * match goal with [|- ?lhs = _] => case_eq lhs; intros end...
      unfold QName in *. rewrite filter_app in H. rewrite H0 in H.
      exfalso. symmetry in H. apply app_cons_not_nil in H...
    * apply IHls... match goal with [|- ?lhs = _] => case_eq lhs; intros end...
      unfold QName in *. rewrite filter_app in H.
      case_eq (filter (fun x : TypeName * Name => eq_TypeName tn (fst x))
        (collect_comatch_names a)); intros.
      -- rewrite H2 in H. simpl in H. rewrite <- filter_app in H. rewrite H1 in H...
      -- rewrite H2 in H. exfalso. symmetry in H. rewrite <- app_comm_cons in H.
         apply app_cons_not_nil in H...
- rewrite Forall_forall in H1. inversion H0; subst... inversion H3; subst.
  apply H1 with (x:=e2)... clear - H H6. cbn in H. generalize dependent ls.
  induction ls; intros; [inversion H6|]. cbn in H. rewrite filter_app in H.
  destruct H6; subst.
  + match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    unfold QName in *. rewrite H0 in H...
  + apply IHls... match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    unfold QName in *. rewrite H1 in H. exfalso. symmetry in H. apply app_cons_not_nil in H...
- rewrite Forall_forall in H1. rewrite Forall_forall in H2.
  inversion H0; subst... inversion H4; subst.
  + apply IHe... match goal with [|- ?lhs = _] => case_eq lhs; intros end...
    cbn in H. rewrite filter_app in H. unfold QName in *. rewrite H5 in H...
  + eapply H2... cbn in H. case_eq (filter (fun x : TypeName * Name => eq_TypeName tn (fst x))
      (collect_comatch_names e2)); intros... apply in_split in H7. destruct H7. destruct H6.
    rewrite <- map_map in H. rewrite H6 in H. rewrite map_app in H. cbn in H.
    repeat (rewrite concat_app in H). cbn in H. repeat (rewrite filter_app in H).
    unfold QName in *. rewrite H5 in H. rewrite <- app_assoc in H.
    match goal with [_ : ?a ++ ?b ++  (_ ++ ?c) ++ ?d = _ |- _] =>
      case_eq a; [intros aEq | intros a0 a' aEq]; rewrite aEq in H; try discriminate;
      case_eq b; [intros bEq | intros b0 b' bEq]; rewrite bEq in H; try discriminate
    end.
  + eapply H1... cbn in H. case_eq (filter (fun x : TypeName * Name => eq_TypeName tn (fst x))
      (collect_comatch_names e2)); intros... apply in_split in H7. destruct H7. destruct H6.
    rewrite <- map_map with (f:=snd) in H. rewrite H6 in H. rewrite map_app in H. cbn in H.
    repeat (rewrite concat_app in H). cbn in H. repeat (rewrite filter_app in H).
    unfold QName in *. rewrite H5 in H.
    match goal with [_ : ?a ++ ?b ++ ?c ++ _ ++ _ = _ |- _] =>
      case_eq a; [intros aEq | intros a0 a' aEq]; rewrite aEq in H; try discriminate;
      case_eq b; [intros bEq | intros b0 b' bEq]; rewrite bEq in H; try discriminate;
      case_eq c; [intros cEq | intros c0 c' cEq]; rewrite cEq in H; try discriminate
    end.
- rewrite Forall_forall in H1. rewrite Forall_forall in H2.
  inversion H0; subst.
  + clear - H. cbn in H. case_eq (eq_TypeName tn (fst n0)); intros; rewrite H0 in H...
    destruct n0. simpl in *. unfold not. intros. inversion H1; subst. rewrite eq_TypeName_refl in H0...
  + inversion H4; subst.
    * eapply H2... cbn in H. case_eq (filter (fun x : TypeName * Name => eq_TypeName tn (fst x))
        (collect_comatch_names e2)); intros... apply in_split in H7. destruct H7. destruct H6.
      rewrite <- map_map in H. rewrite H6 in H. rewrite map_app in H. cbn in H.
      repeat (rewrite concat_app in H). cbn in H. repeat (rewrite filter_app in H).
      unfold QName in *. rewrite H5 in H. rewrite <- app_assoc in H.
      destruct (eq_TypeName tn (fst n0))...
      match goal with [_ : ?a ++  (_ ++ _) ++ _ = _ |- _] =>
        case_eq a; [intros aEq | intros a0 a' aEq]; rewrite aEq in H; try discriminate
      end.
    * eapply H1... cbn in H. case_eq (filter (fun x : TypeName * Name => eq_TypeName tn (fst x))
        (collect_comatch_names e2)); intros... apply in_split in H7. destruct H7. destruct H6.
      rewrite <- map_map with (f:=snd) in H. rewrite H6 in H. rewrite map_app in H. cbn in H.
      repeat (rewrite concat_app in H). cbn in H. repeat (rewrite filter_app in H).
      unfold QName in *. rewrite H5 in H. destruct (eq_TypeName tn (fst n0))...
      rewrite <- app_comm_cons in H.
      match goal with [_ : ?a ++ ?b ++ _ :: _ = _ |- _] =>
        case_eq a; [intros aEq | intros a0 a' aEq]; rewrite aEq in H; try discriminate;
        case_eq b; [intros bEq | intros b0 b' bEq]; rewrite bEq in H; try discriminate
      end.
- inversion H0; subst... inversion H2; subst.
  + apply IHe1... cbn in H. rewrite filter_app in H. apply app_eq_nil in H. destruct H...
  + apply IHe2... cbn in H. rewrite filter_app in H. apply app_eq_nil in H. destruct H...
Qed.

Lemma funs_no_comatches : forall p tn
(eq2 : length (skeleton_gfun_sigs_l (program_skeleton p)) = O)
(eq : length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn
        (new_gfun_sigs_names_unique p tn eq2))) = O),
Forall (no_comatches tn) (map snd (program_fun_bods (lift_comatch_to_program p tn))).
Proof with eauto.
intros. rewrite Forall_forall. intros. apply no_comatches_bridge.
unfold lift_comatch_to_program in H.
destruct (Nat.eq_dec (length (skeleton_gfun_sigs_l (program_skeleton p))) 0).
- destruct (Nat.eq_dec  (length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn
    (new_gfun_sigs_names_unique p tn e)))) 0).
  + simpl in *. rewrite in_map_iff in H. do 2 destruct H. destruct x0. simpl in *. subst.
    rewrite in_map_iff in H0. destruct H0. destruct H. inversion H; subst.
    apply replace_comatches_by_gfun_calls_removes_all_comatches.
  + exfalso. apply n. apply eq.
- exfalso. apply n. apply eq2.
Qed.

Lemma cg_funs_no_comatches : forall p tn bods
(eq2 : length (skeleton_gfun_sigs_l (program_skeleton p)) = O)
(eq : length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn
        (new_gfun_sigs_names_unique p tn eq2))) = O),
((bods = program_cfun_bods_g \/ bods = program_cfun_bods_l) \/
 (bods = program_gfun_bods_g \/ bods = program_gfun_bods_l)) ->
Forall (no_comatches tn) (map snd (flat_map snd (bods (lift_comatch_to_program p tn)))).
Proof with eauto.
intros p tn bods eq2 eq Choice. rewrite Forall_forall. intros. apply no_comatches_bridge.
unfold lift_comatch_to_program in H.
destruct (Nat.eq_dec (length (skeleton_gfun_sigs_l (program_skeleton p))) 0).
- destruct (Nat.eq_dec  (length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn
    (new_gfun_sigs_names_unique p tn e)))) 0).
  + simpl in *. rewrite in_map_iff in H. do 2 destruct H.
    rewrite in_flat_map in H0. do 2 destruct H0.
    destruct Choice as [Choice | Choice]; destruct Choice; subst;
      simpl in H0; [ | exfalso | | shelve]; eauto;
    rewrite in_map_iff in H0; destruct H0; destruct H; inversion H; subst; simpl in *;
    rewrite in_map_iff in H1; destruct H1; destruct H; destruct x0; inversion H; subst;
    apply replace_comatches_by_gfun_calls_removes_all_comatches.
    Unshelve. unfold LiftComatch.new_gfun_bods_l in H0.
    pose proof generate_gfuns_from_expr_contains_no_comatches.
    apply in_app_or in H0. destruct H0; [| apply in_app_or in H0; destruct H0];
      rewrite in_map_iff in H0; do 2 destruct H0; subst;
      rewrite in_flat_map in H2; destruct H2; destruct H0;
      specialize H with (e:=x1)(tn:=tn); rewrite Forall_forall in H;
      apply H in H2; rewrite Forall_forall in H2; apply H2...
  + exfalso. apply n. apply eq.
- exfalso. apply n. apply eq2.
Qed.

Corollary cfuns_g_no_comatches : forall p tn
(eq2 : length (skeleton_gfun_sigs_l (program_skeleton p)) = O)
(eq : length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn
        (new_gfun_sigs_names_unique p tn eq2))) = O),
Forall (no_comatches tn) (map snd (flat_map snd (program_cfun_bods_g (lift_comatch_to_program p tn)))).
Proof with eauto. intros. eapply cg_funs_no_comatches... Qed.

Corollary cfuns_l_no_comatches : forall p tn
(eq2 : length (skeleton_gfun_sigs_l (program_skeleton p)) = O)
(eq : length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn
        (new_gfun_sigs_names_unique p tn eq2))) = O),
Forall (no_comatches tn) (map snd (flat_map snd (program_cfun_bods_l (lift_comatch_to_program p tn)))).
Proof with eauto. intros. eapply cg_funs_no_comatches... Qed.

Corollary gfuns_g_no_comatches : forall p tn
(eq2 : length (skeleton_gfun_sigs_l (program_skeleton p)) = O)
(eq : length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn
        (new_gfun_sigs_names_unique p tn eq2))) = O),
Forall (no_comatches tn) (map snd (flat_map snd (program_gfun_bods_g (lift_comatch_to_program p tn)))).
Proof with eauto. intros. eapply cg_funs_no_comatches... Qed.

Corollary gfuns_l_no_comatches : forall p tn
(eq2 : length (skeleton_gfun_sigs_l (program_skeleton p)) = O)
(eq : length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn
        (new_gfun_sigs_names_unique p tn eq2))) = O),
Forall (no_comatches tn) (map snd (flat_map snd (program_gfun_bods_l (lift_comatch_to_program p tn)))).
Proof with eauto. eauto. intros. eapply cg_funs_no_comatches... Qed.

Lemma no_local_cfuns_after_lift : forall p tn Uniq,
length (skeleton_cfun_sigs_l (program_skeleton p)) = O ->
length (skeleton_cfun_sigs_l (lift_comatch_to_skeleton p tn Uniq)) = O.
Proof with eauto. intros. unfold lift_comatch_to_skeleton... Qed.


(* Note this assumes that the input program contains no functions annotated as local.
   (If there are local consumer or generator functions, this just returns the original program.)
 *)
Definition defunctionalize_program_with_lift (p : program) (tn : TypeName) :=
match Nat.eq_dec (length (skeleton_gfun_sigs_l (program_skeleton p))) O with
| left eq2 =>
let Uniq := new_gfun_sigs_names_unique p tn eq2 in
match Nat.eq_dec (length (skeleton_cfun_sigs_l (program_skeleton p))) O with
| left eq =>
let lifted_prog := lift_comatch_to_program p tn in
let no_local_cfuns := no_local_cfuns_after_lift p tn Uniq eq in
let NoCmFun := funs_no_comatches p tn eq2 no_local_cfuns in
let NoCmCFunG := cfuns_g_no_comatches p tn eq2 no_local_cfuns in
let NoCmCFunL := cfuns_l_no_comatches p tn eq2 no_local_cfuns in
let NoCmGFunG := gfuns_g_no_comatches p tn eq2 no_local_cfuns in
let NoCmGFunL := gfuns_l_no_comatches p tn eq2 no_local_cfuns in
defunctionalize_program lifted_prog tn NoCmFun NoCmCFunG NoCmCFunL NoCmGFunG NoCmGFunL
| _ => p
end
| _ => p
end.
