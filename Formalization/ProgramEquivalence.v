(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: ProgramEquivalence.v                                                                        *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Program.

Require Import GenericLemmas.
Require Import GenericTactics.
Require Import Names.
Require Import AST.
Require Import BodyTypeDefs.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import ProgramDef.
Require Import Subterm.
Require Import Sublist.
Require Import Unique.
Require Import Typechecker.

Require Import InlineMatch.
Require Import LiftMatch.

(* The type of polymorphic permutation functions on lists. Since we don't have parametricity internalized, we have to
spell out that it performs the same permutation whatever type of argument it is used at. *)
Definition perm : Type :=
  {f : forall A, list A -> list A |
                     (forall (B : Type)(ls : list B), Permutation ls (f B ls)) /\
                     (forall (A B : Type) (l : list A)(g : A -> B),f B (map g l) = map g (f A l)) (* Holds by parametricity *)
  }.

Lemma Permutation_Forall : forall (A : Type)(P : A -> Prop)(l l' : list A),
    Forall P l ->
    Permutation l l' ->
    Forall P l'.
Proof.
  intros A P l l' H H0.
  apply Forall_forall; intros. rewrite Forall_forall in H.
  apply H. eapply Permutation_in. apply Permutation_sym. apply H0.
  auto.
Qed.

Lemma Permutation_unique : forall (A : Type) (l l' : list A),
    unique l ->
    Permutation l l' ->
    unique l'.
Proof.
  intros A l l' H H0. induction H0.
  - apply Unique_nil.
  - inversion H; subst. apply Unique_cons; auto.
    intro H_abs. apply H3. eapply Permutation_in. apply Permutation_sym.
    apply H0. auto.
  - inversion H; subst. inversion H3; subst. clear H3 H.
   repeat apply Unique_cons; try auto.
   + intro H_abs. simpl in H_abs. destruct H_abs; subst; try auto.
  - auto.
Qed.

Theorem perm_preserves_cfun_sigs_in_dts : forall (d : dts)(x : cfun_sigs) (f : perm),
    cfun_sigs_in_dts d x ->
    cfun_sigs_in_dts d ((proj1_sig f) cfun_sig x).
Proof.
  intros d x f H.
  unfold perm in *. dependent destruction f. rename x0 into f. destruct a. simpl.
  unfold cfun_sigs_in_dts in *.
  eapply Permutation_Forall.
  - apply H.
  - apply p.
Qed.

Theorem perm_preserves_cfun_sigs_names_unique : forall (x : cfun_sigs) (f : perm),
    cfun_sigs_names_unique x ->
    cfun_sigs_names_unique ((proj1_sig f) cfun_sig x).
Proof.
  intros x f H.
  unfold perm in *. dependent destruction f. rename x0 into f. destruct a. simpl.
  unfold cfun_sigs_names_unique in *.
  generalize dependent (fun x : QName * list TypeName * TypeName => fst (fst x)). intros.
  pose (Permutation_map).
  specialize (p0 _ _ q x (f cfun_sig x) (p cfun_sig x)).
  eapply Permutation_unique. apply H. auto.
Qed.

Definition permuteSkeleton (cfun_perm : perm) (s : skeleton) : skeleton :=
  {|
    (* Datatypes *)
    skeleton_dts := skeleton_dts s;
    skeleton_ctors := skeleton_ctors s;
    skeleton_dts_ctors_in_dts := skeleton_dts_ctors_in_dts s;
    skeleton_dts_ctor_names_unique := skeleton_dts_ctor_names_unique s;
    (* Codatatypes *)
    skeleton_cdts := skeleton_cdts s;
    skeleton_dtors := skeleton_dtors s;
    skeleton_cdts_dtors_in_cdts := skeleton_cdts_dtors_in_cdts s;
    skeleton_cdts_dtor_names_unique := skeleton_cdts_dtor_names_unique s;
    (* Datatypes + Codatatypes *)
    skeleton_dts_cdts_disjoint := skeleton_dts_cdts_disjoint s;
    (* Ordinary functions *)
    skeleton_fun_sigs := skeleton_fun_sigs s;
    skeleton_fun_sigs_names_unique := skeleton_fun_sigs_names_unique s;
    (* Consumer functions *)
    skeleton_cfun_sigs_g := skeleton_cfun_sigs_g s;
    skeleton_cfun_sigs_in_dts_g := skeleton_cfun_sigs_in_dts_g s;
    skeleton_cfun_sigs_names_unique_g := skeleton_cfun_sigs_names_unique_g s;
    (* <<<<<<<<<<<< *)
    skeleton_cfun_sigs_l :=
      (proj1_sig cfun_perm) cfun_sig (skeleton_cfun_sigs_l s);
    skeleton_cfun_sigs_in_dts_l :=
      perm_preserves_cfun_sigs_in_dts (skeleton_dts s) (skeleton_cfun_sigs_l s) cfun_perm (skeleton_cfun_sigs_in_dts_l s);
    skeleton_cfun_sigs_names_unique_l :=
      perm_preserves_cfun_sigs_names_unique (skeleton_cfun_sigs_l s) cfun_perm (skeleton_cfun_sigs_names_unique_l s);
    (* <<<<<<<<<<< *)
    (* Generator functions *)
    skeleton_gfun_sigs_g := skeleton_gfun_sigs_g s;
    skeleton_gfun_sigs_in_cdts_g := skeleton_gfun_sigs_in_cdts_g s;
    skeleton_gfun_sigs_names_unique_g := skeleton_gfun_sigs_names_unique_g s;
    skeleton_gfun_sigs_l := skeleton_gfun_sigs_l s;
    skeleton_gfun_sigs_in_cdts_l := skeleton_gfun_sigs_in_cdts_l s;
    skeleton_gfun_sigs_names_unique_l := skeleton_gfun_sigs_names_unique_l s;
  |}.

Definition SkeletonEquiv (s1 s2: skeleton) (cfun_perm : perm) : Prop :=
  s2 = permuteSkeleton cfun_perm s1.

Definition PP (f : perm) (s2 s1 : skeleton) (c : ctxt) (e : expr) (tn : TypeName) : Prop :=
  SkeletonEquiv s1 s2 f -> s2 / c |- e : tn.
Definition PP0 (f : perm) (s2 s1 : skeleton) (c : ctxt) (es : list expr) (tns : list TypeName) : Prop :=
  SkeletonEquiv s1 s2 f ->  s2 // c ||- es :: tns.
Definition PP1 (f : perm) (s2 s1 : skeleton) (cs : list ctxt) (es : list expr) (tns : list TypeName) : Prop :=
  SkeletonEquiv s1 s2 f ->  s2 /// cs |||- es ::: tns.

Ltac typecheck_equiv_helper :=
  match goal with
    [ H : SkeletonEquiv _ _ _ |-  _ ] =>
    unfold SkeletonEquiv in H; subst; simpl; auto
  end.

Theorem typecheck_equiv : forall (s1 s2 : skeleton) (c : ctxt) (e : expr) (tn : TypeName) (f : perm),
    s1 / c |- e : tn ->
    SkeletonEquiv s1 s2 f ->
    s2 / c |- e : tn.
Proof with try auto; typecheck_equiv_helper.
  intros s1 s2 c e tn f H.
  induction H using type_deriv_ind with (P := PP f s2) (P0 := PP0 f s2) (P1 := PP1 f s2); unfold PP; intros.
  - (* E_Var *)
    constructor. assumption.
  - (* E_Constr *)
    eapply T_Constr...
  - (* E_DestrCall *)
    eapply T_DestrCall...
  - (* E_FunCall *)
    eapply T_FunCall...
  - (* E_ConsFunCall *)
    eapply T_GlobalConsFunCall...
  - (* E_ConsFunCall *)
    eapply T_LocalConsFunCall; try auto.
    clear - H H2. unfold SkeletonEquiv in H2.
    subst. simpl. dependent destruction f. rename x into f. simpl.
    destruct a. eapply Permutation_in; eauto.
  - (* E_GlobalGenFunCall *)
    eapply T_GlobalGenFunCall...
  - (* E_LocalGenFunCall *)
    eapply T_LocalGenFunCall...
  - (* E_Match *)
    eapply T_Match...
  - (* E_CoMatch *)
    eapply T_CoMatch...
  - (* E_Match *)
    eapply T_Let...
  - unfold PP0. intro. apply ListTypeDeriv_Nil.
  - unfold PP0 in *. unfold PP in *. intros.  apply ListTypeDeriv_Cons...
  - unfold PP1. intros. apply ListTypeDeriv'_Nil.
  - unfold PP1 in *. unfold PP in *. intros.  apply ListTypeDeriv'_Cons...
Qed.

Lemma permuteSkeleton_equiv : forall (s : skeleton) (cfun_perm : perm),
    SkeletonEquiv s (permuteSkeleton cfun_perm s) cfun_perm.
Proof.
  intros. unfold SkeletonEquiv. auto.
Qed.

(*******************************************************)
(* Permute Program                                     *)
(*******************************************************)

Theorem program_fun_bods_typecheck_helper : forall (p : program) (cfun_perm : perm),
    fun_bods_typecheck (permuteSkeleton cfun_perm (program_skeleton p)) (program_fun_bods p).
Proof.
  intros p cfun_perm.
  destruct p; simpl in *. clear - program_fun_bods_typecheck. unfold fun_bods_typecheck in *.
  apply Forall_forall. rewrite Forall_forall in program_fun_bods_typecheck. intros.
  specialize (program_fun_bods_typecheck x H).
  destruct program_fun_bods_typecheck as [n [args [tn [H_lookup H_tc]]]].
  exists n. exists args. exists tn. split.
  - clear - H_lookup. unfold lookup_fun_sig in *. destruct program_skeleton. simpl in *. auto.
  - eapply typecheck_equiv.
    + apply H_tc.
    + apply permuteSkeleton_equiv.
Qed.

Theorem program_cfun_bods_g_typecheck_helper : forall (p : program) (cfun_perm : perm),
    cfun_bods_g_typecheck (permuteSkeleton cfun_perm (program_skeleton p)) (program_cfun_bods_g p).
Proof.
  intros p cfun_perm.
  destruct p; simpl. clear - program_cfun_bods_typecheck_g.
  unfold cfun_bods_g_typecheck in *.
  rewrite Forall_forall.  rewrite Forall_forall in program_cfun_bods_typecheck_g.
  intros. specialize (program_cfun_bods_typecheck_g x H).
  destruct program_cfun_bods_typecheck_g as [qn [args [tn [H_eq H_tc]]]].
  exists qn. exists args. exists tn. split; try auto.
  eapply typecheck_equiv.
  - apply H_tc.
  - unfold SkeletonEquiv. reflexivity.
Qed.

Theorem program_has_all_cfun_bods_l_helper : forall (p : program) (cfun_perm : perm),
    has_all_cfun_bods (skeleton_cfun_sigs_l (permuteSkeleton cfun_perm (program_skeleton p))) ((proj1_sig cfun_perm) cfun_bod_named (program_cfun_bods_l p)).
Proof.
  intros p cfun_perm.
  dependent destruction cfun_perm; simpl; destruct a as [H0 H1]; rename x into f.
  destruct p; simpl. clear - program_has_all_cfun_bods_l H0 H1.
  unfold has_all_cfun_bods in *. rewrite <- H1. rewrite <- H1. f_equal. assumption.
Qed.

Theorem program_cfun_bods_typecheck_l_helper : forall (p : program) (cfun_perm : perm),
    cfun_bods_l_typecheck (permuteSkeleton cfun_perm (program_skeleton p)) ((proj1_sig cfun_perm) cfun_bod_named (program_cfun_bods_l p)).
Proof.
  intros p cfun_perm.
  destruct p; simpl. clear - program_cfun_bods_typecheck_l.
  unfold cfun_bods_l_typecheck in *.
  apply Forall_forall. rewrite Forall_forall in program_cfun_bods_typecheck_l.
  intros x H. specialize (program_cfun_bods_typecheck_l x).
  (* dependent destruction cfun_perm; simpl; destruct a as [H0 H1]; rename x0 into f. simpl in *.*)
  eapply Permutation_in with (l' := program_cfun_bods_l) in H.
  - specialize (program_cfun_bods_typecheck_l H).
    destruct program_cfun_bods_typecheck_l as [qn [args [tn [H_eq H_tc]]]].
    exists qn. exists args. exists tn. split; try auto.
    + clear - H_eq.
      pose lookup_cfun_sig_name_correct_l.
      specialize (e program_skeleton (fst x) (qn, args, tn) H_eq). simpl in e. subst.
      pose In_cfun_sig_lookup_cfun_sig_l.
      specialize (i program_skeleton (fst x) args tn).
      rewrite <- i in H_eq.
      pose In_cfun_sig_lookup_cfun_sig_l.
      specialize (i0 (permuteSkeleton cfun_perm program_skeleton) (fst x) args tn).
      apply i0. clear - H_eq. destruct program_skeleton. simpl in *.
      dependent destruction cfun_perm; simpl in *.
      destruct a.
      eapply Permutation_in.
      * apply H.
      * assumption.
    + eapply typecheck_equiv.
      * apply H_tc.
      * unfold SkeletonEquiv. reflexivity.
  - apply Permutation_sym.
    dependent destruction cfun_perm; simpl; destruct a as [H0 H1]; rename x0 into f. simpl in *.
    apply H0.
Qed.

Theorem program_gfun_bods_typecheck_g_helper : forall (p : program) (cfun_perm : perm),
    gfun_bods_g_typecheck (permuteSkeleton cfun_perm (program_skeleton p)) (program_gfun_bods_g p).
Proof.
  intros p cfun_perm.
  destruct p; simpl. clear - program_gfun_bods_typecheck_g.
  unfold gfun_bods_g_typecheck in *. apply Forall_forall.
  rewrite Forall_forall in program_gfun_bods_typecheck_g.
  intros. specialize (program_gfun_bods_typecheck_g x H).
  destruct program_gfun_bods_typecheck_g as [qn [args [H_eq H_tc]]].
  exists qn. exists args. split; try auto.
  eapply typecheck_equiv.
  - apply H_tc.
  - unfold SkeletonEquiv. auto.
Qed.

Theorem program_gfun_bods_typecheck_l_helper : forall (p : program) (cfun_perm : perm),
    gfun_bods_l_typecheck (permuteSkeleton cfun_perm (program_skeleton p)) (program_gfun_bods_l p).
Proof.
  intros p cfun_perm.
  destruct p; simpl. clear - program_gfun_bods_typecheck_l.
  unfold gfun_bods_l_typecheck in *. apply Forall_forall.
  rewrite Forall_forall in program_gfun_bods_typecheck_l.
  intros. specialize (program_gfun_bods_typecheck_l x H).
  destruct program_gfun_bods_typecheck_l as [qn [args [H_eq H_tc]]].
  exists qn. exists args. split; try auto.
  eapply typecheck_equiv.
  - apply H_tc.
  - unfold SkeletonEquiv. auto.
Qed.

Lemma Permutation_app_4 : forall (A : Type) (l1 l2 l3 l3' l4 : list A),
    unique (l1 ++ l2 ++ l3 ++ l4) ->
    Permutation l3 l3' ->
    unique (l1 ++ l2 ++ l3' ++ l4).
Proof.
  intros.
  repeat rewrite <- uniqueness_app_rewrite.
  repeat rewrite <- uniqueness_app_rewrite in H.
  destruct H as [H1 [[H2 [[H3 [H4 H5]] H6]] H7]].
  repeat split; try auto.
  - eapply Permutation_unique.
    +apply H3.
    + assumption.
  - eapply Permutation_Forall.
    + apply H5.
    + assumption.
  - clear - H6 H0. apply Forall_forall. rewrite Forall_forall in H6.
    intros. specialize (H6 x H). intro H_abs. apply H6.
    apply in_or_app. apply in_app_or in H_abs. destruct H_abs; try auto.
    left. eapply Permutation_in.
    + apply Permutation_sym. apply H0.
    + eauto.
  - clear - H7 H0. apply Forall_forall. rewrite Forall_forall in H7.
    intros. specialize (H7 x H). intro H_abs. apply H7.
    apply in_or_app. apply in_app_or in H_abs. destruct H_abs; try auto. right.
    apply in_or_app. apply in_app_or in H1. destruct H1; try auto. left.
    eapply Permutation_in.
    + apply Permutation_sym. apply H0.
    + eauto.
Qed.

Lemma Permutation_concat : forall (A : Type) (l l': list (list A)),
    Permutation l l' ->
    Permutation (concat l) (concat l').
Proof.
  intros A l l' H.
  induction H; simpl.
  - constructor.
  - apply Permutation_app.
    + apply Permutation_refl.
    + assumption.
  - repeat rewrite app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm.
  - eapply Permutation_trans; eauto.
Qed.

Theorem program_match_names_unique_helper : forall (p : program) (cfun_perm : perm),
    match_names_unique (program_fun_bods p) (program_cfun_bods_g p ++ (proj1_sig cfun_perm) cfun_bod_named (program_cfun_bods_l p)) (program_gfun_bods_g p ++ program_gfun_bods_l p).
Proof.
  intros p cfun_perm.
  destruct p; simpl. clear - program_match_names_unique. unfold match_names_unique in *.
  generalize dependent (map snd (concat (map snd (program_gfun_bods_g ++ program_gfun_bods_l)))).
  generalize (map snd program_fun_bods).
  repeat rewrite map_app. intros. rename program_cfun_bods_g into s. rename program_cfun_bods_l into s'.
  repeat rewrite map_app. repeat rewrite map_app in program_match_names_unique.
  generalize dependent (map collect_match_names l). intros. generalize dependent (map collect_match_names l0).
  intros. rewrite concat_app. rewrite concat_app in program_match_names_unique. generalize dependent (concat l1).
  intros. rewrite concat_app. rewrite concat_app in program_match_names_unique. generalize dependent (concat l2).
  intros. repeat rewrite concat_map. repeat rewrite map_app.
  repeat rewrite concat_map in program_match_names_unique.
  repeat rewrite map_app in program_match_names_unique.
  repeat rewrite concat_app. repeat rewrite concat_app in program_match_names_unique.
  generalize dependent (map collect_match_names). intros.
  unfold cfun_bod in *.
  match goal with
    [ |- unique (_ ++ (?l ++ _) ++ _) ] => generalize dependent l
  end.
  intros. reassoc_list_to_right_all.
  dependent destruction cfun_perm; simpl. rename x into f. destruct a as [H1 H2].
  eapply Permutation_app_4.
  - apply program_match_names_unique.
  - repeat apply Permutation_concat. repeat apply Permutation_map.
    apply H1.
Qed.

Theorem program_comatch_names_unique_helper : forall (p : program) (cfun_perm : perm),
    comatch_names_unique (program_fun_bods p) (program_cfun_bods_g p ++ (proj1_sig cfun_perm) cfun_bod_named (program_cfun_bods_l p)) (program_gfun_bods_g p ++ program_gfun_bods_l p).
Proof.
  intros p cfun_perm.
  destruct p; simpl. clear - program_comatch_names_unique. unfold comatch_names_unique in *.
  generalize dependent (map snd (concat (map snd (program_gfun_bods_g ++ program_gfun_bods_l)))).
  generalize (map snd program_fun_bods).
  repeat rewrite map_app. intros. rename program_cfun_bods_g into s. rename program_cfun_bods_l into s'.
  repeat rewrite map_app. repeat rewrite map_app in program_comatch_names_unique.
  generalize dependent (map collect_comatch_names l). intros. generalize dependent (map collect_comatch_names l0).
  intros. rewrite concat_app. rewrite concat_app in program_comatch_names_unique. generalize dependent (concat l1).
  intros. rewrite concat_app. rewrite concat_app in program_comatch_names_unique. generalize dependent (concat l2).
  intros. repeat rewrite concat_map. repeat rewrite map_app.
  repeat rewrite concat_map in program_comatch_names_unique.
  repeat rewrite map_app in program_comatch_names_unique.
  repeat rewrite concat_app. repeat rewrite concat_app in program_comatch_names_unique.
  generalize dependent (map collect_comatch_names). intros.
  unfold cfun_bod in *.
  match goal with
    [ |- unique (_ ++ (?l ++ _) ++ _) ] => generalize dependent l
  end.
  intros. reassoc_list_to_right_all.
  dependent destruction cfun_perm; simpl. rename x into f. destruct a as [H1 H2].
  eapply Permutation_app_4.
  - apply program_comatch_names_unique.
  - repeat apply Permutation_concat. repeat apply Permutation_map.
    apply H1.
Qed.

Definition permuteProgram (p : program) (f : perm) : program :=
  {|
    program_skeleton := permuteSkeleton f (program_skeleton p);
    program_fun_bods := program_fun_bods p;
    program_cfun_bods_g := program_cfun_bods_g p;
    program_gfun_bods_g := program_gfun_bods_g p;
    program_cfun_bods_l := (proj1_sig f) cfun_bod_named (program_cfun_bods_l p);
    program_gfun_bods_l := program_gfun_bods_l p;
    program_has_all_fun_bods := program_has_all_fun_bods p;
    program_has_all_cfun_bods_g := program_has_all_cfun_bods_g p;
    program_has_all_cfun_bods_l := program_has_all_cfun_bods_l_helper p f;
    program_has_all_gfun_bods_g := program_has_all_gfun_bods_g p;
    program_has_all_gfun_bods_l := program_has_all_gfun_bods_l p;
    program_match_names_unique := program_match_names_unique_helper p f;
    program_comatch_names_unique := program_comatch_names_unique_helper p f;
    program_fun_bods_typecheck    := program_fun_bods_typecheck_helper p f;
    program_cfun_bods_typecheck_g := program_cfun_bods_g_typecheck_helper p f;
    program_cfun_bods_typecheck_l := program_cfun_bods_typecheck_l_helper p f;
    program_gfun_bods_typecheck_g := program_gfun_bods_typecheck_g_helper p f;
    program_gfun_bods_typecheck_l := program_gfun_bods_typecheck_l_helper p f;
  |}.

Definition ProgEquiv (p1 p2:  program) (cfun_perm : perm): Prop :=
  p2 = permuteProgram p1 cfun_perm.

