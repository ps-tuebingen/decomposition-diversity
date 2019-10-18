(* Standard library imports *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.
Import ListNotations.
(* Project related imports *)
Require Import GenericLemmas.
Require Import OptionMonad.
Require Import Names.
Require Import AST.
Require Import UtilsProgram.
Require Import UtilsSkeleton.
Require Import Skeleton.
Require Import Typechecker.
Require Import Unique.

(**************************************************************************************************)
(** * Constructorization Part I:                                                                 *)
(**                                                                                               *)
(** In the first part of the algorithm we compute a new program skeleton.                         *)
(**************************************************************************************************)

Definition DestrFunSignature : Type := list TypeName * TypeName.

Definition Constructor : Type := ScopedName * list TypeName.

Definition computeNewDatatype (p : program) (n : TypeName) : list Constructor :=
  (map (fun x => (global (fst x), snd x))
       (filter (fun x => eq_TypeName (fst (fst x)) n) (skeleton_gfun_sigs_g (program_skeleton p)))) ++
  (map (fun x => (local (fst x), snd x))
       (filter (fun x => eq_TypeName (fst (fst x)) n) (skeleton_gfun_sigs_l (program_skeleton p)))).

(**************************************************************************************************)
(** ** Proof of dts_ctors_in_dts (dt well-formedness #1)                                          *)
(**************************************************************************************************)

Lemma new_dts_ctors_in_dts_g : forall (p : program) (n : TypeName),
    dts_ctors_in_dts (n :: skeleton_dts (program_skeleton p))
      (map (fun x => (global (fst x), snd x))
       (filter (fun x => eq_TypeName (fst (fst x)) n) (skeleton_gfun_sigs_g (program_skeleton p)))).
Proof.
intros p n. unfold dts_ctors_in_dts.
assert (H : Forall (fun ctor => fst (unscope (fst ctor)) = n)
  (map (fun x => (global (fst x), snd x))
       (filter (fun x => eq_TypeName (fst (fst x)) n) (skeleton_gfun_sigs_g (program_skeleton p))))).
- induction (skeleton_gfun_sigs_g (program_skeleton p)).
  + simpl. apply Forall_nil.
  + simpl. destruct a as [[a0 a1] a2]; simpl in *. destruct (eq_TypeName a0 n) eqn:E.
    * simpl. apply Forall_cons. simpl. name_eq_tac. apply IHg.
    * apply IHg.
- induction (map (fun x => (global (fst x), snd x))
       (filter (fun x => eq_TypeName (fst (fst x)) n) (skeleton_gfun_sigs_g (program_skeleton p))));
    inversion H; subst.
  + apply Forall_nil.
  + apply Forall_cons.
    * simpl. left. reflexivity.
    * apply IHl. assumption.
Qed.

Lemma new_dts_ctors_in_dts_l : forall (p : program) (n : TypeName),
    dts_ctors_in_dts (n :: skeleton_dts (program_skeleton p))
      (map (fun x => (local (fst x), snd x))
       (filter (fun x => eq_TypeName (fst (fst x)) n) (skeleton_gfun_sigs_l (program_skeleton p)))).
intros p n. unfold dts_ctors_in_dts.
assert (H : Forall (fun ctor => fst (unscope (fst ctor)) = n)
  (map (fun x => (local (fst x), snd x))
       (filter (fun x => eq_TypeName (fst (fst x)) n) (skeleton_gfun_sigs_l (program_skeleton p))))).
- induction (skeleton_gfun_sigs_l (program_skeleton p)).
  + simpl. apply Forall_nil.
  + simpl. destruct a as [[a0 a1] a2]; simpl in *. destruct (eq_TypeName a0 n) eqn:E.
    * simpl. apply Forall_cons. simpl. name_eq_tac. apply IHg.
    * apply IHg.
- induction (map (fun x => (local (fst x), snd x))
       (filter (fun x => eq_TypeName (fst (fst x)) n) (skeleton_gfun_sigs_l (program_skeleton p))));
    inversion H; subst.
  + apply Forall_nil.
  + apply Forall_cons.
    * simpl. left. reflexivity.
    * apply IHl. assumption.
Qed.

Lemma new_dts_ctors_in_dts : forall (p : program) (n : TypeName),
    dts_ctors_in_dts (n :: skeleton_dts (program_skeleton p)) ((computeNewDatatype p n) ++ (skeleton_ctors (program_skeleton p))).
Proof.
intros p n. unfold dts_ctors_in_dts. unfold computeNewDatatype.
repeat apply Forall_app.
- apply new_dts_ctors_in_dts_g.
- apply new_dts_ctors_in_dts_l.
- destruct p. simpl. clear - program_skeleton. destruct program_skeleton. simpl.
  clear - skeleton_dts_ctors_in_dts. unfold dts_ctors_in_dts in skeleton_dts_ctors_in_dts.
  induction skeleton_ctors.
  + apply Forall_nil.
  + apply Forall_cons.
    * right. inversion skeleton_dts_ctors_in_dts; subst. assumption.
    * apply IHskeleton_ctors. inversion skeleton_dts_ctors_in_dts; subst. assumption.
Qed.

(**************************************************************************************************)
(** ** Proof of dts_ctor_names_unique (dt well-formedness #1)                                     *)
(**************************************************************************************************)

Lemma disjoint_app_unique : forall {A} (l1 l2 : list A),
  (forall a, ~(In a l1 /\ In a l2)) ->
  unique l1 ->
  unique l2 ->
  unique (l1 ++ l2).
Proof with try apply in_eq; try apply in_cons; auto.
intros. induction l1... rewrite <- app_comm_cons. apply Unique_cons.
- unfold not. intros. unfold not in H. inversion H0; subst. apply in_app_or in H2. destruct H2...
  apply H with (a0:=a). split...
- inversion H0; subst. apply IHl1... intros. unfold not. intros. unfold not in H. destruct H2. apply H with (a0:=a0). split...
Qed.

Lemma new_dts_ctor_names_unique : forall (p : program)(n : TypeName),
    dts_ctor_names_unique ((computeNewDatatype p n) ++ skeleton_ctors (program_skeleton p)).
Proof with auto.
intros p n. unfold dts_ctor_names_unique.
unfold computeNewDatatype. repeat (rewrite map_app). repeat (rewrite map_map). simpl.
pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)) as ctorInDts.
pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)) as dtorInCdts.
pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as InCdt_g.
pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as InCdt_l.
apply disjoint_app_unique.
- intros. unfold not. intros. unfold dts_cdts_disjoint in Disj.
  unfold not in Disj. destruct H. apply in_app_or in H. destruct H.
  + unfold gfun_sigs_in_cdts in InCdt_g.
    rewrite Forall_forall in InCdt_g.
    rewrite in_map_iff in H. destruct H as [x [H xIn]].
    rewrite filter_In in xIn. destruct xIn.
    eapply Disj. rewrite and_comm. split.
    * apply InCdt_g. eauto.
    * unfold dts_ctors_in_dts in ctorInDts. rewrite Forall_forall in ctorInDts.
      apply (f_equal unscope) in H. simpl in H. unfold QName in *. rewrite H.
      rewrite in_map_iff in H0. destruct H0. destruct H0. destruct x0. simpl in *; subst.
      change a with (fst (a,l)). apply ctorInDts...
  + unfold gfun_sigs_in_cdts in InCdt_l.
    rewrite Forall_forall in InCdt_l.
    rewrite in_map_iff in H. destruct H as [x [H xIn]].
    rewrite filter_In in xIn. destruct xIn.
    eapply Disj. rewrite and_comm. split.
    * apply InCdt_l. eauto.
    * unfold dts_ctors_in_dts in ctorInDts. rewrite Forall_forall in ctorInDts.
      apply (f_equal unscope) in H. simpl in H. unfold QName in *. rewrite H.
      rewrite in_map_iff in H0. destruct H0. destruct H0. destruct x0. simpl in *; subst.
      change a with (fst (a,l)). apply ctorInDts...
- apply disjoint_app_unique.
  + intros. unfold not. intros. destruct H.
    rewrite in_map_iff in H. rewrite in_map_iff in H0.
    destruct H as [x [H xIn]]. destruct H0 as [x0 [H0 x0In]].
    rewrite <- H0 in H. discriminate.
  + pose proof (skeleton_gfun_sigs_names_unique_g (program_skeleton p)) as H.
    unfold gfun_sigs_names_unique in H. rewrite <- map_map.
    assert (forall l, unique l -> unique (map global l)) as H0.
    { intros. induction l; try apply Unique_nil. simpl. inversion H0; subst.
      apply Unique_cons... unfold not. intros. unfold not in H3. apply H3.
      rewrite in_map_iff in H1. do 2 (destruct H1). inversion H1; subst... }
    apply H0.
    rewrite filter_map with
      (g:=fun x : TypeName * Name => eq_TypeName (fst x) n) (f:=fst).
    apply filter_unique...
  + pose proof (skeleton_gfun_sigs_names_unique_l (program_skeleton p)) as H.
    unfold gfun_sigs_names_unique in H. rewrite <- map_map.
    assert (forall l, unique l -> unique (map local l)) as H0.
    { intros. induction l; try apply Unique_nil. simpl. inversion H0; subst.
      apply Unique_cons... unfold not. intros. unfold not in H3. apply H3.
      rewrite in_map_iff in H1. do 2 (destruct H1). inversion H1; subst... }
    apply H0.
    rewrite filter_map with
      (g:=fun x : TypeName * Name => eq_TypeName (fst x) n) (f:=fst).
    apply filter_unique...
- apply (skeleton_dts_ctor_names_unique (program_skeleton p)).
Qed.


(**************************************************************************************************)
(** ** Proof of cdts_dtors_in_cdts (cdt well-formedness #1)                                       *)
(**************************************************************************************************)

Definition new_cdts (p : program) (n : TypeName) : list TypeName :=
      (filter (fun n' : TypeName => negb (eq_TypeName n n')) (skeleton_cdts (program_skeleton p))).

Definition new_dtors (p : program) (n : TypeName) :=
  filter (fun x => match x with (n',_,_) => negb (eq_TypeName n (fst (unscope n'))) end) (skeleton_dtors (program_skeleton p)).

Lemma new_cdts_dtors_in_cdts : forall (p : program) (n : TypeName),
  cdts_dtors_in_cdts (new_cdts p n) (new_dtors p n).
Proof.
intros p n. unfold new_dtors. unfold new_cdts. destruct p. simpl. clear - program_skeleton.
destruct program_skeleton. simpl. clear - skeleton_cdts_dtors_in_cdts.
unfold cdts_dtors_in_cdts in *.
induction skeleton_dtors.
- simpl. apply Forall_nil.
- simpl. destruct a as [[a0 a1] a2]. simpl in *.
  destruct (eq_TypeName n (fst (unscope a0))) eqn:E.
  + simpl. apply IHskeleton_dtors. inversion skeleton_cdts_dtors_in_cdts; subst. apply H2.
  + simpl. apply Forall_cons.
    * simpl. inversion skeleton_cdts_dtors_in_cdts; subst. simpl in *. remember (fst (unscope a0)) as X.
      clear - H1 E. induction skeleton_cdts; try inversion H1.
      simpl. simpl in H1. destruct H1.
      -- subst. rewrite E. simpl. left. reflexivity.
      -- destruct (eq_TypeName n a) eqn:E'.
         ++ name_eq_tac. simpl. apply IHskeleton_cdts. assumption.
         ++ simpl. right. apply IHskeleton_cdts. assumption.
      -- simpl. destruct (eq_TypeName n a) eqn:E2.
         ++ simpl. apply IHskeleton_cdts. assumption.
         ++ simpl. right. apply IHskeleton_cdts. assumption.
    * apply IHskeleton_dtors. inversion skeleton_cdts_dtors_in_cdts; subst. assumption.
Qed.

(**************************************************************************************************)
(** ** Proof of cdts_dtor_names_unique (cdt well-formedness #2)                                   *)
(**************************************************************************************************)

Fact filter_ext : forall {A} (l : list A) f g,
  (forall a, f a = g a) ->
  filter f l = filter g l.
Proof with auto. intros. induction l... simpl. rewrite H. rewrite IHl... Qed.

Lemma new_cdts_dtor_names_unique : forall (p : program)(n : TypeName),
  cdts_dtor_names_unique (new_dtors p n).
Proof.
intros p n. unfold new_dtors. destruct p. simpl. clear - program_skeleton.
destruct program_skeleton. simpl. clear - skeleton_cdts_dtor_names_unique.
unfold cdts_dtor_names_unique in *.
rewrite filter_ext with (g:=fun x => negb (eq_TypeName n (fst (unscope (fst (fst x)))))).
2: { intros. destruct a. destruct p. auto. }
rewrite filter_map with
  (g:=fun x : ScopedName => negb (eq_TypeName n (fst (unscope x))))
  (f:=fun x => fst (fst x)). apply filter_unique. auto.
Qed.

(**************************************************************************************************)
(** ** Proof of dts_cdts_disjoint                                                                     *)
(**************************************************************************************************)

Lemma new_d_cd_disj : forall (p : program) (n : TypeName),
    dts_cdts_disjoint (n :: skeleton_dts (program_skeleton p)) (new_cdts p n).
Proof.
intros p n. unfold dts_cdts_disjoint. intros t H. unfold new_cdts in H.
destruct p; simpl in *. clear - H program_skeleton.
destruct program_skeleton; simpl in *. clear - H skeleton_dts_cdts_disjoint.
unfold dts_cdts_disjoint in skeleton_dts_cdts_disjoint.
destruct H. destruct H.
- subst. clear - H0. induction skeleton_cdts.
  + simpl in H0. assumption.
  + simpl in H0. destruct (eq_TypeName t a) eqn:E.
    * simpl in *. apply IHskeleton_cdts. assumption.
    * simpl in *. destruct H0.
      -- subst. name_refl_tac. inversion E.
      -- apply IHskeleton_cdts. assumption.
- specialize (skeleton_dts_cdts_disjoint t). apply skeleton_dts_cdts_disjoint. split.
   + assumption.
   + clear - H0. induction skeleton_cdts.
    * inversion H0.
    * simpl in *. destruct (eq_TypeName n a) eqn:E.
      -- simpl in *. name_eq_tac. right. apply IHskeleton_cdts. assumption.
      -- simpl in *. destruct H0.
         ++ left. assumption.
         ++ right. apply IHskeleton_cdts. assumption.
Qed.

(**************************************************************************************************)
(** ** Proof of cfun_sigs_in_dts (cfuns well-formedness #1)                                       *)
(**************************************************************************************************)

Definition cfunsigs_mapfun (x : ScopedName * list TypeName * TypeName) :=
  match x with (x1,x2,x3) => (unscope x1, x2, x3) end.

Definition cfunsigs_filterfun_g (n : TypeName) (x : ScopedName * list TypeName * TypeName) :=
  match x with
  |(global n',_,_) => eq_TypeName n (fst n')
  | _ => false
  end.

Definition new_cfunsigs_g p n :=
  List.map cfunsigs_mapfun (filter (cfunsigs_filterfun_g n) (skeleton_dtors (program_skeleton p)))
           ++ (skeleton_cfun_sigs_g (program_skeleton p)).

Lemma new_cfun_sigs_in_dts_g : forall (p : program) (n : TypeName),
    cfun_sigs_in_dts
      (n :: skeleton_dts (program_skeleton p))
      (new_cfunsigs_g p n).
Proof.
  intros p n. pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)).
  unfold cfun_sigs_in_dts in *. unfold new_cfunsigs_g. apply Forall_app.
  - (* Show the newly generated cfunsigs are in (n :: dts) *)
    clear H. induction (skeleton_dtors (program_skeleton p)).
    + simpl. apply Forall_nil.
    + simpl. destruct a as [[a0 a1] a2]. simpl in *. destruct a0.
      * apply IHd.
      * destruct (eq_TypeName n (fst q)) eqn:E.
        ** simpl. apply Forall_cons.
           *** left. simpl. name_eq_tac.
           *** apply IHd.
        ** apply IHd.
  - (* Show the old cfunsigs are in dts *)
    induction (skeleton_cfun_sigs_g (program_skeleton p)).
    + apply Forall_nil.
    + apply Forall_cons.
      * apply in_cons. inversion H; assumption.
      * apply IHc. inversion H; subst. assumption.
Qed.

Definition cfunsigs_filterfun_l (n : TypeName) (x : ScopedName * list TypeName * TypeName) :=
  match x with
  |(local n',_,_) => eq_TypeName n (fst n')
  | _ => false
  end.

Definition new_cfunsigs_l p n :=
  List.map cfunsigs_mapfun (filter (cfunsigs_filterfun_l n) (skeleton_dtors (program_skeleton p)))
           ++ (skeleton_cfun_sigs_l (program_skeleton p)).

Lemma new_cfun_sigs_in_dts_l : forall (p : program) (n : TypeName),
    cfun_sigs_in_dts
      (n :: skeleton_dts (program_skeleton p))
      (new_cfunsigs_l p n).
Proof.
  intros p n. pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)).
  unfold cfun_sigs_in_dts in *. unfold new_cfunsigs_l. apply Forall_app.
  - (* Show the newly generated cfunsigs are in (n :: dts) *)
    clear H. induction (skeleton_dtors (program_skeleton p)).
    + simpl. apply Forall_nil.
    + simpl. destruct a as [[a0 a1] a2]. simpl in *. destruct a0.
      * destruct (eq_TypeName n (fst q)) eqn:E.
        ** simpl. apply Forall_cons.
           *** left. simpl. name_eq_tac.
           *** apply IHd.
        ** apply IHd.
      * apply IHd.
  - (* Show the old cfunsigs are in dts *)
    induction (skeleton_cfun_sigs_l (program_skeleton p)).
    + apply Forall_nil.
    + apply Forall_cons.
      * apply in_cons. inversion H; assumption.
      * apply IHc. inversion H; subst. assumption.
Qed.


(**************************************************************************************************)
(** ** Proof of cfun_sigs_names_unique (cfuns well-formedness #2)                                 *)
(**************************************************************************************************)

Lemma new_cfun_sigs_names_unique_g : forall (p : program) (n : TypeName),
    cfun_sigs_names_unique (new_cfunsigs_g p n).
Proof.
intros p n. unfold cfun_sigs_names_unique. unfold new_cfunsigs_g.
pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)).
unfold cfun_sigs_names_unique in H. unfold cfunsigs_mapfun.
pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)) as dtorInCdts.
pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as InDt_g.
rewrite map_app.
apply disjoint_app_unique.
- intros. unfold not. intros. destruct H0.
  unfold cdts_dtors_in_cdts in dtorInCdts. rewrite Forall_forall in dtorInCdts.
  rewrite map_map in H0. rewrite in_map_iff in H0. do 2 (destruct H0).
  rewrite filter_In in H2. destruct H2. pose proof (dtorInCdts _ H2).

  unfold cfun_sigs_in_dts in InDt_g. rewrite Forall_forall in InDt_g.
  rewrite in_map_iff in H1. do 2 (destruct H1). pose proof (InDt_g _ H5).
  destruct x. destruct p0. subst. simpl in *. unfold QName in *. rewrite H1 in H6.

  unfold dts_cdts_disjoint in Disj. unfold not in Disj. eapply Disj. split; eauto.
- pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)).
  unfold cdts_dtor_names_unique in H0.
  unfold cfunsigs_filterfun_g. clear - H0.
  generalize dependent (skeleton_dtors (program_skeleton p)). induction d; intros.
  + simpl. apply Unique_nil.
  + simpl. destruct a. destruct p0. destruct s.
    * apply IHd. inversion H0; subst. auto.
    * case (eq_TypeName n (fst q)).
      -- simpl. apply Unique_cons.
         ++ inversion H0; subst. unfold not in *. intros. apply H2. clear - H.
            rewrite map_map in H. rewrite in_map_iff in H. do 2 (destruct H).
            rewrite filter_In in H0. destruct H0. destruct x. destruct p. rewrite <- H.
            simpl in *. rewrite in_map_iff. exists (s,l,t). simpl. split; auto.
            destruct s; try discriminate. auto.
         ++ inversion H0; subst. auto.
      -- inversion H0; subst. auto.
- apply (skeleton_cfun_sigs_names_unique_g (program_skeleton p)).
Qed.

Lemma new_cfun_sigs_names_unique_l : forall (p : program) (n : TypeName),
    cfun_sigs_names_unique (new_cfunsigs_l p n).
Proof.
intros p n. unfold cfun_sigs_names_unique. unfold new_cfunsigs_l.
pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)).
unfold cfun_sigs_names_unique in H. unfold cfunsigs_mapfun.
pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)) as dtorInCdts.
pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as InDt_l.
rewrite map_app.
apply disjoint_app_unique.
- intros. unfold not. intros. destruct H0.
  unfold cdts_dtors_in_cdts in dtorInCdts. rewrite Forall_forall in dtorInCdts.
  rewrite map_map in H0. rewrite in_map_iff in H0. do 2 (destruct H0).
  rewrite filter_In in H2. destruct H2. pose proof (dtorInCdts _ H2).

  unfold cfun_sigs_in_dts in InDt_l. rewrite Forall_forall in InDt_l.
  rewrite in_map_iff in H1. do 2 (destruct H1). pose proof (InDt_l _ H5).
  destruct x. destruct p0. subst. simpl in *. unfold QName in *. rewrite H1 in H6.

  unfold dts_cdts_disjoint in Disj. unfold not in Disj. eapply Disj. split; eauto.
- pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)).
  unfold cdts_dtor_names_unique in H0.
  unfold cfunsigs_filterfun_l. clear - H0.
  generalize dependent (skeleton_dtors (program_skeleton p)). induction d; intros.
  + simpl. apply Unique_nil.
  + simpl. destruct a. destruct p0. destruct s.
    * case (eq_TypeName n (fst q)).
      -- simpl. apply Unique_cons.
         ++ inversion H0; subst. unfold not in *. intros. apply H2. clear - H.
            rewrite map_map in H. rewrite in_map_iff in H. do 2 (destruct H).
            rewrite filter_In in H0. destruct H0. destruct x. destruct p. rewrite <- H.
            simpl in *. rewrite in_map_iff. exists (s,l,t). simpl. split; auto.
            destruct s; try discriminate. auto.
         ++ inversion H0; subst. auto.
      -- inversion H0; subst. auto.
    * apply IHd. inversion H0; subst. auto.
- apply (skeleton_cfun_sigs_names_unique_l (program_skeleton p)).
Qed.

(**************************************************************************************************)
(** ** Proof of gfun_sigs_in_dts (gfuns well-formedness #1)                                       *)
(**************************************************************************************************)

Definition new_gfunsigs_g p n :=
  filter (fun x => match x with (n',_) => negb (eq_TypeName n (fst n')) end) (skeleton_gfun_sigs_g (program_skeleton p)).

Lemma new_gfun_sigs_in_cdts_g : forall (p : program) (n : TypeName),
  gfun_sigs_in_cdts (new_cdts p n) (new_gfunsigs_g p n).
Proof.
  intros p n. unfold gfun_sigs_in_cdts. unfold new_cdts.
  unfold new_gfunsigs_g. destruct p; simpl. clear - program_skeleton.
  destruct program_skeleton; simpl. clear - skeleton_gfun_sigs_in_cdts_g.
  unfold gfun_sigs_in_cdts in skeleton_gfun_sigs_in_cdts_g.
  induction skeleton_gfun_sigs_g.
  -simpl. apply Forall_nil.
  -simpl. destruct a as [a0 a1]. simpl. destruct (eq_TypeName n (fst a0)) eqn:E.
   +simpl. apply IHskeleton_gfun_sigs_g. inversion skeleton_gfun_sigs_in_cdts_g; subst. assumption.
   +simpl. apply Forall_cons.
    *simpl. inversion skeleton_gfun_sigs_in_cdts_g; subst. clear - E H1. simpl in H1. induction skeleton_cdts.
     **inversion H1.
     **simpl. destruct (eq_TypeName n a) eqn:E'.
       ***simpl. apply IHskeleton_cdts. simpl in H1. destruct H1.
          ****subst. rewrite E in E'. inversion E'.
          ****assumption.
       ***simpl. simpl in H1. destruct H1.
          ****subst. left. reflexivity.
          ****right. apply IHskeleton_cdts. assumption.
    *apply IHskeleton_gfun_sigs_g. inversion skeleton_gfun_sigs_in_cdts_g; subst. assumption.
Qed.

Definition new_gfunsigs_l p n :=
  filter (fun x => match x with (n',_) => negb (eq_TypeName n (fst n')) end) (skeleton_gfun_sigs_l (program_skeleton p)).

Lemma new_gfun_sigs_in_cdts_l : forall (p : program) (n : TypeName),
  gfun_sigs_in_cdts (new_cdts p n) (new_gfunsigs_l p n).
Proof.
  intros p n. unfold gfun_sigs_in_cdts. unfold new_cdts.
  unfold new_gfunsigs_l. destruct p; simpl. clear - program_skeleton.
  destruct program_skeleton; simpl. clear - skeleton_gfun_sigs_in_cdts_l.
  unfold gfun_sigs_in_cdts in skeleton_gfun_sigs_in_cdts_l.
  induction skeleton_gfun_sigs_l.
  -simpl. apply Forall_nil.
  -simpl. destruct a as [a0 a1]. simpl. destruct (eq_TypeName n (fst a0)) eqn:E.
   +simpl. apply IHskeleton_gfun_sigs_l. inversion skeleton_gfun_sigs_in_cdts_l; subst. assumption.
   +simpl. apply Forall_cons.
    *simpl. inversion skeleton_gfun_sigs_in_cdts_l; subst. clear - E H1. simpl in H1. induction skeleton_cdts.
     **inversion H1.
     **simpl. destruct (eq_TypeName n a) eqn:E'.
       ***simpl. apply IHskeleton_cdts. simpl in H1. destruct H1.
          ****subst. rewrite E in E'. inversion E'.
          ****assumption.
       ***simpl. simpl in H1. destruct H1.
          ****subst. left. reflexivity.
          ****right. apply IHskeleton_cdts. assumption.
    *apply IHskeleton_gfun_sigs_l. inversion skeleton_gfun_sigs_in_cdts_l; subst. assumption.
Qed.

(**************************************************************************************************)
(** ** Proof of gfun_sigs_names_unique (gfuns well-formedness #2)                                 *)
(**************************************************************************************************)

Lemma new_gfun_sigs_names_unique_g : forall (p : program) (n : TypeName),
  gfun_sigs_names_unique (new_gfunsigs_g p n).
Proof.
intros p n. unfold gfun_sigs_names_unique. unfold new_gfunsigs_g.
pose proof (skeleton_gfun_sigs_names_unique_g (program_skeleton p)).
unfold gfun_sigs_names_unique in H.
assert (forall l, filter (fun x : TypeName * Name * list TypeName => let (n', _) := x in negb (eq_TypeName n (fst n'))) l
 = filter (fun x : TypeName * Name * list TypeName => negb (eq_TypeName n (fst (fst x)))) l).
{ clear. intros. induction l; auto. simpl. destruct a. simpl. rewrite IHl. auto. }
rewrite H0.
rewrite filter_map with
  (g:=fun x : TypeName * Name => negb (eq_TypeName n (fst x)))
  (f:=fst). apply filter_unique. auto.
Qed.

Lemma new_gfun_sigs_names_unique_l : forall (p : program) (n : TypeName),
  gfun_sigs_names_unique (new_gfunsigs_l p n).
Proof.
intros p n. unfold gfun_sigs_names_unique. unfold new_gfunsigs_l.
pose proof (skeleton_gfun_sigs_names_unique_l (program_skeleton p)).
unfold gfun_sigs_names_unique in H.
assert (forall l, filter (fun x : TypeName * Name * list TypeName => let (n', _) := x in negb (eq_TypeName n (fst n'))) l
 = filter (fun x : TypeName * Name * list TypeName => negb (eq_TypeName n (fst (fst x)))) l).
{ clear. intros. induction l; auto. simpl. destruct a. simpl. rewrite IHl. auto. }
rewrite H0.
rewrite filter_map with
  (g:=fun x : TypeName * Name => negb (eq_TypeName n (fst x)))
  (f:=fst). apply filter_unique. auto.
Qed.

(**************************************************************************************************)
(** * Constructorize to Skeleton.                                                                *)
(**************************************************************************************************)

Definition constructorize_to_skeleton (p : program) (n : TypeName) : skeleton :=
  let newDatatype := (computeNewDatatype p n) in
  {|
    skeleton_dts := n :: skeleton_dts (program_skeleton p);
    skeleton_ctors := newDatatype ++ (skeleton_ctors (program_skeleton p));
    skeleton_dts_ctors_in_dts := new_dts_ctors_in_dts p n;
    skeleton_dts_ctor_names_unique := new_dts_ctor_names_unique p n;
    skeleton_cdts := new_cdts p n;
    skeleton_dtors := new_dtors p n;
    skeleton_cdts_dtors_in_cdts := new_cdts_dtors_in_cdts p n;
    skeleton_cdts_dtor_names_unique := new_cdts_dtor_names_unique p n;
    skeleton_dts_cdts_disjoint := new_d_cd_disj p n;
    skeleton_fun_sigs := skeleton_fun_sigs (program_skeleton p);
    skeleton_fun_sigs_names_unique := skeleton_fun_sigs_names_unique (program_skeleton p);
    skeleton_cfun_sigs_g := new_cfunsigs_g p n;
    skeleton_cfun_sigs_in_dts_g := new_cfun_sigs_in_dts_g p n;
    skeleton_cfun_sigs_names_unique_g := new_cfun_sigs_names_unique_g p n;
    skeleton_cfun_sigs_l := new_cfunsigs_l p n;
    skeleton_cfun_sigs_in_dts_l := new_cfun_sigs_in_dts_l p n;
    skeleton_cfun_sigs_names_unique_l := new_cfun_sigs_names_unique_l p n;
    skeleton_gfun_sigs_g := new_gfunsigs_g p n;
    skeleton_gfun_sigs_in_cdts_g := new_gfun_sigs_in_cdts_g p n;
    skeleton_gfun_sigs_names_unique_g := new_gfun_sigs_names_unique_g p n;
    skeleton_gfun_sigs_l := new_gfunsigs_l p n;
    skeleton_gfun_sigs_in_cdts_l := new_gfun_sigs_in_cdts_l p n;
    skeleton_gfun_sigs_names_unique_l := new_gfun_sigs_names_unique_l p n
  |}.
