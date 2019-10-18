(**************************************************************************************************)
(* Total Constructor/Destructorization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: UtilsSkeleton.v                                                                          *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

Require Import GenericLemmas.
Require Import Unique.
Require Import GenericTactics.
Require Import Names.
Require Import AST.
Require Import Skeleton.


Inductive is_first {A : Type} : A -> list A -> (A -> A -> bool) -> Prop :=
| is_first_head : forall (x : A) (xs : list A) (eq : A -> A -> bool),
    is_first x (x :: xs) eq
| is_first_tail : forall (x y : A) (xs : list A) (eq : A -> A -> bool),
    eq x y = false ->
    is_first x xs eq ->
    is_first x (y :: xs) eq.


(**************************************************************************************************)
(** * Lookup Functions for Skeleton                                                               *)
(**                                                                                               *)
(**************************************************************************************************)

(**************************************************************************************************)
(** ** Datatypes and Constructors                                                                 *)
(**                                                                                               *)
(**************************************************************************************************)

(**************************************************************************************************)
(** Given a typename, return the list of constructors from the constructortable.                  *)
(**************************************************************************************************)
Definition lookup_ctors (s : skeleton) (tn : TypeName) : option ctors :=
  let filterResult := filter (fun x => match x with (n,_) => eq_TypeName (fst (unscope n)) tn end) (skeleton_ctors s) in
  let tnresult := filter (eq_TypeName tn) (skeleton_dts s) in
  match tnresult with [] => None | _ => Some filterResult end.

Lemma lookup_ctors_in_ctors : forall (s : skeleton) (tn : TypeName) (ctors : ctors),
    lookup_ctors s tn = Some ctors ->
    Forall (fun ctor => In ctor (skeleton_ctors s)) ctors.
Proof.
  intros s tn ctors H.
  unfold lookup_ctors in H.
  induction (skeleton_dts s); try solve [inversion H].
  simpl in H. destruct (eq_TypeName tn a) eqn: E_tn.
  - inversion H. clear. induction (skeleton_ctors s) as [|ctor ctors_rest].
   + apply Forall_nil.
   + simpl. destruct ctor as [sn ts].
     destruct (eq_TypeName (fst (unscope sn)) tn).
     * apply Forall_cons; try auto.
       apply Forall_Or_right. apply IHctors_rest.
     * apply Forall_Or_right. apply IHctors_rest.
  - apply IHd; assumption.
Qed.

Ltac tuple_destruct_tac :=
  match goal with
  | [  |- context [ let (_,_) := ?p in _ ] ] => destruct p
  end.

Ltac in_filter_tac :=
  match goal with
  | [ H : In ?x ?ls |- context [?f _ ?ls] ] =>
    induction ls; inversion H; simpl;
    match goal with
    | [ H1 : ?a = x |- _ ] => rewrite H1; simpl; name_refl_tac
    | [  |- _ ] => name_destruct_tac || (tuple_destruct_tac; name_destruct_tac)
    end
  end.

Lemma lookup_ctors_In_propagates: forall (sk : skeleton) (sn : ScopedName) (cargs : list TypeName) (ctors : ctors),
    lookup_ctors sk (fst (unscope sn)) = Some ctors ->
    In (sn, cargs) (skeleton_ctors sk) ->
    In (sn, cargs) ctors.
Proof.
  intros sk sn cargs ctors H H0; unfold lookup_ctors in H.
  match_destruct_tac; inversion H;
  clear - H0; in_filter_tac.
  - left; auto.
  - right. IH_tac.
  - IH_tac.
Qed.

Lemma in_ctors_lookup_ctors : forall (sk : skeleton) (ctor : ctor),
    In ctor (skeleton_ctors sk) ->
    exists ctors, lookup_ctors sk (fst (unscope (fst ctor))) = Some ctors.
Proof.
  intros sk ctor H.
  eexists. unfold lookup_ctors.
  assert (H_in_dts : In (fst (unscope (fst ctor))) (skeleton_dts sk)).
  {   pose proof (skeleton_dts_ctors_in_dts sk) as H_ctors_in_dts.
      unfold dts_ctors_in_dts in H_ctors_in_dts.
      induction (skeleton_ctors sk); try solve [inversion H].
      inversion H.
      - inversion H_ctors_in_dts; subst; assumption.
      - inversion H_ctors_in_dts. apply IHc; try assumption. }
  assert (H_filter : exists d ds, filter (eq_TypeName (fst (unscope (fst ctor)))) (skeleton_dts sk) = d :: ds).
  { clear - H_in_dts. in_filter_tac; eauto. }
  inversion_clear H_filter as [d [ds E_filter]]. rewrite E_filter. eauto.
Qed.

Lemma in_ctors_lookup_ctors': forall (sk : skeleton) (ctor : ctor),
    In ctor (skeleton_ctors sk) ->
    exists ctors, lookup_ctors sk (fst (unscope (fst ctor))) = Some ctors /\

             In ctor ctors.
Proof.
  intros sk ctor H_in. pose proof H_in as H.
  apply in_ctors_lookup_ctors in H. inversion H as [ctors H1]; clear H.
  exists ctors. split; try assumption.
  unfold lookup_ctors in H1.
  match goal with
  | [ H: context [match ?x with | _ => _ end] |- _ ] => destruct x; try solve [inversion H]
  end.
  inversion H1 as [E]; clear H1.
  generalize dependent ctors; induction (skeleton_ctors sk) as [|c_head c_tail]; intros; try solve [inversion H_in]; simpl.
  simpl in E. destruct c_head as [c_n c_args].
  match goal with
  | [ H: context [if ?x then _ else _] |- _ ] => let E := fresh E "_" H in destruct x eqn:E
  end.
  - match goal with
    | [ H: In ctor _ |- _ ] => let H' := fresh H "_inv" in inversion H as [H' | H']
    end.
    + left. assumption.
    + right. destruct ctors; try solve [inversion E]. inversion E. specialize (IHc_tail H_in_inv ctors).
      IH_tac.
  - specialize IHc_tail with (ctors0 := ctors). IH_tac idtac.
    inversion H_in; try assumption.
    rewrite <- H in E_E. simpl in E_E. name_refl_tac. inversion E_E.
Qed.

Lemma lookup_ctors_in_dts : forall (s : skeleton) (tn : TypeName) (ctors : ctors),
    lookup_ctors s tn = Some ctors ->
    In tn (skeleton_dts s).
Proof.
  intros s tn ctors H.
  unfold lookup_ctors in H.
  induction (skeleton_dts s) as [| dt dts]; try solve [inversion H].
  simpl in H. destruct (eq_TypeName tn dt) eqn:E_tn.
  - simpl; left; symmetry. apply eq_TypeName_eq. assumption.
  - simpl; right. apply IHdts; assumption.
Qed.

Lemma lookup_ctors_not_in_cdts : forall (s : skeleton) (tn : TypeName) (ctors : ctors),
    lookup_ctors s tn = Some ctors ->
    ~ In tn (skeleton_cdts s).
Proof.
  intros s tn ctors H.
  apply lookup_ctors_in_dts in H.
  intros H1.
  pose proof (skeleton_dts_cdts_disjoint s) as H_unique.
  unfold dts_cdts_disjoint in H_unique.
  specialize (H_unique tn).  apply H_unique. auto.
Qed.

Opaque lookup_ctors.

(**************************************************************************************************)
(** Given a scoped name of a constructor, return the types of its arguments.                      *)
(**************************************************************************************************)

Definition lookup_ctor_sig (s : skeleton) (sn : ScopedName) : option ctor :=
  find (fun x => eq_ScopedName sn (fst x)) (skeleton_ctors s).

Lemma lookup_ctor_sig_in_ctors : forall (s : skeleton) (sn : ScopedName) (ctor : ctor),
    lookup_ctor_sig s sn = Some ctor ->
    In ctor (skeleton_ctors s).
Proof.
  intros s sn ctor H.
  unfold lookup_ctor_sig in H.
  apply find_in in H. assumption.
Qed.

Lemma in_ctors_lookup_ctor_sig : forall (sk : skeleton) (ctor : ctor),
    In ctor (skeleton_ctors sk) ->
    lookup_ctor_sig sk (fst ctor) = Some ctor.
Proof.
  intros sk ctor H.
  pose proof (skeleton_dts_ctor_names_unique sk) as H_unique.
  unfold lookup_ctor_sig. induction (skeleton_ctors sk); try solve [inversion H].
  destruct a as [sname args]. simpl. inversion H as [H1 | H1].
  - rewrite <- H1. simpl. rewrite eq_ScopedName_refl. reflexivity.
  - destruct (eq_ScopedName (fst ctor) sname) eqn:E_sn.
    + unfold dts_ctor_names_unique in H_unique. inversion H_unique; subst.
      exfalso. destruct ctor as [sn x]. simpl in *. rewrite eq_ScopedName_eq in E_sn; rewrite E_sn in *.
      apply H3. clear - H1. induction c; try solve [inversion H1].
      inversion H1.
      * left. rewrite H. reflexivity.
      * right; apply IHc; try assumption.
    + apply IHc; try assumption. inversion H_unique. assumption.
Qed.

Lemma lookup_ctor_sig_correct_name : forall (s : skeleton) (sn : ScopedName) (ctor : ctor),
    lookup_ctor_sig s sn = Some ctor ->
    sn = (fst ctor).
Proof.
  intros s sn ctor H. unfold lookup_ctor_sig in H. induction (skeleton_ctors s); try inversion H.
  destruct a as [sname args]; simpl in *. destruct (eq_ScopedName sn sname) eqn:E.
  - inversion H1. simpl. name_eq_tac.
  - apply IHc. assumption.
Qed.

Lemma lookup_ctor_sig_in_dts : forall (s : skeleton) (sn : ScopedName) (ctor : ctor),
    lookup_ctor_sig s sn = Some ctor ->
    In (fst (unscope (fst ctor))) (skeleton_dts s).
Proof.
  intros s sn ctor H. unfold lookup_ctor_sig in H. pose proof (skeleton_dts_ctors_in_dts s).
  induction (skeleton_ctors s); try inversion H.
  destruct a as [sname args]; simpl in *. destruct (eq_ScopedName sn sname) eqn:E.
  - inversion H2. simpl.
    unfold dts_ctors_in_dts in H0. inversion H0. assumption.
  - apply IHc; try assumption.
    unfold dts_ctors_in_dts in *. inversion H0; assumption.
Qed.

Lemma lookup_ctor_sig_not_in_cdts : forall (s : skeleton) (sn : ScopedName) (ctor : ctor),
    lookup_ctor_sig s sn = Some ctor ->
    ~ In (fst (unscope (fst ctor))) (skeleton_cdts s).
Proof.
  intros s sn ctor H. intro H_in.
  pose proof (skeleton_dts_cdts_disjoint s) as H_unique.
  apply lookup_ctor_sig_in_dts in H.
  specialize (H_unique (fst (unscope (fst ctor)))).
  apply H_unique. auto.
Qed.

Opaque lookup_ctor_sig.

(**************************************************************************************************)
(** ** Codatatypes and Destructors                                                                *)
(**                                                                                               *)
(**************************************************************************************************)

(**************************************************************************************************)
(** Given a typename, return the list of destructors from the destructortable.                    *)
(**************************************************************************************************)
Definition lookup_dtors (ps : skeleton) (tn : TypeName) : option dtors :=
  let filterResult := filter (fun x => match x with (n,_,_) => eq_TypeName (fst (unscope n)) tn end) (skeleton_dtors ps) in
  let tnResult := filter (eq_TypeName tn) (skeleton_cdts ps) in
  match tnResult with [] => None | _ => Some filterResult end.

Lemma lookup_dtors_in_dtors : forall (s : skeleton) (tn : TypeName) (dtors : dtors),
    lookup_dtors s tn = Some dtors ->
    Forall (fun dtor => In dtor (skeleton_dtors s)) dtors.
Proof.
  intros s tn dtors H.
  unfold lookup_dtors in H.
  induction (skeleton_cdts s); try solve [inversion H].
  simpl in H. destruct (eq_TypeName tn a) eqn: E_tn.
  - inversion H. clear. induction (skeleton_dtors s) as [|dtor dtors_rest].
   + apply Forall_nil.
   + simpl. destruct dtor as [[sn x] ts].
     destruct (eq_TypeName (fst (unscope sn)) tn).
     * apply Forall_cons; try auto.
       apply Forall_Or_right. apply IHdtors_rest.
     * apply Forall_Or_right. apply IHdtors_rest.
  - apply IHc; assumption.
Qed.

Lemma in_dtors_lookup_dtors : forall (sk : skeleton) (dtor : dtor),
    In dtor (skeleton_dtors sk) ->
    exists dtors, lookup_dtors sk (fst (unscope (fst (fst dtor)))) = Some dtors.
Proof.
  intros sk dtor H.
  eexists. unfold lookup_dtors.
  assert (H_in_cdts : In (fst (unscope (fst (fst dtor)))) (skeleton_cdts sk)).
  { pose proof (skeleton_cdts_dtors_in_cdts sk) as H_dtors_in_cdts.
    unfold cdts_dtors_in_cdts in H_dtors_in_cdts.
    induction (skeleton_dtors sk); try solve [inversion H].
    inversion H.
    - inversion H_dtors_in_cdts; subst; assumption.
    - inversion H_dtors_in_cdts. apply IHd; try assumption. }
  assert (H_filter : exists d ds, filter (eq_TypeName (fst (unscope (fst (fst dtor))))) (skeleton_cdts sk) = d :: ds).
  { clear - H_in_cdts. in_filter_tac; eauto. }
  inversion_clear H_filter as [d [ds E_filter]]. rewrite E_filter. eauto.
Qed.

Lemma in_dtors_lookup_dtors': forall (sk : skeleton) (dtor : dtor),
    In dtor (skeleton_dtors sk) ->
    exists dtors, lookup_dtors sk (fst (unscope (fst (fst dtor)))) = Some dtors /\

             In dtor dtors.
Proof.
  intros sk dtor H_in. pose proof H_in as H.
  apply in_dtors_lookup_dtors in H. inversion H as [dtors H1]; clear H.
  exists dtors. split; try assumption.
  unfold lookup_dtors in H1.
  match goal with
  | [ H: context [match ?x with | _ => _ end] |- _ ] => destruct x; try solve [inversion H]
  end.
  inversion H1 as [E]; clear H1.
  generalize dependent dtors; induction (skeleton_dtors sk) as [|d_head d_tail]; intros; try solve [inversion H_in]; simpl.
  simpl in E. destruct d_head as [[d_n d_args] d_ret].
  match goal with
  | [ H: context [if ?x then _ else _] |- _ ] => let E := fresh E "_" H in destruct x eqn:E
  end.
  - match goal with
    | [ H: In dtor _ |- _ ] => let H' := fresh H "_inv" in inversion H as [H' | H']
    end.
    + left. assumption.
    + right. destruct dtors; try solve [inversion E]. inversion E. specialize (IHd_tail H_in_inv dtors).
      IH_tac.
  - specialize IHd_tail with (dtors0 := dtors). IH_tac idtac.
    inversion H_in; try assumption.
    rewrite <- H in E_E. simpl in E_E. name_refl_tac. inversion E_E.
Qed.

Lemma lookup_dtors_in_cdts : forall (s : skeleton) (tn : TypeName) (dtors : dtors),
    lookup_dtors s tn = Some dtors ->
    In tn (skeleton_cdts s).
Proof.
  intros s tn dtors H.
  unfold lookup_dtors in H.
  induction (skeleton_cdts s) as [| cdt cdts]; try solve [inversion H].
  simpl in H. destruct (eq_TypeName tn cdt) eqn:E_tn.
  - simpl; left; symmetry. apply eq_TypeName_eq. assumption.
  - simpl; right. apply IHcdts; assumption.
Qed.

Lemma lookup_dtors_not_in_dts : forall (s : skeleton) (tn : TypeName) (dtors : dtors),
    lookup_dtors s tn = Some dtors ->
    ~ In tn (skeleton_dts s).
Proof.
  intros s tn dtors H.
  apply lookup_dtors_in_cdts in H.
  intros H1.
  pose proof (skeleton_dts_cdts_disjoint s) as H_unique.
  unfold dts_cdts_disjoint in H_unique.
  specialize (H_unique tn).  apply H_unique. auto.
Qed.

Lemma lookup_dtors_name_order: forall (s : skeleton) (tn : TypeName) (dtors : dtors),
    lookup_dtors s tn = Some dtors ->
    map (fun x => fst (fst x)) dtors
    = filter (fun t => eq_TypeName (fst (unscope t)) tn) (map (fun x => fst (fst x)) (skeleton_dtors s)).
Proof.
  intros s tn dtors H; unfold lookup_dtors in H.
  match_destruct_tac; inversion H; clear H.
  gen_induction dtors (skeleton_dtors s); destruct dtors; try solve [inversion H1]; eauto;
    destruct a as [[a_sn a_args] a_rt]; simpl in *;
      match_destruct_tac; auto; try solve [inversion H1]; eauto.
  simpl. f_equal; eauto.
Qed.

Opaque lookup_dtors.

(**************************************************************************************************)
(** Given a scoped name of a destructor, return the types of its arguments and the returntype.    *)
(**************************************************************************************************)
Definition lookup_dtor (ps : skeleton) (sn : ScopedName) : option dtor :=
  (find (fun x => eq_ScopedName sn (fst (fst x))) (skeleton_dtors ps)).

Lemma lookup_dtor_in_dtors : forall (s : skeleton) (sn : ScopedName) (dtor : dtor),
    lookup_dtor s sn = Some dtor ->
    In dtor (skeleton_dtors s).
Proof.
  intros s sn dtor H. unfold lookup_dtor in H.
  apply find_in in H. assumption.
Qed.

Lemma in_dtors_lookup_dtor : forall (sk : skeleton) (dtor : dtor),
    In dtor (skeleton_dtors sk) ->
    lookup_dtor sk (fst (fst dtor)) = Some dtor.
Proof.
  intros sk dtor H.
  pose proof (skeleton_cdts_dtor_names_unique sk) as H_unique.
  unfold lookup_dtor. induction (skeleton_dtors sk); try solve [inversion H].
  destruct a as [[sname args] x]. simpl. inversion H as [H1 | H1].
  - rewrite <- H1. simpl. rewrite eq_ScopedName_refl. reflexivity.
  - destruct (eq_ScopedName (fst (fst dtor)) sname) eqn:E_sn.
    + unfold cdts_dtor_names_unique in H_unique. inversion H_unique; subst.
      exfalso. destruct dtor as [[sn y] z]. simpl in *. rewrite eq_ScopedName_eq in E_sn; rewrite E_sn in *.
      apply H3. clear - H1. induction d; try solve [inversion H1].
      inversion H1.
      * left. rewrite H. reflexivity.
      * right; apply IHd; try assumption.
    + apply IHd; try assumption. inversion H_unique. assumption.
Qed.

Lemma lookup_dtor_correct_name : forall (s : skeleton) (sn : ScopedName) (dtor : dtor),
    lookup_dtor s sn = Some dtor ->
    sn = (fst (fst dtor)).
Proof.
  intros s sn dtor H. unfold lookup_dtor in H. induction (skeleton_dtors s); try inversion H.
  destruct a as [[sname args] rtype]; simpl in *. destruct (eq_ScopedName sn sname) eqn:E.
  - inversion H1. simpl. name_eq_tac.
  - apply IHd. assumption.
Qed.

Lemma lookup_dtor_in_cdts : forall (s : skeleton) (sn : ScopedName) (dtor : dtor),
    lookup_dtor s sn = Some dtor ->
    In (fst (unscope (fst (fst dtor)))) (skeleton_cdts s).
Proof.
  intros s sn dtor H. unfold lookup_dtor in H. pose proof (skeleton_cdts_dtors_in_cdts s).
  induction (skeleton_dtors s); try inversion H.
  destruct a as [[sname args] rtype]; simpl in *. destruct (eq_ScopedName sn sname) eqn:E.
  - inversion H2. simpl.
    unfold dts_ctors_in_dts in H0. inversion H0. assumption.
  - apply IHd; try assumption.
    unfold dts_ctors_in_dts in *. inversion H0; assumption.
Qed.

Lemma lookup_dtor_not_in_dts : forall (s : skeleton) (sn : ScopedName) (dtor : dtor),
    lookup_dtor s sn = Some dtor ->
    ~ In (fst (unscope (fst (fst dtor)))) (skeleton_dts s).
Proof.
  intros s sn dtor H. intro H_in.
  pose proof (skeleton_dts_cdts_disjoint s) as H_unique.
  apply lookup_dtor_in_cdts in H.
  specialize (H_unique (fst (unscope (fst (fst dtor))))).
  apply H_unique. auto.
Qed.

Opaque lookup_dtor.

(**************************************************************************************************)
(** ** Functions Signatures                                                                       *)
(**                                                                                               *)
(**************************************************************************************************)

(**************************************************************************************************)
(** Given the name of a function, return the types of its arguments and its returntype.           *)
(**************************************************************************************************)
Definition lookup_fun_sig (ps : skeleton) (n : Name) : option fun_sig :=
  (find (fun x => eq_Name n (fst (fst x))) (skeleton_fun_sigs ps)).

Lemma lookup_fun_sig_name_correct : forall (s : skeleton) (n : Name) (fun_sig : fun_sig),
    lookup_fun_sig s n = Some fun_sig ->
    n = fst (fst fun_sig).
Proof.
  intros s n fun_sig H.
  unfold lookup_fun_sig in H. induction (skeleton_fun_sigs s) as [| fsig fsigs]; try solve [inversion H].
  simpl in H. destruct fsig as [[n_fsig x] y]; simpl in *. destruct (eq_Name n n_fsig) eqn:E_n.
  - inversion H. simpl. rewrite eq_Name_eq in E_n. assumption.
  - apply IHfsigs. assumption.
Qed.

Lemma lookup_fun_sig_in_fun_sigs : forall (sk : skeleton) (n : Name) (sig : fun_sig),
    lookup_fun_sig sk n =  Some sig ->
    In sig (skeleton_fun_sigs sk).
Proof.
  intros sk n sig H.
  unfold lookup_fun_sig in H.
  apply find_in in H. assumption.
Qed.

Lemma in_fun_sigs_lookup_fun_sig : forall (sk : skeleton) (sig : fun_sig),
    In sig (skeleton_fun_sigs sk) ->
    lookup_fun_sig sk (fst (fst sig)) =  Some sig.
Proof.
  intros sk sig H.
  pose proof (skeleton_fun_sigs_names_unique sk) as H_unique.
  unfold lookup_fun_sig. induction (skeleton_fun_sigs sk); try solve [inversion H].
  inversion H; subst.
  - simpl. destruct sig as [[n argts] rtype]; simpl. rewrite eq_Name_refl. reflexivity.
  - simpl. destruct sig as [[n argts] rtype]; simpl.
    destruct a as [[a_n a_argts] a_rtype]; simpl.
    destruct (eq_Name n a_n) eqn:E_n.
    + inversion H_unique; subst.
      exfalso. apply H3. rewrite <- map_compose. do 2 (apply In_fst in H0). rewrite eq_Name_eq in E_n.
      rewrite <- E_n. assumption.
    + apply IHf; try assumption. inversion H_unique; assumption.
Qed.

Opaque lookup_fun_sig.

(**************************************************************************************************)
(** ** Comatch Functions Signatures                                                               *)
(**                                                                                               *)
(**************************************************************************************************)

(**************************************************************************************************)
(** Given the qualified name of a generator function, return the types of its arguments.          *)
(** The "return type" is the first component of the qualified name.                               *)
(**************************************************************************************************)

Definition lookup_gfun_sig_x (sigs : gfun_sigs) (qn : QName) : option gfun_sig :=
  find (fun sig => eq_QName qn (fst sig)) sigs.

Definition lookup_gfun_sig_g (s : skeleton) (qn : QName) : option gfun_sig :=
  lookup_gfun_sig_x (skeleton_gfun_sigs_g s) qn.

Definition lookup_gfun_sig_l (s : skeleton) (qn : QName) : option gfun_sig :=
  lookup_gfun_sig_x (skeleton_gfun_sigs_l s) qn.

Definition lookup_gfun_sig_scoped (s : skeleton) (sn : ScopedName) : option gfun_sig :=
  match sn with
  | local qn => lookup_gfun_sig_l s qn
  | global qn => lookup_gfun_sig_g s qn
  end.

Lemma lookup_gfun_sig_in_gfun_sig_l: forall (sk : skeleton) (qn : QName) (sig : gfun_sig),
    lookup_gfun_sig_l sk qn = Some sig ->
    In sig (skeleton_gfun_sigs_l sk).
Proof.
  intros sk qn sig H. unfold lookup_gfun_sig_l in H. unfold lookup_gfun_sig_x in H.
  apply find_in in H. assumption.
Qed.

Lemma lookup_gfun_sig_in_gfun_sig_g: forall (sk : skeleton) (qn : QName) (sig : gfun_sig),
    lookup_gfun_sig_g sk qn = Some sig ->
    In sig (skeleton_gfun_sigs_g sk).
Proof.
  intros sk qn sig H. unfold lookup_gfun_sig_g in H. unfold lookup_gfun_sig_x in H.
  apply find_in in H. assumption.
Qed.

Lemma lookup_gfun_sig_name_correct_g : forall (s : skeleton) (qn : QName) (gfun_sig : gfun_sig),
    lookup_gfun_sig_g s qn = Some gfun_sig ->
    qn = fst gfun_sig.
Proof.
  intros s n fun_sig H.
  unfold lookup_gfun_sig_g in H. induction (skeleton_gfun_sigs_g s) as [| fsig fsigs]; try solve [inversion H].
  simpl in H. destruct fsig as [n_fsig x]; simpl in *. destruct (eq_QName n n_fsig) eqn:E_n.
  - inversion H. simpl. rewrite eq_QName_eq in E_n. assumption.
  - apply IHfsigs. assumption.
Qed.

Lemma lookup_gfun_sig_name_correct_l : forall (s : skeleton) (qn : QName) (gfun_sig : gfun_sig),
    lookup_gfun_sig_l s qn = Some gfun_sig ->
    qn = fst gfun_sig.
Proof.
  intros s n fun_sig H.
  unfold lookup_gfun_sig_l in H. induction (skeleton_gfun_sigs_l s) as [| fsig fsigs]; try solve [inversion H].
  simpl in H. destruct fsig as [n_fsig x]; simpl in *. destruct (eq_QName n n_fsig) eqn:E_n.
  - inversion H. simpl. rewrite eq_QName_eq in E_n. assumption.
  - apply IHfsigs. assumption.
Qed.


(**************************************************************************************************)
(** ** Match Functions Signatures                                                                 *)
(**                                                                                               *)
(**************************************************************************************************)

(**************************************************************************************************)
(** Given the qualified name of a consumer function, return the types of its arguments and        *)
(** its return type. The type of the first argument of a destructor function is given by the      *)
(** first component of the qualified name.                                                        *)
(**************************************************************************************************)

Definition lookup_cfun_sig_x (sigs : cfun_sigs) (qn : QName) : option cfun_sig :=
  find (fun sig => eq_QName qn (fst (fst sig))) sigs.

Definition lookup_cfun_sig_g (s : skeleton) (qn : QName) : option cfun_sig :=
  lookup_cfun_sig_x (skeleton_cfun_sigs_g s) qn.

Definition lookup_cfun_sig_l (s : skeleton) (qn : QName) : option cfun_sig :=
  lookup_cfun_sig_x (skeleton_cfun_sigs_l s) qn.

Definition lookup_cfun_sig_scoped (s : skeleton) (sn : ScopedName) : option cfun_sig :=
  match sn with
  | local qn => lookup_cfun_sig_l s qn
  | global qn => lookup_cfun_sig_g s qn
  end.

Lemma lookup_cfun_sig_in_cfun_sig_l: forall (sk : skeleton) (qn : QName) (sig : cfun_sig),
    lookup_cfun_sig_l sk qn = Some sig ->
    In sig (skeleton_cfun_sigs_l sk).
Proof.
  intros sk qn sig H. unfold lookup_cfun_sig_l in H. unfold lookup_cfun_sig_x in H.
  apply find_in in H. assumption.
Qed.

Lemma lookup_cfun_sig_in_cfun_sig_g: forall (sk : skeleton) (qn : QName) (sig : cfun_sig),
    lookup_cfun_sig_g sk qn = Some sig ->
    In sig (skeleton_cfun_sigs_g sk).
Proof.
  intros sk qn sig H. unfold lookup_cfun_sig_g in H. unfold lookup_cfun_sig_x in H.
  apply find_in in H. assumption.
Qed.

Lemma lookup_cfun_sig_name_correct_g : forall (s : skeleton) (qn : QName) (cfun_sig : cfun_sig),
    lookup_cfun_sig_g s qn = Some cfun_sig ->
    qn = fst (fst cfun_sig).
Proof.
  intros s n fun_sig H.
  unfold lookup_cfun_sig_g in H. induction (skeleton_cfun_sigs_g s) as [| fsig fsigs]; try solve [inversion H].
  simpl in H. destruct fsig as [[n_fsig x] y]; simpl in *. destruct (eq_QName n n_fsig) eqn:E_n.
  - inversion H. simpl. rewrite eq_QName_eq in E_n. assumption.
  - apply IHfsigs. assumption.
Qed.

Lemma lookup_cfun_sig_name_correct_l : forall (s : skeleton) (qn : QName) (cfun_sig : cfun_sig),
    lookup_cfun_sig_l s qn = Some cfun_sig ->
    qn = fst (fst cfun_sig).
Proof.
  intros s n fun_sig H.
  unfold lookup_cfun_sig_l in H. induction (skeleton_cfun_sigs_l s) as [| fsig fsigs]; try solve [inversion H].
  simpl in H. destruct fsig as [[n_fsig x] y]; simpl in *. destruct (eq_QName n n_fsig) eqn:E_n.
  - inversion H. simpl. rewrite eq_QName_eq in E_n. assumption.
  - apply IHfsigs. assumption.
Qed.


(**************************************************************************************************)
(** ** Datatypes and Constructors                                                                 *)
(**                                                                                               *)
(**************************************************************************************************)

Lemma In_constructor_lookupsig : forall (prog : skeleton)(cargs : list TypeName)(sn : ScopedName),
    In (sn, cargs) (skeleton_ctors prog) <->
    lookup_ctor_sig prog sn = Some (sn, cargs).
Proof.
  intros prog cargs sn.  split; intro H.
  - (* -> *)
    apply in_ctors_lookup_ctor_sig in H. simpl in H. assumption.
  -(* <- *)
   apply lookup_ctor_sig_in_ctors in H. assumption.
Qed.

Lemma lookup_constructor_lemma : forall (prog : skeleton)(tn : TypeName)(ctor : ScopedName * list TypeName)
                                        (ctorlist : list (ScopedName * list TypeName)),
    lookup_ctors prog tn = Some ctorlist ->
    In ctor ctorlist ->
    In ctor (skeleton_ctors prog).
Proof.
  intros prog tn ctor ctorlist H H_in.
  apply lookup_ctors_in_ctors in H. apply Forall_extract with (ls := ctorlist) (a := ctor); try assumption.
Qed.

Lemma In_ctors_in_dts : forall (n : ScopedName) tn (p : skeleton),
  In (n, tn) (skeleton_ctors p) ->
  In (fst (unscope n)) (skeleton_dts p).
Proof.
  intros n tn p H.
  pose proof (skeleton_dts_ctors_in_dts p). unfold dts_ctors_in_dts in H0.
  rewrite Forall_forall in H0. apply H0 in H. simpl in H. assumption.
Qed.

Lemma ctor_lookup_succeeds : forall (sk : skeleton) (sn : ScopedName) (cargs : list TypeName),
    In (sn, cargs) (skeleton_ctors sk) ->
    exists dt dtlist, filter (eq_TypeName (fst (unscope sn))) (skeleton_dts sk) = dt :: dtlist.
Proof.
  intros sk sn cargs Hin.
  pose proof (skeleton_dts_ctors_in_dts sk) as Hwf.
  induction (skeleton_ctors sk) as [|ctor ctors]; try solve [inversion Hin].
  destruct ctor as [ctor_sn ctor_ts].
  inversion Hwf; subst.
  inversion Hin.
  -inversion H as [Esn]; subst. inversion Hwf.
   clear - H4.
   induction (skeleton_dts sk); try solve [inversion H4].
   destruct (eq_TypeName (fst (unscope sn)) a) eqn:Esn.
   +exists a. simpl. rewrite Esn.
    exists (filter (eq_TypeName (fst (unscope sn))) d). reflexivity.
   +inversion H4.
    *simpl in H. symmetry in H. apply eq_TypeName_eq in H. rewrite H in Esn. discriminate Esn.
    *simpl. rewrite Esn. apply IHd; try assumption.
  -apply IHctors; try assumption.
Qed.

Lemma dtor_lookup_succeeds:
  forall (sk : skeleton) (sn : ScopedName) (dargs : list TypeName) (t : TypeName),
    In (sn, dargs, t) (skeleton_dtors sk) ->
    exists (dt : ScopedName * list TypeName * TypeName) (dtlist : list (ScopedName * list TypeName * TypeName)),
      filter
        (fun x : ScopedName * list TypeName * TypeName =>
           let (y, _) := x in let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (unscope sn)))
        (skeleton_dtors sk) = dt :: dtlist.
Proof.
  intros sk sn dargs t Hin_dtors.
  induction (skeleton_dtors sk); try solve [inversion Hin_dtors]. simpl.
  - destruct a as [[a_sn a_ts] a_t].
    destruct (eq_TypeName (fst (unscope a_sn)) (fst (unscope sn))) eqn:Etn.
    + exists (a_sn, a_ts, a_t).
      exists (filter
           (fun x : ScopedName * list TypeName * TypeName =>
              let (y, _) := x in let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (unscope sn))) d).
      reflexivity.
    + inversion Hin_dtors.
      * inversion H as [[E _E _E']]. apply f_equal with (f := fun x => fst (unscope x)) in E.
        apply eq_TypeName_eq in E. rewrite Etn in E. discriminate E.
      * apply IHd; try assumption.
Qed.

Lemma filter_preserves_In : forall (sn : ScopedName) (cargs : list TypeName) (ctors : list (ScopedName * list TypeName)),
    In (sn, cargs) ctors <->
    In (sn, cargs) (filter (fun p : ScopedName * list TypeName => let (x, _) := p in eq_TypeName (fst (unscope x)) (fst (unscope sn))) ctors).
Proof.
  intros sn cargs ctors. unfold iff. split.
  -intro H.
   induction ctors; inversion H.
   +rewrite H0 in *; clear H0 H.
    simpl. rewrite eq_TypeName_refl.
    unfold In. left. reflexivity.
   +simpl. destruct a as [a_sn a_ts].
    destruct (eq_TypeName (fst (unscope a_sn)) (fst (unscope sn))).
    *simpl. right. apply IHctors; try assumption.
    *apply IHctors; try assumption.
  -intro H.
   induction ctors; try solve [simpl in H; contradiction].
   simpl in H. destruct a as [a_sn a_ts]. destruct (eq_TypeName (fst (unscope a_sn)) (fst (unscope sn))).
   +simpl in H.
    inversion H; try solve [left; assumption].
    right. apply IHctors; try assumption.
   +right. apply IHctors; try assumption.
Qed.

Lemma filter_preserves_In_neg : forall (sn : ScopedName) (dargs : list TypeName) (dtors : list (ScopedName * list TypeName * TypeName)) (t : TypeName),
    In (sn, dargs, t) dtors <->
    In (sn, dargs, t) (filter (fun t : ScopedName * list TypeName * TypeName => let (p, _) := t in let (x, _) := p in eq_TypeName (fst (unscope x)) (fst (unscope sn))) dtors).
Proof.
  intros sn dargs dtors t. unfold iff. split.
  -intro H.
   induction dtors; inversion H.
   +rewrite H0 in *; clear H0 H.
    simpl. rewrite eq_TypeName_refl.
    unfold In. left. reflexivity.
   +simpl. destruct a as [[a_sn a_ts] a_t].
    destruct (eq_TypeName (fst (unscope a_sn)) (fst (unscope sn))).
    *simpl. right. apply IHdtors; try assumption.
    *apply IHdtors; try assumption.
  -intro H.
   induction dtors; try solve [simpl in H; contradiction].
   simpl in H. destruct a as [[a_sn a_ts] a_t]. destruct (eq_TypeName (fst (unscope a_sn)) (fst (unscope sn))).
   +simpl in H.
    inversion H; try solve [left; assumption].
    right. apply IHdtors; try assumption.
   +right. apply IHdtors; try assumption.
Qed.

Lemma In_filter_nonempty : forall (sn : ScopedName) (cargs : list TypeName) (ctors : list (ScopedName * list TypeName)),
    ~(In (sn, cargs) ctors /\
      List.length (filter (fun x => eq_ScopedName sn (fst x)) ctors) = 0).
Proof.
  intros sn cargs ctors H.
  inversion_clear H as [Hin Hlen].
  induction ctors; try solve [inversion Hin].
  destruct a as [a_sn a_ts]. simpl in Hlen. inversion Hin.
  -inversion H as [[Esn _E]]. symmetry in Esn. apply eq_ScopedName_eq in Esn.
   rewrite Esn in *. inversion Hlen.
  -destruct (eq_ScopedName sn a_sn) eqn:Esn; try solve [inversion Hlen].
   apply IHctors; try assumption.
Qed.

Lemma In_filter_nonempty_neg : forall (sn : ScopedName) (dargs : list TypeName) (t : TypeName) (dtors : list (ScopedName * list TypeName * TypeName)),
    ~(In (sn, dargs, t) dtors /\
      List.length (filter (fun x => eq_ScopedName sn (fst (fst x))) dtors) = 0).
Proof.
  intros sn dargs t dtors H.
  inversion_clear H as [Hin Hlen].
  induction dtors; try solve [inversion Hin].
  destruct a as [[a_sn a_ts] a_t]. simpl in Hlen. inversion Hin.
  -inversion H as [[Esn _E]]. symmetry in Esn. apply eq_ScopedName_eq in Esn.
   rewrite Esn in *. inversion Hlen.
  -destruct (eq_ScopedName sn a_sn) eqn:Esn; try solve [inversion Hlen].
   apply IHdtors; try assumption.
Qed.

Lemma constructor_type_unique : forall (sk : skeleton) (sn : ScopedName) (cargs cargs' : list TypeName) (ctorlist : ctors),
    In (sn, cargs) (skeleton_ctors sk) ->
    lookup_ctors sk (fst (unscope sn)) = Some ctorlist ->
    In (sn, cargs') ctorlist ->
    cargs = cargs'.
Proof.
  intros sk sn cargs cargs' ctorlist H_in_ctors H_lookup H_in_ctorlist.
  apply lookup_ctors_in_ctors in H_lookup.
  assert (H_in_ctors' : In (sn, cargs') (skeleton_ctors sk)).
  { apply Forall_extract with (ls := ctorlist) (a := (sn, cargs')); assumption. }
  clear H_lookup.
  pose proof (skeleton_dts_ctor_names_unique sk) as H_unique.
  unfold dts_ctor_names_unique in H_unique.
  induction (skeleton_ctors sk) as [| ctor ctors]; try solve [inversion H_in_ctors].
  inversion H_unique as [| _tmp _tmp1 H_not_in H_unique_rest]; subst.
  inversion H_in_ctors as [E_ctors | E_ctors].
  - rewrite E_ctors in *; clear E_ctors.
    inversion H_in_ctors' as [E_ctors' | E_ctors'].
    + inversion E_ctors'; reflexivity.
    + simpl in H_not_in. exfalso. apply H_not_in. apply In_fst in E_ctors'. assumption.
  - inversion H_in_ctors' as [E_ctors' | E_ctors'].
    + rewrite E_ctors' in H_not_in. exfalso; apply H_not_in.
      simpl. apply In_fst in E_ctors; assumption.
    + apply IHctors; try assumption.
Qed.

Lemma destructor_type_unique : forall (sk : skeleton) (sn : ScopedName) (dargs dargs' : list TypeName) (t t' : TypeName) (dtorlist : dtors),
    In (sn, dargs, t) (skeleton_dtors sk) ->
    lookup_dtors sk (fst (unscope sn)) = Some dtorlist ->
    In (sn, dargs', t') dtorlist ->
    dargs = dargs' /\ t = t'.
Proof.
  intros sk sn dargs dargs' t t' dtorlist H_in_dtors H_lookup H_in_dtorlist.
  apply lookup_dtors_in_dtors in H_lookup.
  assert (H_in_dtors' : In (sn, dargs', t') (skeleton_dtors sk)).
  { apply Forall_extract with (ls := dtorlist) (a := (sn, dargs', t')); assumption. }
  clear H_lookup.
  pose proof (skeleton_cdts_dtor_names_unique sk) as H_unique.
  unfold cdts_dtor_names_unique in H_unique.
  induction (skeleton_dtors sk) as [| dtor dtors]; try solve [inversion H_in_dtors].
  inversion H_unique as [| _tmp _tmp1 H_not_in H_unique_rest]; subst.
  inversion H_in_dtors as [E_dtors | E_dtors].
  - rewrite E_dtors in *; clear E_dtors.
    inversion H_in_dtors' as [E_dtors' | E_dtors'].
    + inversion E_dtors'; split; reflexivity.
    + simpl in H_not_in. exfalso. apply H_not_in. do 2 (apply In_fst in E_dtors').

      rewrite map_compose in E_dtors'. assumption.
  - inversion H_in_dtors' as [E_dtors' | E_dtors'].
    + rewrite E_dtors' in H_not_in. exfalso; apply H_not_in.
      simpl. do 2 (apply In_fst in E_dtors). rewrite map_compose in E_dtors; assumption.
    + apply IHdtors; try assumption.
Qed.

(**************************************************************************************************)
(** ** Codatatypes and Destructors                                                                *)
(**                                                                                               *)
(**************************************************************************************************)


Lemma In_destructor_lookupsig : forall (prog : skeleton)(dargs : list TypeName)(rtype :  TypeName)(sn : ScopedName),
    In (sn, dargs, rtype) (skeleton_dtors prog) <->
    lookup_dtor prog sn = Some (sn, dargs, rtype).
Proof.
  intros prog dargs rtype sn. split; intro H.
    - (* -> *)
    apply in_dtors_lookup_dtor in H. simpl in H. assumption.
  -(* <- *)
   apply lookup_dtor_in_dtors in H. assumption.
Qed.

Lemma lookup_destructor_lemma : forall (prog : skeleton)(tn : TypeName)(dtor : ScopedName * list TypeName * TypeName)
                                        (dtorlist : list (ScopedName * list TypeName * TypeName)),
    lookup_dtors prog tn = Some dtorlist ->
    In dtor dtorlist ->
    In dtor (skeleton_dtors prog).
Proof.
  intros prog tn dtor dtorlist H H_in.
  apply lookup_dtors_in_dtors in H. apply Forall_extract with (ls := dtorlist) (a := dtor); try assumption.
Qed.

Lemma In_dtors_in_cdts : forall (n : ScopedName) tn (p : skeleton) x,
  In (n, tn, x) (skeleton_dtors p) ->
  In (fst (unscope n)) (skeleton_cdts p).
Proof.
  intros n tn p x H.
  pose proof (skeleton_cdts_dtors_in_cdts p). unfold cdts_dtors_in_cdts in H0.
  rewrite Forall_forall in H0. apply H0 in H. simpl in H. assumption.
Qed.

(**************************************************************************************************)
(** ** Functions Signatures                                                                       *)
(**                                                                                               *)
(**************************************************************************************************)

Lemma In_fun_sig_lookup_fun_sig : forall (prog : skeleton)(n : Name)(argts : list TypeName) (rtype : TypeName),
    In (n,argts,rtype) (skeleton_fun_sigs prog) <->
    lookup_fun_sig prog n = Some (n,argts,rtype).
Proof.
  intros prog n argts rtype. split; intro H.
  - apply in_fun_sigs_lookup_fun_sig in H. simpl in H. assumption.
  - apply lookup_fun_sig_in_fun_sigs in H. assumption.
Qed.

(**************************************************************************************************)
(** ** Comatch Functions Signatures                                                               *)
(**                                                                                               *)
(**************************************************************************************************)


Lemma In_gfun_sig_lookup_gfun_sig_g : forall (prog : skeleton)(qn : QName)(argts : list TypeName),
    In (qn,argts) (skeleton_gfun_sigs_g prog) <->
    lookup_gfun_sig_g prog qn = Some (qn,argts).
Proof.
  intros prog qn argts. split; intro H.
  - (* -> *)
    unfold lookup_gfun_sig_g. unfold lookup_gfun_sig_x.
    pose proof (skeleton_gfun_sigs_names_unique_g prog) as H_names_unique. unfold gfun_sigs_names_unique in H_names_unique.
    induction (skeleton_gfun_sigs_g prog); try solve [inversion H].
    simpl in H. destruct H.
    + subst. simpl. name_refl_tac.
    + destruct a. simpl in *. inversion H_names_unique; subst. specialize (IHg H H3).
      destruct (eq_QName qn q) eqn:E.
      * name_eq_tac. exfalso. clear - H2 IHg. induction g; simpl in *; try solve [inversion IHg].
        destruct a; simpl in *. destruct (eq_QName q q0) eqn:E. name_eq_tac.
        ** apply H2. left. reflexivity.
        ** apply IHg0; try assumption. intro Habs. apply H2. right. assumption.
      * assumption.
  - (* <- *)
    unfold lookup_gfun_sig_g in H. unfold lookup_gfun_sig_x in H. apply find_in in H. assumption.
Qed.


Lemma In_gfun_sig_lookup_gfun_sig_l : forall (prog : skeleton)(qn : QName)(argts : list TypeName),
    In (qn,argts) (skeleton_gfun_sigs_l prog) <->
    lookup_gfun_sig_l prog qn = Some (qn,argts).
Proof.
  intros prog qn argts. split; intro H.
  - (* -> *)
    unfold lookup_gfun_sig_l. unfold lookup_gfun_sig_x.
    pose proof (skeleton_gfun_sigs_names_unique_l prog) as H_names_unique. unfold gfun_sigs_names_unique in H_names_unique.
    induction (skeleton_gfun_sigs_l prog); try solve [inversion H].
    simpl in H. destruct H.
    + subst. simpl. name_refl_tac.
    + destruct a. simpl in *. inversion H_names_unique; subst. specialize (IHg H H3).
      destruct (eq_QName qn q) eqn:E.
      * name_eq_tac. exfalso. clear - H2 IHg. induction g; simpl in *; try solve [inversion IHg].
        destruct a; simpl in *. destruct (eq_QName q q0) eqn:E. name_eq_tac.
        ** apply H2. left. reflexivity.
        ** apply IHg0; try assumption. intro Habs. apply H2. right. assumption.
      * assumption.
  - (* <- *)
    unfold lookup_gfun_sig_l in H. unfold lookup_gfun_sig_x in H. apply find_in in H. assumption.
Qed.

Opaque lookup_gfun_sig_g lookup_gfun_sig_l.
(**************************************************************************************************)
(** ** Match Functions Signatures                                                                 *)
(**                                                                                               *)
(**************************************************************************************************)


Lemma In_cfun_sig_lookup_cfun_sig_g : forall (sk : skeleton)(qn : QName)(argts : list TypeName) (rtype : TypeName),
    In (qn,argts,rtype) (skeleton_cfun_sigs_g sk) <->
    lookup_cfun_sig_g sk qn = Some (qn,argts,rtype).
Proof.
  intros prog qn argts rtype. split; intro H.
    - (* -> *)
    unfold lookup_cfun_sig_g. unfold lookup_cfun_sig_x.
    pose proof (skeleton_cfun_sigs_names_unique_g prog) as H_names_unique. unfold cfun_sigs_names_unique in H_names_unique.
    induction (skeleton_cfun_sigs_g prog); try solve [inversion H].
    simpl in H. destruct H.
    + subst. simpl. name_refl_tac.
    + destruct a as [[q args] rtype']. simpl in *. inversion H_names_unique; subst. specialize (IHc H H3).
      destruct (eq_QName qn q) eqn:E.
      * name_eq_tac. exfalso. clear - H2 IHc. induction c; simpl in *; try solve [inversion IHc].
        destruct a as [[q0 x] y]; simpl in *. destruct (eq_QName q q0) eqn:E. name_eq_tac.
        ** apply H2. left. reflexivity.
        ** apply IHc0; try assumption. intro Habs. apply H2. right. assumption.
      * assumption.
  - (* <- *)
    unfold lookup_cfun_sig_g in H. unfold lookup_cfun_sig_x in H. apply find_in in H. assumption.
Qed.

Lemma In_cfun_sig_lookup_cfun_sig_l : forall (sk : skeleton)(qn : QName)(argts : list TypeName) (rtype : TypeName),
    In (qn,argts,rtype) (skeleton_cfun_sigs_l sk) <->
    lookup_cfun_sig_l sk qn = Some (qn,argts,rtype).
Proof.
  intros prog qn argts rtype. split; intro H.
  - (* -> *)
    unfold lookup_cfun_sig_l. unfold lookup_cfun_sig_x.
    pose proof (skeleton_cfun_sigs_names_unique_l prog) as H_names_unique. unfold cfun_sigs_names_unique in H_names_unique.
    induction (skeleton_cfun_sigs_l prog); try solve [inversion H].
    simpl in H. destruct H.
    + subst. simpl. name_refl_tac.
    + destruct a as [[q args] rtype']. simpl in *. inversion H_names_unique; subst. specialize (IHc H H3).
      destruct (eq_QName qn q) eqn:E.
      * name_eq_tac. exfalso. clear - H2 IHc. induction c; simpl in *; try solve [inversion IHc].
        destruct a as [[q0 x] y]; simpl in *. destruct (eq_QName q q0) eqn:E. name_eq_tac.
        ** apply H2. left. reflexivity.
        ** apply IHc0; try assumption. intro Habs. apply H2. right. assumption.
      * assumption.
  - (* <- *)
    unfold lookup_cfun_sig_l in H. unfold lookup_cfun_sig_x in H. apply find_in in H. assumption.
Qed.

Opaque lookup_cfun_sig_g lookup_cfun_sig_l.

(**  NEW LEMMAS *)

Lemma no_simultaneous_xtors : forall (sk : skeleton) (tn : TypeName),
    ~ ((exists (ctors : list (ScopedName * list TypeName)), lookup_ctors sk tn = Some ctors) /\
       (exists (dtors : list (ScopedName * list TypeName * TypeName)), lookup_dtors sk tn = Some dtors)).
Proof.
  intros sk tn [[ ctors H_abs1] [dtors H_abs2]].
  pose proof (skeleton_dts_cdts_disjoint sk tn) as H. apply H. split.
  - apply lookup_ctors_in_dts in H_abs1; assumption.
  - apply lookup_dtors_in_cdts in H_abs2; assumption.
Qed.

