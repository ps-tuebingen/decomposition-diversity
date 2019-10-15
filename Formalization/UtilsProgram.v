Require Import Coq.Lists.List.
Import ListNotations.

Require Import Unique.
Require Import GenericLemmas.
Require Import GenericTactics.
Require Import Skeleton.
Require Import Names.
Require Import AST.
Require Import Typechecker.
Require Import UtilsSkeleton.
Require Import BodyTypeDefs.
Require Export ProgramDef.

(**************************************************************************************************)
(** Given the name of a function, return its body                                                 *)
(**************************************************************************************************)
Definition lookup_fun_bods (p : program) (n : Name) : option fun_bod :=
  let result := (fix lookupHelper (bs : list (Name * expr)) : option fun_bod :=
                   match bs with
                   | [] => None (*Cannot occur*)
                   | (f :: fs) =>
                     if eq_Name (fst f) n
                     then Some (snd f)
                     else lookupHelper fs
                end) (program_fun_bods p)
  in result.

(* Lemma lookupFunctionBody_In : forall (prog : program) (n : Name) (e : expr), *)
(*     lookupFunctionBody prog n = Some e <-> *)
(*     In (n, e) (program_fun_bods prog). *)
(* Proof. *)
(*   intros prog n e. split. *)
(*   -(* -> *) *)
(*     intro H_lookup. *)
(*     unfold lookupFunctionBody in H_lookup. *)
(*     induction (funbodies prog). *)
(*     *inversion H_lookup. *)
(*     *destruct (eq_Name (fst a) n) eqn:E. *)
(*      **destruct a. name_eq_tac. inversion H_lookup. subst. *)
(*        simpl. left. reflexivity. *)
(*      **simpl. right. apply IHf. assumption. *)
(*   -(* <- *) *)
(*     intro H_In. *)
(*     assert (H_wf : hasAllFunbodies (fsigs (skeleton prog)) (funbodies prog)); *)
(*       try apply hasAllFuns;  unfold hasAllFunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*     rewrite Forall_forall in H_wf2. specialize (H_wf2 (n, e) H_In). *)
(*     assert (H_exists : exists argts rtype, In (n, argts, rtype) (fsigs (skeleton prog))). *)
(*     +clear H_wf1. *)
(*      induction (fsigs (skeleton prog)); try (inversion H_wf2). *)
(*      simpl in H_wf2. destruct (eq_Name (fst (fst a))) eqn:E. *)
(*      *destruct a as [[a0 a1] a2]. simpl in *. *)
(*       exists a1. exists a2. left. name_eq_tac. *)
(*      *specialize (IHf H_wf2). destruct IHf. destruct H. *)
(*       exists x. exists x0. simpl. right. assumption. *)
(*     +destruct H_exists. destruct H. *)
(*      rewrite Forall_forall in H_wf1. specialize (H_wf1 (n,x,x0) H). simpl in H_wf1. *)
(*      clear H_wf2 H. *)
(*      unfold lookupFunctionBody. *)
(*      induction (funbodies prog). *)
(*      *simpl in *. contradiction. *)
(*      *destruct a. simpl in *. destruct H_In. *)
(*       **inversion H; subst. name_refl_tac. *)
(*       **destruct (eq_Name n n0) eqn:E; rewrite eq_Name_symm in E; rewrite E; try solve [apply IHf; assumption]. *)
(*         exfalso. name_eq_tac. simpl in H_wf1. inversion H_wf1. clear - H1 H. *)
(*         induction f; try contradiction. *)
(*         simpl in *. destruct a. destruct H. *)
(*         ***inversion H; subst. simpl in H1. name_refl_tac. simpl in H1. inversion H1. *)
(*         ***apply IHf; try assumption. simpl in H1. destruct (eq_Name n n0). *)
(*            inversion H1. assumption. *)
(* Qed. *)

Lemma lookup_fun_bods_is_first : forall (prog : program) (n : Name) (e : expr),
    lookup_fun_bods prog n = Some e <->
    is_first (n, e) (program_fun_bods prog) (fun x y => eq_Name (fst x) (fst y)).
Proof.
  intros prog n e.
  unfold iff. split.
  - intro Hlookup. unfold lookup_fun_bods in Hlookup.
    induction (program_fun_bods prog); try solve [inversion Hlookup].
    destruct (eq_Name (fst a) n) eqn:En.
    + destruct a. simpl in *.
      apply eq_Name_eq in En. symmetry in En. rewrite En in *. rewrite eq_Name_refl in Hlookup.
      inversion Hlookup as [El]. rewrite El in *.
      apply is_first_head.
    + apply is_first_tail.
      * simpl. rewrite eq_Name_symm. assumption.
      * destruct a; simpl in *; rewrite En in Hlookup.
        apply IHf; try assumption.
  - intro H_is_first. unfold lookup_fun_bods.
    induction (program_fun_bods prog); try solve [inversion H_is_first].
    destruct (eq_Name (fst a) n) eqn:En; destruct a as [a_n a_e]; simpl in *; rewrite En.
    + f_equal. inversion H_is_first; try reflexivity.
      subst. simpl in H2. rewrite eq_Name_symm in H2. rewrite H2 in En. discriminate En.
    + apply IHf.
      inversion H_is_first; try assumption.
      inversion H1. symmetry in H4. apply eq_Name_eq in H4. rewrite H4 in En. discriminate En.
Qed.

(* Lemma lookupFunctionSig_lookupFunctionBody : forall (prog : program)(n : Name) (sig : list TypeName * TypeName), *)
(*     lookupFunctionSig (skeleton prog) n = Some sig -> *)
(*     exists body, lookupFunctionBody prog n = Some body. *)
(* Proof. *)
(*   intros prog n sig H_lookupSig. *)
(*   assert (H_wf: hasAllFunbodies (fsigs (skeleton prog)) (funbodies prog)); *)
(*     try apply hasAllFuns; unfold hasAllFunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*   clear H_wf2. rewrite Forall_forall in H_wf1. specialize (H_wf1 (n, (fst sig), (snd sig))). *)
(*   destruct sig. *)
(*   rewrite <- In_funsig_lookupsig in H_lookupSig. specialize (H_wf1 H_lookupSig). *)
(*   clear - H_wf1. simpl in *. *)
(*   unfold lookupFunctionBody. induction (funbodies prog). *)
(*   -simpl in *. inversion H_wf1. *)
(*   -simpl in *. destruct (eq_Name n (fst a)) eqn:E. *)
(*    +rewrite eq_Name_symm in E. rewrite E. exists (snd a). reflexivity. *)
(*    +rewrite eq_Name_symm in E. rewrite E. apply IHf.  assumption. *)
(* Qed. *)

(* Lemma lookupFunctionBody_lookupFunctionSig : forall (prog : program) (n : Name) (e : expr), *)
(*     lookupFunctionBody prog n = Some e -> *)
(*     exists sig, lookupFunctionSig (skeleton prog) n = Some sig. *)
(* Proof. *)
(*   intros prog n e H_lookupBody. *)
(*   assert (H_wf: hasAllFunbodies (fsigs (skeleton prog)) (funbodies prog)); *)
(*     try apply hasAllFuns; unfold hasAllFunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*   rewrite lookupFunctionBody_In in H_lookupBody.  *)
(*   clear H_wf1. rewrite Forall_forall in H_wf2. specialize (H_wf2 (n,e) H_lookupBody). clear - H_wf2. *)
(*   unfold lookupFunctionSig. induction (fsigs (skeleton prog)). *)
(*   -simpl in *. inversion H_wf2. *)
(*   -simpl in *. destruct (eq_Name (fst (fst a)) n) eqn:E. *)
(*    +destruct a as [[a0 a1] a2]. exists (a1, a2). simpl. name_eq_tac. simpl. name_refl_tac. *)
(*    +destruct a as [[a0 a1] a2]. simpl in *. rewrite E. apply IHf. assumption. *)
(* Qed. *)

(**************************************************************************************************)
(** Given the qualified name of a generator function, return its body, i.e. a list of cases.      *)
(**************************************************************************************************)
Definition lookup_gfun_bods_x (bodies : gfun_bods) (qn : QName) : option gfun_bod_named :=
  find (fun body => eq_QName qn (fst body)) bodies.

Definition lookup_gfun_bods_g (p : program) (qn : QName) : option gfun_bod_named :=
  lookup_gfun_bods_x (program_gfun_bods_g p) qn.
Definition lookup_gfun_bods_l (p : program) (qn : QName) : option gfun_bod_named :=
  lookup_gfun_bods_x (program_gfun_bods_l p) qn.
Definition lookup_gfun_bods_scoped (p : program) (sn : ScopedName) : option gfun_bod_named :=
  match sn with
    | local qn  => lookup_gfun_bods_l p qn
    | global qn => lookup_gfun_bods_g p qn
  end.

Lemma lookup_gfun_bods_g_scoped: forall (qn : QName) (p : program),
    lookup_gfun_bods_g p qn = lookup_gfun_bods_scoped p (global qn).
auto. Qed.

Lemma lookup_gfun_bods_l_scoped: forall (qn : QName) (p : program),
    lookup_gfun_bods_l p qn = lookup_gfun_bods_scoped p (local qn).
auto. Qed.

Lemma lookup_gfun_bods_x_fst: forall (bodies : gfun_bods) (qn : QName) (body_named : gfun_bod_named),
    lookup_gfun_bods_x bodies qn = Some body_named ->
    exists body, body_named = (qn, body).
Proof.
  intros bodies qn body_named H.
  induction bodies; try solve [inversion H].
  simpl in H.
  match goal with
  | [ H: (if ?p then _ else _) = Some _ |- _ ] =>
    destruct p eqn:E
  end.
  - inversion H. apply eq_QName_eq in E. destruct a. simpl in *. subst qn. eauto.
  - IH_tac ltac:(assumption).
Qed.

Lemma lookup_gfun_bods_g_fst: forall (p : program) (qn : QName) (body_named : gfun_bod_named),
    lookup_gfun_bods_g p qn = Some body_named ->
    exists body, body_named = (qn, body).
Proof.
  intros p qn body_named H.
  unfold lookup_gfun_bods_g in H.
  apply lookup_gfun_bods_x_fst in H; assumption.
Qed.

Lemma lookup_gfun_bods_l_fst: forall (p : program) (qn : QName) (body_named : gfun_bod_named),
    lookup_gfun_bods_l p qn = Some body_named ->
    exists body, body_named = (qn, body).
Proof.
  intros p qn body_named H.
  unfold lookup_gfun_bods_l in H.
  apply lookup_gfun_bods_x_fst in H; assumption.
Qed.

Lemma lookup_gfun_bods_scoped_fst: forall (sn : ScopedName) (p : program) (body_named : gfun_bod_named),
    lookup_gfun_bods_scoped p sn = Some body_named ->
    exists body, body_named = (unscope sn, body).
Proof.
  intros sn p body_named H.
  destruct sn; unfold lookup_gfun_bods_scoped in H.
  - apply lookup_gfun_bods_l_fst in H; assumption.
  - apply lookup_gfun_bods_g_fst in H; assumption.
Qed.

(* Lemma lookupGenFunctionBody_In : forall (prog : program) (qn : QName) (cocases : list (ScopedName * expr)), *)
(*     lookup_gfun_bods_g prog qn = Some cocases <-> *)
(*     In (qn, cocases) (comatchbodies prog). *)
(* Proof. *)
(*   intros prog qn cocases. split. *)
(*   -(* -> *) *)
(*     intro H_lookup. unfold lookupGenFunctionBody in H_lookup. *)
(*     induction (comatchbodies prog). *)
(*     +inversion H_lookup. *)
(*     +destruct (eq_QName (fst a) qn) eqn:E. *)
(*      *destruct a. name_eq_tac. inversion H_lookup; subst. simpl. left. reflexivity. *)
(*      *simpl. right. apply IHc. assumption. *)
(*   -(* <- *) *)
(*     intro H_in. *)
(*     assert (H_wf : hasAllComatchfunbodies (cmfsigs (skeleton prog)) (comatchbodies prog)); *)
(*       try apply hasAllComatches;  unfold hasAllComatchfunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*     rewrite Forall_forall in H_wf2. specialize (H_wf2 (qn, cocases) H_in). *)
(*     assert (H_exists : exists argts, In (qn, argts) (cmfsigs (skeleton prog))). *)
(*     +clear H_wf1. *)
(*      induction (cmfsigs (skeleton prog)); try solve[inversion H_wf2]. *)
(*      simpl in H_wf2. destruct (eq_QName (fst a)) eqn:E. *)
(*      *destruct a. simpl in *. *)
(*       exists l. left. name_eq_tac. *)
(*      *specialize (IHc H_wf2). destruct IHc. *)
(*       exists x. simpl. right. assumption. *)
(*     +destruct H_exists. *)
(*      rewrite Forall_forall in H_wf1. specialize (H_wf1 (qn,x) H). simpl in H_wf1. *)
(*      clear H_wf2 H. *)
(*      unfold lookupGenFunctionBody. *)
(*      induction (comatchbodies prog). *)
(*      *simpl in *. contradiction. *)
(*      *destruct a. simpl in *. destruct H_in. *)
(*       **inversion H; subst. name_refl_tac. *)
(*       **destruct (eq_QName qn q) eqn:E; rewrite eq_QName_symm in E; rewrite E; try solve [apply IHc; assumption]. *)
(*         exfalso. name_eq_tac. simpl in H_wf1. inversion H_wf1. clear - H1 H. *)
(*         induction c; try contradiction. *)
(*         simpl in *. destruct a. destruct H. *)
(*         ***inversion H; subst. simpl in H1. name_refl_tac. simpl in H1. inversion H1. *)
(*         ***apply IHc; try assumption. simpl in H1. destruct (eq_QName qn q). *)
(*            inversion H1. assumption. *)
(* Qed. *)

Lemma lookup_gfun_bods_x_is_first : forall (bodies : gfun_bods) (qn : QName) (body : gfun_bod_named),
    lookup_gfun_bods_x bodies qn = Some body <->
    is_first (qn, snd body) bodies (fun x y => eq_QName (fst x) (fst y)) /\ qn = fst body.
Proof.
  intros bodies qn body.
  unfold iff. split.
  - intro Hlookup. unfold lookup_gfun_bods_x in Hlookup. split.
    induction bodies; try solve [inversion Hlookup].
    + destruct (eq_QName (fst a) qn) eqn:Eqn.
      * destruct a as [a_n a_b]. simpl in *.
        apply eq_QName_eq in Eqn. symmetry in Eqn. rewrite Eqn in *.
        rewrite eq_QName_refl in Hlookup.
        inversion Hlookup as [El]. rewrite <- El in *.
        apply is_first_head.
      * apply is_first_tail.
        -- simpl. rewrite eq_QName_symm. assumption.
        -- destruct a. simpl in *. rewrite eq_QName_symm in Hlookup; rewrite Eqn in Hlookup. apply IHbodies; try assumption.
    + induction bodies; try solve [inversion Hlookup].
      simpl in Hlookup. destruct (eq_QName qn (fst a)) eqn:E.
      * inversion Hlookup as [E_b]; rewrite E_b in *. apply eq_QName_eq; assumption.
      * apply IHbodies; assumption.
  - intro H_pair. unfold lookup_gfun_bods_x. inversion_clear H_pair as [H_is_first E].
    induction bodies as [| bds_head bds_tail]; try solve [inversion H_is_first]; simpl.
    destruct (eq_QName qn (fst bds_head)) eqn:Eqn.
    + rewrite eq_QName_eq in Eqn. inversion H_is_first.
      * destruct body; simpl in *; subst; auto.
      * simpl in *. subst.
        match goal with
        | [ H: eq_QName ?x ?y = false |- _ ] =>
          rewrite Eqn in H; rewrite eq_QName_refl in H; inversion H
        end.
    + destruct bds_head as [a_qn a_dtors]; simpl in *. apply IHbds_tail.
      inversion H_is_first; try assumption.
      match goal with
      | [ H : eq_QName ?x ?y = false |- _ ] => match goal with
                                     | [ E : x = y |- _ ] => rewrite E in H; rewrite eq_QName_refl in H; inversion H
                                     end
      end.
Qed.

Lemma lookup_gfun_bods_scoped_is_first : forall (sn : ScopedName) (p : program) (body : gfun_bod_named),
    lookup_gfun_bods_scoped p sn = Some body <->
    exists qn, qn = fst body /\
          ((is_first (qn, snd body) (program_gfun_bods_g p) (fun x y => eq_QName (fst x) (fst y)) /\ (global qn = sn)) \/
          (is_first (qn, snd body) (program_gfun_bods_l p) (fun x y => eq_QName (fst x) (fst y)) /\ (local qn = sn))).
Proof.
  intros sn p body.
  destruct sn as [qn | qn]; simpl;
  match goal with
  | [  |- ?lookup _ _ = _ _ <-> _ ] => unfold lookup
  end;
  let solve_tac :=
      split; intros;
        [> exists qn; apply lookup_gfun_bods_x_is_first in H; inversion H; split; auto
           |
           inversion H as [qn' H1]; inversion H1; inversion H2;
           match goal with
           | [ H: _ /\ _ = _ |- _ ] =>
             let E := fresh "E" in let H1 := fresh H in inversion H as [H1 E]; clear H; rename H1 into H; inversion E
           end; subst;
           apply lookup_gfun_bods_x_is_first; auto ]
  in [> solve_tac | solve_tac].
Qed.

Ltac is_first_tac :=
  match goal with
  | [ |- ?lookup ?p ?qn = Some ?body <-> is_first (?qn, snd ?body) ?bods _ /\ ?qn = fst ?body ] =>
    split; intros;
       [> let H0 := fresh
          in match lookup with
          | lookup_gfun_bods_g =>
            assert (H0: lookup_gfun_bods_scoped p (global qn) = Some body)
          | lookup_gfun_bods_l =>
            assert (H0: lookup_gfun_bods_scoped p (local qn) = Some body)
          end;
        [> unfold lookup_gfun_bods_scoped; assumption |];
        apply lookup_gfun_bods_scoped_is_first in H0; inversion H0;
        match goal with
        | [ H1: _ /\ _ |- _ ] => inversion H1
        end;
        match goal with
        | [ H3: _ \/ _ |- _ ] => inversion H3
        end;
        match goal with
        | [ H4: _ /\ ?scope _ = ?scope' _ |- _ ] =>
          inversion H4;
          match goal with
          | [ E: scope _ = scope' _ |- _ ] =>
            inversion E; subst; split; try assumption; try reflexivity
          end
        end
       | let H0 := fresh
         in match lookup with
         | lookup_gfun_bods_g =>
           assert (H0: lookup_gfun_bods_scoped p (global qn) = Some body)
         | lookup_gfun_bods_l =>
           assert (H0: lookup_gfun_bods_scoped p (local qn) = Some body)
         end;
         [> apply lookup_gfun_bods_scoped_is_first;
          exists qn; split;
          [> inversion H; assumption
          | match lookup with
            | lookup_gfun_bods_g => left
            | lookup_gfun_bods_l => right
            end;
            inversion H; split; try assumption; try reflexivity
          ]
         |];
         simpl in H0; assumption
       ]
  end.

Lemma lookup_gfun_bods_is_first_g: forall (qn: QName) (p : program) (body : gfun_bod_named),
    lookup_gfun_bods_g p qn = Some body <->
    (is_first (qn, snd body) (program_gfun_bods_g p) (fun x y => eq_QName (fst x) (fst y))) /\ qn = fst body.
Proof.
  intros qn p body; is_first_tac.
Qed.

Lemma lookup_gfun_bods_is_first_l: forall (qn: QName) (p : program) (body : gfun_bod_named),
    lookup_gfun_bods_l p qn = Some body <->
    (is_first (qn, snd body) (program_gfun_bods_l p) (fun x y => eq_QName (fst x) (fst y))) /\ qn = fst body.
Proof.
  intros qn p body; is_first_tac.
Qed.

Lemma in_gfun_bods_lookup_gfun_x : forall (qn : QName) (bodies : gfun_bods),
    (exists body, In (qn, body) bodies) ->
    exists body, lookup_gfun_bods_x bodies qn = Some body.
Proof.
  intros qn bodies H; inversion H; unfold lookup_gfun_bods_x; in_filter_tac; eauto.
Qed.

Lemma in_gfun_bods_lookup_gfun_g : forall (qn : QName) (p : program),
    (exists body, In (qn, body) (program_gfun_bods_g p)) ->
    exists body, lookup_gfun_bods_g p qn = Some body.
Proof.
  intros qn p H; unfold lookup_gfun_bods_g; apply in_gfun_bods_lookup_gfun_x; assumption.
Qed.

Lemma in_gfun_bods_lookup_gfun_l : forall (qn : QName) (p : program),
    (exists body, In (qn, body) (program_gfun_bods_l p)) ->
    exists body, lookup_gfun_bods_l p qn = Some body.
Proof.
  intros qn p H; unfold lookup_gfun_bods_l; apply in_gfun_bods_lookup_gfun_x; assumption.
Qed.

Ltac lookup_gfun_bods_scoped_in_gfun_bods_tac :=
  let H := fresh in
  let H1 := fresh in
  let H2 := fresh in
  let v := fresh "v" in
  match goal with
  | [ Hl: ?lookup ?p ?sn = Some (?qn, ?body) |- In (?qn, ?body) ?l ] =>
    apply lookup_gfun_bods_scoped_is_first in Hl;
      inversion_clear Hl as [v H];
        inversion_clear H as [Hl H1];
          inversion_clear H1 as [H|H];
          inversion_clear H as [H1 H2]; induction l; inversion H2; subst; simpl in *;
            inversion H1; subst;
              [> left; auto | right; IH_tac]
  end.

Lemma lookup_gfun_bods_scoped_in_gfun_bods_l : forall (qn : QName) (p : program) (body : gfun_bod),
    lookup_gfun_bods_scoped p (local qn) = Some (qn, body) ->
    In (qn, body) (program_gfun_bods_l p).
Proof.
  intros qn p body H; lookup_gfun_bods_scoped_in_gfun_bods_tac.
Qed.

Lemma lookup_gfun_bods_scoped_in_gfun_bods_g : forall (qn : QName) (p : program) (body : gfun_bod),
    lookup_gfun_bods_scoped p (global qn) = Some (qn, body) ->
    In (qn, body) (program_gfun_bods_g p).
Proof.
  intros qn p body H; lookup_gfun_bods_scoped_in_gfun_bods_tac.
Qed.

(* Lemma lookupGenFunctionSig_lookupGenFunctionBody : forall (prog : program) (qn : QName) (sig : list TypeName), *)
(*     lookupGenFunctionSig (skeleton prog) qn = Some sig -> *)
(*     exists cocases, lookupGenFunctionBody prog qn = Some cocases. *)
(* Proof. *)
(*   intros prog qn sig H_lookupSig. *)
(*   assert (H_wf : hasAllComatchfunbodies (cmfsigs (skeleton prog)) (comatchbodies prog)); *)
(*     try apply hasAllComatches;  unfold hasAllComatchfunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*   clear H_wf2. rewrite Forall_forall in H_wf1. *)
(*   rewrite <- In_comatchfunsig_lookupsig in H_lookupSig. *)
(*   specialize (H_wf1 (qn, sig) H_lookupSig). clear - H_wf1. simpl in *. *)
(*   unfold lookupGenFunctionBody. induction (comatchbodies prog). *)
(*   -simpl in H_wf1. inversion H_wf1. *)
(*   -simpl in *. destruct (eq_QName qn (fst a)) eqn:E; rewrite eq_QName_symm in E; rewrite E. *)
(*    +simpl in *. name_eq_tac. exists (snd a). reflexivity. *)
(*    +apply IHc. assumption. *)
(* Qed. *)

(* Lemma lookupGenFunctionBody_lookupGenFunctionSig : forall (prog : program) (qn : QName) (cocases : list (ScopedName * expr)), *)
(*   lookupGenFunctionBody prog qn = Some cocases -> *)
(*   exists sig, lookupGenFunctionSig (skeleton prog) qn = Some sig. *)
(* Proof. *)
(*   intros prog qn cocases H_lookupBody. *)
(*   assert (H_wf : hasAllComatchfunbodies (cmfsigs (skeleton prog)) (comatchbodies prog)); *)
(*     try apply hasAllComatches;  unfold hasAllComatchfunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*   clear H_wf1. rewrite Forall_forall in H_wf2. *)
(*   rewrite lookupGenFunctionBody_In in H_lookupBody. *)
(*   specialize (H_wf2 (qn, cocases) H_lookupBody). clear - H_wf2. simpl in *. *)
(*   unfold lookupGenFunctionSig. unfold option_map. induction (cmfsigs (skeleton prog)). *)
(*   -simpl in H_wf2. inversion H_wf2. *)
(*   -simpl in *. destruct (eq_QName (fst a) qn) eqn:E. *)
(*    +destruct a. name_eq_tac. simpl. name_refl_tac. exists l. reflexivity. *)
(*    +destruct a. simpl in *. rewrite E. apply IHc. assumption. *)
(* Qed. *)

(**************************************************************************************************)
(** Given the qualified name of a consumer function, return its body, i.e. a list of cocases.     *)
(**************************************************************************************************)
Definition lookup_cfun_bods_x (bodies : cfun_bods) (qn : QName) : option cfun_bod_named :=
  find (fun body => eq_QName qn (fst body)) bodies.
Definition lookup_cfun_bods_g (p : program) (qn : QName) : option cfun_bod_named :=
  lookup_cfun_bods_x (program_cfun_bods_g p) qn.
Definition lookup_cfun_bods_l (p : program) (qn : QName) : option cfun_bod_named :=
  lookup_cfun_bods_x (program_cfun_bods_l p) qn.
Definition lookup_cfun_bods_scoped (p : program) (sn : ScopedName) : option cfun_bod_named :=
  match sn with
    | local qn  => lookup_cfun_bods_l p qn
    | global qn => lookup_cfun_bods_g p qn
  end.

Lemma lookup_cfun_bods_g_scoped: forall (qn : QName) (p : program),
    lookup_cfun_bods_g p qn = lookup_cfun_bods_scoped p (global qn).
auto. Qed.

Lemma lookup_cfun_bods_l_scoped: forall (qn : QName) (p : program),
    lookup_cfun_bods_l p qn = lookup_cfun_bods_scoped p (local qn).
auto. Qed.

Lemma lookup_cfun_bods_x_fst: forall (bodies : cfun_bods) (qn : QName) (body_named : cfun_bod_named),
    lookup_cfun_bods_x bodies qn = Some body_named ->
    exists body, body_named = (qn, body).
Proof.
  intros bodies qn body_named H.
  induction bodies; try solve [inversion H].
  simpl in H.
  match goal with
  | [ H: (if ?p then _ else _) = Some _ |- _ ] =>
    destruct p eqn:E
  end.
  - inversion H. apply eq_QName_eq in E. destruct a. simpl in *. subst qn. eauto.
  - IH_tac ltac:(assumption).
Qed.

Lemma lookup_cfun_bods_g_fst: forall (p : program) (qn : QName) (body_named : cfun_bod_named),
    lookup_cfun_bods_g p qn = Some body_named ->
    exists body, body_named = (qn, body).
Proof.
  intros p qn body_named H.
  unfold lookup_cfun_bods_g in H.
  apply lookup_cfun_bods_x_fst in H; assumption.
Qed.

Lemma lookup_cfun_bods_l_fst: forall (p : program) (qn : QName) (body_named : cfun_bod_named),
    lookup_cfun_bods_l p qn = Some body_named ->
    exists body, body_named = (qn, body).
Proof.
  intros p qn body_named H.
  unfold lookup_cfun_bods_l in H.
  apply lookup_cfun_bods_x_fst in H; assumption.
Qed.

Lemma lookup_cfun_bods_scoped_fst: forall (sn : ScopedName) (p : program) (body_named : cfun_bod_named),
    lookup_cfun_bods_scoped p sn = Some body_named ->
    exists body, body_named = (unscope sn, body).
Proof.
  intros sn p body_named H.
  destruct sn; unfold lookup_cfun_bods_scoped in H.
  - apply lookup_cfun_bods_l_fst in H; assumption.
  - apply lookup_cfun_bods_g_fst in H; assumption.
Qed.

(* Lemma lookupConsFunctionBody_In : forall (prog : program) (qn : QName) (ctors : list (ScopedName * expr)), *)
(*     lookupConsFunctionBody prog qn = Some ctors <-> *)
(*     In (qn, ctors) (matchbodies prog). *)
(* Proof. *)
(*   intros prog n e. split. *)
(*   -(* -> *) *)
(*     intro H_lookup. *)
(*     unfold lookupConsFunctionBody in H_lookup. *)
(*     induction (matchbodies prog). *)
(*     *inversion H_lookup. *)
(*     *destruct (eq_QName (fst a) n) eqn:E. *)
(*      **destruct a. simpl in E. apply eq_QName_eq in E. inversion H_lookup. subst. *)
(*        simpl. left. reflexivity. *)
(*      **simpl. right. apply IHm. assumption. *)
(*   -(* <- *) *)
(*     intro H_in. *)
(*      assert (H_wf : hasAllMatchfunbodies (mfsigs (skeleton prog)) (matchbodies prog)); *)
(*       try apply hasAllMatches;  unfold hasAllMatchfunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*      rewrite Forall_forall in H_wf2. specialize (H_wf2 (n, e) H_in). *)
(*      assert (H_exists : exists argts rtype, In (n, argts, rtype) (mfsigs (skeleton prog))). *)
(*     +clear H_wf1. *)
(*      induction (mfsigs (skeleton prog)); try (inversion H_wf2). *)
(*      simpl in H_wf2. destruct (eq_QName (fst (fst a)) n) eqn:E. *)
(*      *destruct a as [[a0 a1] a2]. simpl in *. *)
(*       exists a1. exists a2. left. name_eq_tac. *)
(*      *specialize (IHm H_wf2). destruct IHm. destruct H. *)
(*       exists x. exists x0. simpl. right. assumption. *)
(*     +destruct H_exists. destruct H. *)
(*      rewrite Forall_forall in H_wf1. specialize (H_wf1 (n,x,x0) H). simpl in H_wf1. *)
(*      clear H_wf2 H. *)
(*      unfold lookupConsFunctionBody. *)
(*      induction (matchbodies prog). *)
(*      *simpl in *. contradiction. *)
(*      *destruct a. simpl in *. destruct H_in. *)
(*       **inversion H; subst. name_refl_tac. *)
(*       **destruct (eq_QName n q) eqn:E; rewrite eq_QName_symm in E; rewrite E; try solve [apply IHm; assumption]. *)
(*         exfalso. name_eq_tac. simpl in H_wf1. inversion H_wf1. clear - H1 H. *)
(*         induction m; try contradiction. *)
(*         simpl in *. destruct a. destruct H. *)
(*         ***inversion H; subst. simpl in H1. name_refl_tac. simpl in H1. inversion H1. *)
(*         ***apply IHm; try assumption. simpl in H1. destruct (eq_QName n q). *)
(*            inversion H1. assumption. *)
(* Qed. *)

(* Lemma lookupConsFunctionSig_lookupConsFunctionBody : forall (prog : program) (qn : QName) (sig : list TypeName * TypeName), *)
(*     lookupConsFunctionSig (skeleton prog) qn = Some sig -> *)
(*     exists cases, lookupConsFunctionBody prog qn = Some cases. *)
(* Proof. *)
(*   intros prog qn sig H_lookupSig. *)
(*   assert (H_wf : hasAllMatchfunbodies (mfsigs (skeleton prog)) (matchbodies prog)); *)
(*     try apply hasAllMatches;  unfold hasAllMatchfunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*   clear H_wf2. rewrite Forall_forall in H_wf1. destruct sig. *)
(*   rewrite <- In_matchfunsig_lookupsig in H_lookupSig. *)
(*   specialize (H_wf1 (qn, l, t) H_lookupSig). clear - H_wf1. simpl in *. *)
(*   unfold lookupConsFunctionBody. induction (matchbodies prog). *)
(*   -simpl in H_wf1. inversion H_wf1. *)
(*   -simpl in *. destruct (eq_QName qn (fst a)) eqn:E; rewrite eq_QName_symm in E; rewrite E. *)
(*    +exists (snd a). reflexivity. *)
(*    +apply IHm. assumption. *)
(* Qed. *)

(* Lemma lookupConsFunctionBody_lookupConsFunctionSig : forall (prog : program) (qn : QName) (cases : list (ScopedName * expr)), *)
(*     lookupConsFunctionBody prog qn = Some cases -> *)
(*     exists sig, lookupConsFunctionSig (skeleton prog) qn = Some sig. *)
(* Proof. *)
(*   intros prog qn cases H_lookupBody. *)
(*   assert (H_wf : hasAllMatchfunbodies (mfsigs (skeleton prog)) (matchbodies prog)); *)
(*     try apply hasAllMatches;  unfold hasAllMatchfunbodies in H_wf; destruct H_wf as [H_wf1 H_wf2]. *)
(*   clear H_wf1. rewrite Forall_forall in H_wf2. *)
(*   rewrite lookupConsFunctionBody_In in H_lookupBody. *)
(*   specialize (H_wf2 (qn, cases) H_lookupBody). clear - H_wf2. simpl in *. *)
(*   unfold lookupConsFunctionSig. unfold option_map. induction (mfsigs (skeleton prog)). *)
(*   -simpl in H_wf2. inversion H_wf2. *)
(*   -simpl in *. destruct (eq_QName (fst (fst a)) qn) eqn:E. *)
(*    +name_eq_tac.  destruct a as [[a0 a1] a2]. simpl. name_refl_tac. exists (a1, a2). reflexivity. *)
(*    +destruct a as [[a0 a1] a2]. simpl in *. rewrite E. apply IHm. assumption. *)
(* Qed. *)

Lemma lookup_cfun_bods_x_is_first : forall (bodies : cfun_bods) (qn : QName) (body : cfun_bod_named),
    lookup_cfun_bods_x bodies qn = Some body <->
    is_first (qn, snd body) bodies (fun x y => eq_QName (fst x) (fst y)) /\ qn = fst body.
Proof.
  intros bodies qn body.
  unfold iff. split.
  - intro Hlookup. unfold lookup_cfun_bods_x in Hlookup. split.
    induction bodies; try solve [inversion Hlookup].
    + destruct (eq_QName (fst a) qn) eqn:Eqn.
      * destruct a as [a_n a_b]. simpl in *.
        apply eq_QName_eq in Eqn. symmetry in Eqn. rewrite Eqn in *.
        rewrite eq_QName_refl in Hlookup.
        inversion Hlookup as [El]. rewrite <- El in *.
        apply is_first_head.
      * apply is_first_tail.
        -- simpl. rewrite eq_QName_symm. assumption.
        -- destruct a. simpl in *. rewrite eq_QName_symm in Hlookup; rewrite Eqn in Hlookup. apply IHbodies; try assumption.
    + induction bodies; try solve [inversion Hlookup].
      simpl in Hlookup. destruct (eq_QName qn (fst a)) eqn:E.
      * inversion Hlookup as [E_b]; rewrite E_b in *. apply eq_QName_eq; assumption.
      * apply IHbodies; assumption.
  - intro H_pair. unfold lookup_cfun_bods_x. inversion_clear H_pair as [H_is_first E].
    induction bodies as [| bds_head bds_tail]; try solve [inversion H_is_first]; simpl.
    destruct (eq_QName qn (fst bds_head)) eqn:Eqn.
    + rewrite eq_QName_eq in Eqn. inversion H_is_first.
      * destruct body; simpl in *; subst; auto.
      * simpl in *. subst.
        match goal with
        | [ H: eq_QName ?x ?y = false |- _ ] =>
          rewrite Eqn in H; rewrite eq_QName_refl in H; inversion H
        end.
    + destruct bds_head as [a_qn a_dtors]; simpl in *. apply IHbds_tail.
      inversion H_is_first; try assumption.
      match goal with
      | [ H : eq_QName ?x ?y = false |- _ ] => match goal with
                                     | [ E : x = y |- _ ] => rewrite E in H; rewrite eq_QName_refl in H; inversion H
                                     end
      end.
Qed.

Lemma lookup_cfun_bods_scoped_is_first : forall (sn : ScopedName) (p : program) (body : cfun_bod_named),
    lookup_cfun_bods_scoped p sn = Some body <->
    exists qn, qn = fst body /\
          ((is_first (qn, snd body) (program_cfun_bods_g p) (fun x y => eq_QName (fst x) (fst y)) /\ (global qn = sn)) \/
          (is_first (qn, snd body) (program_cfun_bods_l p) (fun x y => eq_QName (fst x) (fst y)) /\ (local qn = sn))).
Proof.
  intros sn p body.
  destruct sn as [qn | qn]; simpl;
  match goal with
  | [  |- ?lookup _ _ = _ _ <-> _ ] => unfold lookup
  end;
  let solve_tac :=
      split; intros;
        [> exists qn; apply lookup_cfun_bods_x_is_first in H; inversion H; split; auto
           |
           inversion H as [qn' H1]; inversion H1; inversion H2;
           match goal with
           | [ H: _ /\ _ = _ |- _ ] =>
             let E := fresh "E" in let H1 := fresh H in inversion H as [H1 E]; clear H; rename H1 into H; inversion E
           end; subst;
           apply lookup_cfun_bods_x_is_first; auto ]
  in [> solve_tac | solve_tac].
Qed.


Lemma in_cfun_bods_lookup_cfun_x : forall (qn : QName) (bodies : cfun_bods),
    (exists body, In (qn, body) bodies) ->
    exists body, lookup_cfun_bods_x bodies qn = Some body.
Proof.
  intros qn bodies H; inversion H; unfold lookup_cfun_bods_x; in_filter_tac; eauto.
Qed.

Lemma in_cfun_bods_lookup_cfun_g : forall (qn : QName) (p : program),
    (exists body, In (qn, body) (program_cfun_bods_g p)) ->
    exists body, lookup_cfun_bods_g p qn = Some body.
Proof.
  intros qn p H; unfold lookup_cfun_bods_g; apply in_cfun_bods_lookup_cfun_x; assumption.
Qed.

Lemma in_cfun_bods_lookup_cfun_l : forall (qn : QName) (p : program),
    (exists body, In (qn, body) (program_cfun_bods_l p)) ->
    exists body, lookup_cfun_bods_l p qn = Some body.
Proof.
  intros qn p H; unfold lookup_cfun_bods_l; apply in_cfun_bods_lookup_cfun_x; assumption.
Qed.

Ltac lookup_cfun_bods_scoped_in_cfun_bods_tac :=
  let H := fresh in
  let H1 := fresh in
  let H2 := fresh in
  let v := fresh "v" in
  match goal with
  | [ Hl: ?lookup ?p ?sn = Some (?qn, ?body) |- In (?qn, ?body) ?l ] =>
    apply lookup_cfun_bods_scoped_is_first in Hl;
      inversion_clear Hl as [v H];
        inversion_clear H as [Hl H1];
          inversion_clear H1 as [H|H];
          inversion_clear H as [H1 H2]; induction l; inversion H2; subst; simpl in *;
            inversion H1; subst;
              [> left; auto | right; IH_tac]
  end.

Lemma lookup_cfun_bods_scoped_in_cfun_bods_l : forall (qn : QName) (p : program) (body : cfun_bod),
    lookup_cfun_bods_scoped p (local qn) = Some (qn, body) ->
    In (qn, body) (program_cfun_bods_l p).
Proof.
  intros qn p body H; lookup_cfun_bods_scoped_in_cfun_bods_tac.
Qed.

Lemma lookup_cfun_bods_scoped_in_cfun_bods_g : forall (qn : QName) (p : program) (body : cfun_bod),
    lookup_cfun_bods_scoped p (global qn) = Some (qn, body) ->
    In (qn, body) (program_cfun_bods_g p).
Proof.
  intros qn p body H; lookup_cfun_bods_scoped_in_cfun_bods_tac.
Qed.


Definition lookup_case (cs : list (ScopedName * expr))(sn : ScopedName) : option ( ScopedName * expr) :=
  find (fun case => eq_ScopedName sn (fst case)) cs.

Definition lookup_cocase (ccs : list (ScopedName * expr)) (sn : ScopedName) : option (ScopedName * expr) :=
  find (fun cocase => eq_ScopedName sn (fst cocase)) ccs.

Lemma lookup_case_In : forall (cs : list (ScopedName * expr))(sn : ScopedName)(ctor : ScopedName * expr),
    lookup_case cs sn = Some ctor ->
    In ctor cs /\ sn = (fst ctor).
Proof.
  intros cs sn ctor H. unfold lookup_case in H. induction cs.
  - inversion H.
  - simpl in H. destruct (eq_ScopedName sn (fst a)) eqn:E.
    + split.
      * simpl. left. inversion H. reflexivity.
      * inversion H; subst. apply eq_ScopedName_eq in E. assumption.
    + split.
      * simpl. right. apply IHcs. assumption.
      * apply IHcs. assumption.
Qed.

Lemma lookup_cocase_In : forall (ccs : list (ScopedName * expr)) (sn : ScopedName) (dtor : ScopedName * expr),
    lookup_cocase ccs sn = Some dtor ->
    In dtor ccs /\ sn = (fst dtor).
Proof.
  intros ccs sn dtor H. unfold lookup_cocase. induction ccs.
  - inversion H.
  - simpl in H. destruct (eq_ScopedName sn (fst a)) eqn:E.
    + split.
      * simpl. left. inversion H. reflexivity.
      * inversion H; subst. apply eq_ScopedName_eq in E. assumption.
    + split.
      * simpl. right. apply IHccs. assumption.
      * apply IHccs. assumption.
Qed.

Lemma lookup_case_is_first : forall (sn : ScopedName) (body : expr) (cases : list (ScopedName * expr)),
    lookup_case cases sn = Some (sn, body) <->
    is_first (sn, body) cases (fun x y => eq_ScopedName (fst x) (fst y)).
Proof.
  intros sn body cases.
  unfold iff. split.
  -intro Hl.
   induction cases.
   +simpl in Hl. discriminate Hl.
   +simpl in Hl. destruct (eq_ScopedName sn (fst a)) eqn:Esn.
    *inversion Hl. apply is_first_head.
    *apply is_first_tail.
     --apply lookup_case_In in Hl. apply proj2 in Hl. rewrite Hl in Esn. assumption.
     --apply IHcases. assumption.
  -intro Hfirst.
   induction cases; try solve [inversion Hfirst].
   destruct a as [sn_a body_a]. simpl.
   destruct (eq_ScopedName sn sn_a) eqn:Esn.
   +inversion Hfirst; try reflexivity.
    simpl in H2. rewrite H2 in Esn. discriminate Esn.
   +apply IHcases.
    inversion Hfirst; try assumption. subst. rewrite eq_ScopedName_refl in Esn. discriminate Esn.
Qed.


Lemma lookup_cocase_is_first : forall (sn : ScopedName)(body : expr) (cocases : list (ScopedName * expr)),
    lookup_cocase cocases sn = Some (sn, body) <->
    is_first (sn, body) cocases (fun x y => eq_ScopedName (fst x) (fst y)).
Proof.
  intros sn body cocases.
  unfold iff. split.
  -intro Hl.
   induction cocases.
   +simpl in Hl. discriminate Hl.
   +simpl in Hl. destruct (eq_ScopedName sn (fst a)) eqn:Esn.
    *inversion Hl. apply is_first_head.
    *apply is_first_tail.
     --apply lookup_case_In in Hl. apply proj2 in Hl. rewrite Hl in Esn. assumption.
     --apply IHcocases. assumption.
  -intro Hfirst.
   induction cocases; try solve [inversion Hfirst].
   destruct a as [sn_a  body_a]. simpl.
   destruct (eq_ScopedName sn sn_a) eqn:Esn.
   +inversion Hfirst; try reflexivity.
    simpl in H2. rewrite H2 in Esn. discriminate Esn.
   +apply IHcocases.
    inversion Hfirst; try assumption. subst. rewrite eq_ScopedName_refl in Esn. discriminate Esn.
Qed.

Lemma in_cocases_lookup_cocase : forall (sn : ScopedName) (ccs : list (ScopedName * expr)),
    (exists e, In (sn, e) ccs) ->
    exists cocase, lookup_cocase ccs sn = Some cocase.
Proof.
  intros sn ccs H. inversion H. unfold lookup_cocase. in_filter_tac; eauto.
Qed.

Lemma in_cases_lookup_case : forall (sn : ScopedName) (ccs : list (ScopedName * expr)),
    (exists e, In (sn, e) ccs) ->
    exists case, lookup_case ccs sn = Some case.
Proof.
  intros sn ccs H. inversion H. unfold lookup_case. in_filter_tac; eauto.
Qed.

Lemma lookup_comatch_cocase_succeeds : forall (p : program) (sn : ScopedName) (qn : QName) (ccs : list (ScopedName * expr)),
    (exists ctx bs dtor_args tn, (program_skeleton p / ctx |- (E_DestrCall sn (E_CoMatch qn bs ccs) dtor_args) : tn)) ->
    exists cocase, lookup_cocase ccs sn = Some cocase.
Proof.
  intros p sn qn ccs H.
  inversion_clear H as [ctx [bs [dtor_args [tn H']]]].
  inversion_clear H'.
  unfold lookup_cocase.
  inversion H0; subst. clear H0.
  apply in_dtors_lookup_dtors' in H. inversion_clear H as [dtors [H_lookup H_in]]; simpl in H_lookup.
  rewrite H5 in H10.
  rewrite H10 in H_lookup. inversion H_lookup. subst dtors; clear H_lookup H10.
  gen_induction dtorlist ccs.
  - inversion H12; subst.
    symmetry in H2; apply map_eq_nil in H2; subst dtorlist.
    inversion H_in.
  - simpl. match_destruct_tac; eauto.
    destruct dtorlist; try solve [inversion H12].
    inversion_clear H_in.
    + inversion_clear H12. subst p0; simpl in *.
      inversion H11; subst. destruct a. subst s.
      simpl in E_match. name_refl_contradiction_tac.
    + apply IHccs with (dtorlist := dtorlist); auto; try Forall_tail_tac.
      inversion H12; auto.
Qed.

Lemma lookup_gfun_cocase_succeeds : forall (p : program) (sn_gfun sn_dtor : ScopedName) (ccs : gfun_bod_named),
    lookup_gfun_bods_scoped p sn_gfun = Some ccs ->
    (exists ctx gfun_args dtor_args tn, (program_skeleton p / ctx |- (E_DestrCall sn_dtor (E_GenFunCall sn_gfun gfun_args) dtor_args) : tn)) ->
    exists cocase, lookup_cocase (snd ccs) sn_dtor = Some cocase.
Proof.
  intros p sn_gfun sn_dtor ccs H_lookup H_t';
  let rec destruct_tc := inversion_clear H_t' as [ctx [gfun_args [dtor_args [tn H_t]]]];
                           inversion H_t; subst; clear H_t
  with
    pose_lookup_dtor := match goal with
                        | [ H: In _ (skeleton_dtors _) |- _ ] =>
                          let H' := fresh H_lookup_dtors in pose proof H as H';
                                                              apply in_dtors_lookup_dtors' in H'
                        end
  with
    in_dtors_to_in_cdts := match goal with
                           | [ H: In _ (skeleton_dtors _) |- _ ] => apply In_dtors_in_cdts in H
                           end
  with

    housekeeping_scoped := match goal with
                       | [ H : ?lookup_X ?p ?qn = Some ?ccs |- _ ] =>
                         unfold lookup_X in H;
                         let H_tc := fresh "H_tc"
                         in match lookup_X with
                            | lookup_gfun_bods_g => pose proof (program_gfun_bods_typecheck_g p) as H_tc
                            | lookup_gfun_bods_l => pose proof (program_gfun_bods_typecheck_l p) as H_tc
                            end;
                            match type of H with
                            | ?l ?bods qn = Some ccs =>
                                unfold l in H;
                                match type of H with
                                | find _ ?bods = Some ccs =>
                                    match type of H_tc with
                                    | ?tc (program_skeleton p) bods =>
                                    unfold tc in H_tc
                                    end
                                end
                            end
                       end
   with
     invert_tc_gfun := match goal with
                       | [ H: program_skeleton p / _ |- (E_GenFunCall _ _) : _ |- _ ] =>
                         inversion H; subst;
                           clear H
                       end
   with
     induction_on_gfun_bods :=
                           match goal with
                           | [ H: context [program_gfun_bods_l p] |- _ ] =>
                             induction (program_gfun_bods_l p) as [|bod bods]
                           | [ H: context [program_gfun_bods_g p] |- _ ] =>
                             induction (program_gfun_bods_g p) as [|bod bods]
                           end;
                             try solve [inversion H_lookup]
   with
     destruct_eq_QName_in_lookup :=
         match goal with
         | [ H: find _ _ = Some _ |- _ ] =>
                 simpl in H;
                 match goal with
                 | [ H1: context [eq_QName ?l ?r] |- _ ] =>
                         match H1 with
                         | H => let E := fresh "E" in destruct (eq_QName l r) eqn:E
                         end
                 end
         end
   with
      subst_qn_fst_bod := name_eq_rewrite_tac; simpl in E; subst qn
   with
      destr_subst_ccs :=
                destruct ccs as [ccs_n ccs_b]; simpl in *; inversion H_lookup; subst; simpl in *
   with
      invert_tc_bodies :=
                match goal with
                | [ Ht: Forall ?P ((_, _) :: ?bods) |- _ ] => inversion Ht
                end
   with
      invert_tc_fst :=
                match goal with
                | [ H1: exists q args, _ /\ _ |- _ ] =>
                        simpl in H1; inversion H1 as [qn' [args H_ccs]]; inversion H_ccs as [H_ccs_sig H_ccs_tc]; subst x l; clear H_ccs
                end
   with
      assert_E :=
                match goal with
                | [ H: In _ (skeleton_gfun_sigs_l _) |- _ ] =>
                        apply In_gfun_sig_lookup_gfun_sig_l in H; rewrite H in H_ccs_sig; inversion H_ccs_sig; auto
                | [ H: In _ (skeleton_gfun_sigs_g _) |- _ ] =>
                        apply In_gfun_sig_lookup_gfun_sig_g in H; rewrite H in H_ccs_sig; inversion H_ccs_sig; auto
                end
   with
      assert_H_in_dtorlist :=
                    match goal with
                    | [ H: exists x, lookup_dtors _ _ = Some x /\ _ |- _ ] =>
                            let Dtors := fresh dtors in
                            let H' := fresh H in
                            inversion H as [Dtors H'];
                            let H_lookup := fresh H_lookup_dtors in
                            let H_in := fresh H_in_dtors in
                            inversion H' as [H_lookup H_in]; clear H';
                            match goal with
                            | [ H_l: lookup_dtors _ ?name = Some ?dtors' |- _ ] =>
                                    match H_l with
                                    | H_lookup => fail 1
                                    | _ =>
                                            match type of H_lookup with
                                            | lookup_dtors _ ?name' = _ =>
                                                    subst_in name name' H_l;
                                                    rewrite H_l in H_lookup; inversion H_lookup
                                            end
                                    end
                            end
                    end; assumption
   with
      dtorlist_induction to_gen := generalize dependent to_gen; induction dtorlist as [|dtor dtors_rest];
                      intros; try solve [inversion H_in_dtorlist]
   with
     clear_unnecessary :=
                      match goal with
                         | [ H: Forall _ (combine _ ?dtorlist) |- _ ] =>
                           match goal with
                           | [ H1: _ /// _ |||- _ ::: _ |- _ ] =>
                             match goal with
                             | [ H2: In _ dtorlist |- _ ] =>
                               clear - H H1 H2
                             end
                           end
                         end
   with
     destruct_ccs_b := destruct ccs_b as [| ccs ccss];
                         try solve [match goal with
                                    | [ H: (_ /// _ |||- _ ::: _) |- _ ] => inversion H end]
   with
     invert_list_typing :=
                        match goal with
                        | [ H: Forall _ (combine (_ :: _) (_ :: _)) |- _ ] => inversion H; subst
                        end
   with
     destruct_tuples := destruct ccs as [ccs_sn ccs_e];
                          destruct dtor as [[dtor_sn dtor_ts] dtor_t]; subst
   with
     destruct_In_dtorlist :=
                          match goal with
                          | [ H: In _ (_ :: _) |- _ ] => inversion H
                          end
   with
     in_dtorlist_eq_case :=
                            match goal with
                            | [ E: ?x = ?y |- _ ] => inversion E
                            end; eexists; left; eauto; idtac (* for some reason idtac is necessary here *)
   with
     specialize_IH := match goal with
                      | [ H: context c [forall ccs, ?b] |- _ ] =>
                        match b with
                        | context [In _ _] =>
                          match goal with
                          | [ _: _ /// _ |||- map _ (_ :: ?ccss) ::: _ |- _ ] =>
                            specialize H with (ccs_b := ccss)
                          end
                        end
                      end



   with
     solve_branch := invert_tc_gfun; induction_on_gfun_bods; destruct_eq_QName_in_lookup;
            [> subst_qn_fst_bod; destr_subst_ccs; invert_tc_bodies; invert_tc_fst;
                assert (E : (ccs_n, argts) = (qn', args)); [> assert_E | ];
                destruct E; inversion H_ccs_tc; subst;
                assert (H_in_dtorlist : In (sn_dtor, dargs, tn) dtorlist); [> assert_H_in_dtorlist | ];
                clear_unnecessary;
                let to_generalize := match goal with
                                     | [ gen: gfun_bod |- _ ] => gen
                                     end in
                dtorlist_induction to_generalize; destruct_ccs_b;
                invert_list_typing; destruct_tuples;
                destruct_In_dtorlist;
                    [> in_dtorlist_eq_case
                    | specialize_IH;
                      match goal with
                      | [ H: _ /// _ |||- _ ::: _ |- _ ] =>
                        apply In_right_over_exists; IH_tac ltac:(inversion H; subst; assumption)
                    end]
            | IH_tac ltac:(try Forall_tail_tac) ]
   in destruct_tc; pose_lookup_dtor; in_dtors_to_in_cdts;
      apply in_cocases_lookup_cocase;
      destruct sn_gfun as [qn | qn]; simpl in H_lookup; housekeeping_scoped;
        [> solve_branch | solve_branch ].
Qed.

Lemma lookup_cfun_case_succeeds : forall (p : program) (sn_cfun sn_ctor : ScopedName) (ccs : cfun_bod_named),
    lookup_cfun_bods_scoped p sn_cfun = Some ccs ->
    (exists ctx cfun_args ctor_args tn, (program_skeleton p / ctx |- (E_ConsFunCall sn_cfun (E_Constr sn_ctor ctor_args) cfun_args) : tn)) ->
    exists case, lookup_case (snd ccs) sn_ctor = Some case.
Proof.
  intros p sn_cfun sn_ctor ccs H_lookup H_t';
  let rec destruct_tc := inversion_clear H_t' as [ctx [cfun_args [ctor_args [tn H_t]]]];
                           inversion H_t; subst; clear H_t
   with
     invert_tc_constr := match goal with
                       | [ H: program_skeleton p / _ |- (E_Constr _ _) : _ |- _ ] =>
                         inversion H; subst;
                           clear H
                       end
  with
    pose_lookup_ctor := match goal with
                        | [ H: In _ (skeleton_ctors _) |- _ ] =>
                          let H' := fresh H_lookup_ctors in pose proof H as H';
                                                              apply in_ctors_lookup_ctors' in H'
                        end
  with
    in_ctors_to_in_dts := match goal with
                           | [ H: In _ (skeleton_ctors _) |- _ ] => apply In_ctors_in_dts in H
                           end
  with

    housekeeping_scoped := match goal with
                       | [ H : ?lookup_X ?p ?qn = Some ?ccs |- _ ] =>
                         unfold lookup_X in H;
                         let H_tc := fresh "H_tc"
                         in match lookup_X with
                            | lookup_cfun_bods_g => pose proof (program_cfun_bods_typecheck_g p) as H_tc
                            | lookup_cfun_bods_l => pose proof (program_cfun_bods_typecheck_l p) as H_tc
                            end;
                            match type of H with
                            | ?l ?bods qn = Some ccs =>
                                unfold l in H;
                                match type of H with
                                | find _ ?bods = Some ccs =>
                                    match type of H_tc with
                                    | ?tc (program_skeleton p) bods =>
                                    unfold tc in H_tc
                                    end
                                end
                            end
                       end
   with
     induction_on_cfun_bods :=
                           match goal with
                           | [ H: context [program_cfun_bods_l p] |- _ ] =>
                             induction (program_cfun_bods_l p) as [|bod bods]
                           | [ H: context [program_cfun_bods_g p] |- _ ] =>
                             induction (program_cfun_bods_g p) as [|bod bods]
                           end;
                             try solve [inversion H_lookup]
   with
     destruct_eq_QName_in_lookup :=
         match goal with
         | [ H: find _ _ = Some _ |- _ ] =>
                 simpl in H;
                 match goal with
                 | [ H1: context [eq_QName ?l ?r] |- _ ] =>
                         match H1 with
                         | H => let E := fresh "E" in destruct (eq_QName l r) eqn:E
                         end
                 end
         end
   with
      subst_qn_fst_bod := name_eq_rewrite_tac; simpl in E; subst qn
   with
      destr_subst_ccs :=
                destruct ccs as [ccs_n ccs_b]; simpl in *; inversion H_lookup; subst; simpl in *
   with
      invert_tc_bodies :=
                match goal with
                | [ Ht: Forall ?P ((_, _) :: ?bods) |- _ ] => inversion Ht
                end
   with
      invert_tc_fst :=
                match goal with
                | [ H1: exists q args t, _ /\ _ |- _ ] =>
                        simpl in H1; inversion H1 as [qn' [args [t H_ccs]]]; inversion H_ccs as [H_ccs_sig H_ccs_tc]; subst x l; clear H_ccs
                end
   with
      assert_E :=
                match goal with
                | [ H: In _ (skeleton_cfun_sigs_l _) |- _ ] =>
                        apply In_cfun_sig_lookup_cfun_sig_l in H; rewrite H in H_ccs_sig; inversion H_ccs_sig; auto
                | [ H: In _ (skeleton_cfun_sigs_g _) |- _ ] =>
                        apply In_cfun_sig_lookup_cfun_sig_g in H; rewrite H in H_ccs_sig; inversion H_ccs_sig; auto
                end
   with
      assert_H_in_ctorlist :=
                    match goal with
                    | [ H: exists x, lookup_ctors _ _ = Some x /\ _ |- _ ] =>
                            let Ctors := fresh ctors in
                            let H' := fresh H in
                            inversion H as [Ctors H'];
                            let H_lookup := fresh H_lookup_ctors in
                            let H_in := fresh H_in_ctors in
                            inversion H' as [H_lookup H_in]; clear H';
                            match goal with
                            | [ H_l: lookup_ctors _ ?name = Some ?ctors' |- _ ] =>
                                    match H_l with
                                    | H_lookup => fail 1
                                    | _ =>
                                            match type of H_lookup with
                                            | lookup_ctors _ ?name' = _ =>
                                                    subst_in name name' H_l;
                                                    rewrite H_l in H_lookup; inversion H_lookup
                                            end
                                    end
                            end
                    end; assumption
   with
      ctorlist_induction to_gen := generalize dependent to_gen; induction ctorlist as [|ctor ctors_rest];
                      intros; try solve [inversion H_in_ctorlist]
   with
     clear_unnecessary :=
                      match goal with
                         | [ H: Forall _ (combine _ ?ctorlist) |- _ ] =>
                           match goal with
                           | [ H1: _ /// _ |||- _ ::: _ |- _ ] =>
                             match goal with
                             | [ H2: In _ ctorlist |- _ ] =>
                               clear - H H1 H2
                             end
                           end
                         end
   with
     destruct_ccs_b := destruct ccs_b as [| ccs ccss];
                         try solve [match goal with
                                    | [ H: (_ /// _ |||- _ ::: _) |- _ ] => inversion H end]
   with
     invert_list_typing :=
                        match goal with
                        | [ H: Forall _ (combine (_ :: _) (_ :: _)) |- _ ] => inversion H; subst
                        end
   with
     destruct_tuples := destruct ccs as [ccs_sn ccs_e];
                          destruct ctor as [ctor_sn ctor_ts]; subst
   with
     destruct_In_ctorlist :=
                          match goal with
                          | [ H: In _ (_ :: _) |- _ ] => inversion H
                          end
   with
     in_ctorlist_eq_case :=
                            match goal with
                            | [ E: ?x = ?y |- _ ] => inversion E
                            end; eexists; left; eauto; idtac (* for some reason idtac is necessary here *)
   with
     specialize_IH := match goal with
                      | [ H: context c [forall ccs, ?b] |- _ ] =>
                        match b with
                        | context [In _ _] =>
                          match goal with
                          | [ _: _ /// _ |||- map _ (_ :: ?ccss) ::: _ |- _ ] =>
                            specialize H with (ccs_b := ccss)
                          end
                        end
                      end



   with
     solve_branch := invert_tc_constr; pose_lookup_ctor; in_ctors_to_in_dts;
            induction_on_cfun_bods; destruct_eq_QName_in_lookup;
            [> subst_qn_fst_bod; destr_subst_ccs; invert_tc_bodies; invert_tc_fst;
                assert (E : (ccs_n, argts) = (qn', args)); [> assert_E | ];
                destruct E; inversion H_ccs_tc; subst ;
                assert (H_in_ctorlist : In (sn_ctor, cargs) ctorlist) ; [> assert_H_in_ctorlist | ];
                clear_unnecessary;
                let to_generalize := match goal with
                                     | [ gen: cfun_bod |- _ ] => gen
                                     end in
                ctorlist_induction to_generalize; destruct_ccs_b;
                invert_list_typing; destruct_tuples;
                destruct_In_ctorlist;
                    [> in_ctorlist_eq_case
                    | specialize_IH;
                      match goal with
                      | [ H: _ /// _ |||- _ ::: _ |- _ ] =>
                        apply In_right_over_exists; IH_tac ltac:(inversion H; subst; assumption)
                    end]
            | IH_tac ltac:(try Forall_tail_tac) ]
   in destruct_tc;
      apply in_cases_lookup_case; simpl in H_lookup; housekeeping_scoped;
        [> solve_branch | solve_branch ].
Qed.

Opaque lookup_case lookup_cocase.

Lemma cfun_bods_unique_l : forall (p : program),
    unique (map fst (program_cfun_bods_l p)).
Proof.
  intros p;
  pose proof (program_has_all_cfun_bods_l p) as H;
  unfold has_all_cfun_bods in H;
  pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as H_unique;
  unfold cfun_sigs_names_unique in H_unique;
  rewrite <- H; assumption.
Qed.

Lemma cfun_bods_unique_g : forall (p : program),
    unique (map fst (program_cfun_bods_g p)).
Proof.
  intro p;
  pose proof (program_has_all_cfun_bods_g p) as H;
  unfold has_all_cfun_bods in H;
  pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as H_unique;
  unfold cfun_sigs_names_unique in H_unique;
  rewrite <- H; assumption.
Qed.

Lemma gfun_bods_unique_l : forall (p : program),
    unique (map fst (program_gfun_bods_l p)).
Proof.
  intro p;
  pose proof (program_has_all_gfun_bods_l p) as H;
  unfold has_all_gfun_bods in H;
  pose proof (skeleton_gfun_sigs_names_unique_l (program_skeleton p)) as H_unique;
  unfold gfun_sigs_names_unique in H_unique;
  rewrite <- H; assumption.
Qed.

Lemma gfun_bods_unique_g : forall (p : program),
    unique (map fst (program_gfun_bods_g p)).
Proof.
  intro p;
  pose proof (program_has_all_gfun_bods_g p) as H;
  unfold has_all_gfun_bods in H;
  pose proof (skeleton_gfun_sigs_names_unique_g (program_skeleton p)) as H_unique;
  unfold gfun_sigs_names_unique in H_unique;
  rewrite <- H; assumption.
Qed.

Lemma fun_bods_unique : forall (p : program),
    unique (map fst (program_fun_bods p)).
Proof.
  intro p;
  pose proof (program_has_all_fun_bods p) as H;
  unfold has_all_fun_bods in H;
  pose proof (skeleton_fun_sigs_names_unique (program_skeleton p)) as H_unique;
  unfold fun_sigs_names_unique in H_unique;
  rewrite <- H; assumption.
Qed.


Global Opaque lookup_cfun_bods_g lookup_cfun_bods_l lookup_cfun_bods_x lookup_cfun_bods_scoped.
Global Opaque lookup_gfun_bods_g lookup_gfun_bods_l lookup_gfun_bods_x lookup_gfun_bods_scoped.

Lemma gfun_cocase_order_g: forall (p : program) (gfun: gfun_bod_named),
    In gfun (program_gfun_bods_g p) ->
    map (fun x => fst x) (snd gfun)
    = filter (fun t => eq_TypeName (fst (unscope t)) (fst (fst gfun))) (map (fun x => fst (fst x)) (skeleton_dtors (program_skeleton p))).
Proof.
  intros p gfun H_in.
  pose proof (program_gfun_bods_typecheck_g p) as H_t.
  unfold gfun_bods_g_typecheck in H_t; rewrite Forall_forall in H_t.
  specialize (H_t gfun H_in). inversion H_t as [qn [args [H_lookup H_t']]].
  inversion H_t'; subst. apply lookup_dtors_name_order in H6.
  unfold gfun_bod in *. rewrite <- H6.
  clear - H7  H8. destruct gfun; simpl in *.
  gen_induction dtorlist g; destruct dtorlist; inversion H8; subst; auto.
  simpl in *. inversion H7; subst; auto.
  repeat match goal with
         | [  |- context [fst (fst ?x)] ] => destruct x; simpl in *
         | [  |- context [fst ?x] ] => destruct x; simpl in *
         end; f_equal; auto.
Qed.

Lemma gfun_cocase_order_l: forall (p : program) (gfun: gfun_bod_named),
    In gfun (program_gfun_bods_l p) ->
    map (fun x => fst x) (snd gfun)
    = filter (fun t => eq_TypeName (fst (unscope t)) (fst (fst gfun))) (map (fun x => fst (fst x)) (skeleton_dtors (program_skeleton p))).
Proof.
  intros p gfun H_in.
  pose proof (program_gfun_bods_typecheck_l p) as H_t.
  unfold gfun_bods_l_typecheck in H_t; rewrite Forall_forall in H_t.
  specialize (H_t gfun H_in). inversion H_t as [qn [args [H_lookup H_t']]].
  inversion H_t'; subst. apply lookup_dtors_name_order in H6.
  unfold gfun_bod in *. rewrite <- H6.
  clear - H7  H8. destruct gfun; simpl in *.
  gen_induction dtorlist g; destruct dtorlist; inversion H8; subst; auto.
  simpl in *. inversion H7; subst; auto.
  repeat match goal with
         | [  |- context [fst (fst ?x)] ] => destruct x; simpl in *
         | [  |- context [fst ?x] ] => destruct x; simpl in *
         end; f_equal; auto.
Qed.




Lemma comatch_names_unique_global_sublist: forall fs cfs_g cfs_l gfs_g gfs_l,
    comatch_names_unique fs (cfs_g ++ cfs_l) (gfs_g ++ gfs_l) ->
    comatch_names_unique fs cfs_g gfs_g.
Proof.
  intros.
  unfold comatch_names_unique in *.
  repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
  repeat rewrite <- app_assoc in H.
  unique_sublist_tac.
Qed.

Lemma match_names_unique_global_sublist: forall fs cfs_g cfs_l gfs_g gfs_l,
    match_names_unique fs (cfs_g ++ cfs_l) (gfs_g ++ gfs_l) ->
    match_names_unique fs cfs_g gfs_g.
Proof.
  intros.
  unfold match_names_unique in *.
  repeat (repeat rewrite map_app in *; repeat rewrite concat_app in * ).
  repeat rewrite <- app_assoc in H.
  unique_sublist_tac.
Qed.
