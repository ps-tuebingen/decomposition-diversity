(**************************************************************************************************)
(* Total Constructor/Destructorization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: Unique.v                                                                                 *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import GenericTactics.
Require Import Sublist.

Inductive unique {A : Type} : list A -> Prop :=
| Unique_nil : unique []
| Unique_cons : forall (a : A) (ls : list A),
    ~ In a ls ->
    unique ls ->
    unique (a :: ls).

Remark filter_unique : forall A f (l : list A), unique l -> unique (filter f l).
Proof with auto.
intros. induction l...
simpl. case (f a); intros.
- inversion H; subst. apply Unique_cons...
  unfold not. unfold not in H2. intros. apply H2.
  rewrite filter_In in H0. destruct H0...
- inversion H; subst...
Qed.

Lemma unique_app_switch : forall {A} (l1 l2 l3 : list A), unique (l1 ++ (l2 ++ l3)) -> unique (l1 ++ (l3 ++ l2)).
Proof with auto.
intros. apply proj1 with (B:=forall a, ~ In a (l1++l2++l3) -> ~ In a (l1++l3++l2)).
generalize dependent l2. generalize dependent l3. induction l1.
- intros. split.
  + simpl in *. generalize dependent l3. induction l2; intros.
    * rewrite app_nil_r...
    * inversion H; subst.
      assert (unique (l2 ++ l3 ++ [a])).
      { clear - H2 H3. generalize H2. generalize H3. rewrite app_assoc. generalize (l2++l3).
        clear. induction l; intros.
        - apply Unique_cons...
        - simpl. apply Unique_cons.
          + inversion H3; subst. unfold not. intros. apply in_app_or in H. destruct H...
            unfold not in H2. apply H2. inversion H; subst; try inversion H0. apply in_eq.
          + apply IHl; inversion H3; subst... unfold not. unfold not in H2. intros. apply H2.
            apply in_cons...
      }
      apply IHl2 in H0. rewrite <- app_assoc in H0...
  + intros. unfold not. intros. unfold not in H0. apply H0.
    simpl in *. apply in_app_or in H1. apply in_or_app. destruct H1.
    * right...
    * left...
- intros. inversion H; subst. apply IHl1 in H3. simpl. destruct H3. split.
  + apply Unique_cons...
  + intros. unfold not. intros. destruct H4.
    * subst. unfold not in H3. apply H3. left...
    * unfold not in H3. apply H3. right.
      apply in_or_app.
      apply in_app_or in H4. destruct H4; [| apply in_app_or in H4; destruct H4].
      -- left...
      -- right. apply in_or_app. right...
      -- right. apply in_or_app. left...
Qed.

Lemma uniqueness_piecewise: forall {A : Type} (l m r : list A),
    unique (l ++ m) ->
    unique (m ++ r) ->
    unique (l ++ r) ->
    unique (l ++ m ++ r).
Proof.
  intros A l m r H H0 H1.
  induction l; try assumption.
  simpl. apply Unique_cons;  inversion_clear H1; inversion_clear H.
  - intro Hin. apply in_app_iff in Hin. inversion_clear Hin; try (apply in_app_iff in H; inversion H).
    + apply H2. apply in_app_iff. left; auto.
    + apply H1. apply in_app_iff. right; auto.
    + apply H2. apply in_app_iff. right; auto.
  - IH_auto_tac.
Qed.

Lemma In_app_l: forall {A : Type} (a : A) (l r : list A),
    In a l ->
    In a (l ++ r).
Proof.
  intros A a l r H.
  induction l; inversion_clear H; subst.
  - left; reflexivity.
  - right; IH_tac.
Qed.

Lemma In_app_r: forall {A : Type} (a : A) (l r : list A),
    In a r ->
    In a (l ++ r).
Proof.
  intros A a l r H.
  induction l; try assumption.
  right; assumption.
Qed.

Lemma In_app_iff: forall {A : Type} (a : A) (l r : list A),
    In a l \/ In a r <->
    In a (l ++ r).
Proof.
  intros A a l r; split; intro H.
  - inversion H; apply In_app_l + apply In_app_r; assumption.
  - induction l.
    + right; assumption.
    + inversion H; subst.
      * left; left; reflexivity.
      * specialize (IHl H0). inversion IHl; try (left + right; try right; assumption).
Qed.

Lemma uniqueness_app: forall {A : Type} (l r : list A),
    unique l ->
    unique r ->
    Forall (fun x => ~ In x r) l ->
    unique (l ++ r).
Proof.
  intros A l r H H0 H1.
  induction l; try assumption.
  simpl. apply Unique_cons.
  - inversion_clear H1. intro Hin; inversion H; subst.
    apply In_app_iff in Hin. inversion Hin.
    + apply H5; assumption.
    + apply H2; assumption.
  - IH_tac (try Forall_tail_tac). inversion H; assumption.
Qed.

Lemma uniqueness_sublist: forall {A : Type} (sub tot : list A),
    sublist sub tot ->
    unique tot ->
    unique sub.
Proof.
  intros A sub tot H H0.
  gen_induction sub tot; destruct sub; try apply Unique_nil; inversion_clear H.
  - inversion_clear H0. apply IHtot; try assumption.
  - inversion_clear H0. apply Unique_cons.
    + intro H_in. assert (H_in_tot: In a tot); [> | apply H; assumption].
      apply In_sublist with (sub0 := sub); try assumption.
    + IH_auto_tac.
Qed.

Lemma uniqueness_concat: forall {A B : Type} (f : A -> list B) (l : list A),
    unique (concat (map f l)) ->
    Forall (fun x => unique (f x)) l.
Proof.
  intros A B f l H.
  induction l; try apply Forall_nil.
  apply Forall_cons; try IH_tac;
  match goal with
  | [ H: unique ?ls |- unique ?gs ] =>
    assert (sublist gs ls);
      [> (apply sublist_app_embed_l || apply sublist_app_embed_r)
      | apply uniqueness_sublist with (sub := gs) (tot := ls); assumption
      ]
  end.
Qed.

Lemma uniqueness_app_not_in: forall {A : Type} (l r : list A),
    unique (l ++ r) ->
    Forall (fun x => ~ In x r) l.
Proof.
  intros A l r H.
  induction l; try apply Forall_nil.
  apply Forall_cons; try IH_tac.
  - inversion H. intro H_in. apply H2.
    apply In_app_r; assumption.
  - inversion H; assumption.
Qed.

Ltac unique_sublist_tac :=
  match goal with
  | [ H: unique ?t |- unique ?s ] =>
    apply uniqueness_sublist with (sub := s) (tot := t);
    [> sublist_tac
    | try assumption
    ]
  end.

Lemma uniqueness_app_3way: forall {A : Type} (xs ys zs: list A),
    unique xs ->
    unique ys ->
    unique zs ->
    Forall (fun x => ~ In x ys) xs ->
    Forall (fun x => ~ In x zs) xs ->
    Forall (fun y => ~ In y zs) ys ->
    unique (xs ++ ys ++ zs).
Proof.
  intros A xs ys zs H H0 H1 H2 H3 H4.
  do 2 (try apply uniqueness_app; try assumption).
  induction xs; try apply Forall_nil.
  inversion H; inversion H2; inversion H3; subst.
  apply Forall_cons; try IH_tac.
  intro H_in. apply in_app_or in H_in.
  inversion H_in; contradiction.
Qed.

Ltac unique_reduce_tac ls :=
  match goal with
  | [ H: unique (?l ++ ?r) |- _ ] =>
    let H' := fresh in
    let sub :=
        match l with
        | context [ls] => l
        | _ => r
        end
    in assert (H': unique sub); [> unique_sublist_tac | clear H; rename H' into H];
       unique_reduce_tac ls
  | _ => idtac
  end.

Lemma uniqueness_app_rewrite: forall {A : Type} (l r : list A),
    unique l /\ unique r /\ Forall (fun x => ~ In x r) l <->
    unique (l ++ r).
Proof.
  intros A l r; split; intro H'.
  - inversion_clear H' as [H [H0 H1]].
  induction l; try assumption.
  simpl. apply Unique_cons.
    + inversion_clear H1. intro Hin; inversion H; subst.
      apply In_app_iff in Hin. inversion Hin.
      * apply H5; assumption.
      * apply H2; assumption.
    + IH_tac (try Forall_tail_tac). inversion H; assumption.
  - repeat split; try unique_sublist_tac.
    apply uniqueness_app_not_in; auto.
Qed.

Ltac unique_app_destr_tac :=
  match goal with
  | [ Hunique: unique (?l ++ ?r) |- _ ] =>
    let H1 := fresh Hunique in
    let H2 := fresh Hunique in
    let Hf := fresh Hunique "_f" in
    rewrite <- uniqueness_app_rewrite in Hunique;
    inversion_clear Hunique as [H1 [H2 Hf]]
  end.

Lemma uniqueness_map: forall {A B : Type} (f : A -> B) (ls : list A),
    unique (map f ls) ->
    unique ls.
Proof.
  intros.
  induction ls; simpl in *; try apply Unique_nil.
  inversion_clear H.
  apply Unique_cons; auto.
  intro Hin; apply H0; apply in_map; auto.
Qed.
