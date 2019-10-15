(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: Sublists.v                                                                               *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Unique.

Require Import ProgramDef.

Inductive Sublist {A : Type} : (list A) -> (list A) ->  Prop :=
| Sublist_nil : forall ys, Sublist [] ys
| Sublist_eq : forall xs ys z, Sublist xs ys -> Sublist (z :: xs) (z :: ys)
| Sublist_cons : forall xs ys  y, Sublist xs ys -> Sublist xs (y :: ys).

Lemma Unique_sublist : forall {A : Type} (xs ys : list A),
    Sublist xs ys ->
    unique ys ->
    unique ys.
Proof.
  intros. inversion H; subst.
  -assumption.
  -apply Unique_cons.
   +  inversion H0; subst. assumption.
   + inversion H0; subst. assumption.
  - apply Unique_cons.
    + inversion H0; subst. assumption.
    + inversion H0; subst. assumption.
Qed.

Lemma Sublist_refl : forall {A  : Type} (xs : list A),
    Sublist xs xs.
Proof.
  intros. induction xs.
  - apply Sublist_nil.
  - apply Sublist_eq. assumption.
Qed.

Lemma Sublist_app_r : forall {A : Type} (xs xs' ys : list A),
    Sublist xs xs' ->
    Sublist xs (ys ++ xs').
Proof.
  intros. induction ys.
  - simpl. assumption.
  - simpl. apply Sublist_cons. assumption.
Qed.

Lemma Sublist_app_l : forall {A : Type} (xs xs' ys : list A),
    Sublist xs xs' ->
    Sublist xs (xs' ++ ys).
Proof.
  intros. generalize dependent xs. generalize dependent ys.
  induction xs'; intros; simpl in *.
  - inversion H; subst. apply Sublist_nil.
  - inversion H; subst.
    + apply Sublist_nil.
    + apply Sublist_eq. apply IHxs'. assumption.
    + apply Sublist_cons. apply IHxs'. assumption.
Qed.

Lemma Sublist_app_cons_r : forall {A : Type} (xs xs' : list A) (a : A),
    Sublist xs xs' ->
    Sublist (xs ++ [a]) (xs' ++ [a]).
Proof.
  intros A xs xs' a H. generalize dependent xs. induction xs'; simpl; intros.
  - inversion H; subst. simpl. apply Sublist_refl.
  - inversion H; subst; simpl in *.
    * clear. apply Sublist_cons. induction xs'.
      ** simpl. apply Sublist_refl.
      ** simpl. apply Sublist_cons. assumption.
    * apply Sublist_eq. apply IHxs'. assumption.
    * apply Sublist_cons. apply IHxs'. assumption.
Qed.

Lemma app_cons : forall {A : Type} (xs ys : list A) (y : A),
    xs ++ (y :: ys) = (xs ++ [y]) ++ ys.
Proof.
  intros A xs ys y. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma Sublist_app_same_r : forall {A : Type} (xs xs' ys : list A),
    Sublist xs xs' ->
    Sublist (xs ++ ys) (xs' ++ ys).
Proof.
  intros A xs xs' ys H. generalize dependent xs. generalize dependent xs'.
  induction ys.
  - intros xs' xs H. repeat rewrite app_nil_r. assumption.
  - intros. rewrite app_cons. rewrite (app_cons xs'). apply IHys.
    apply Sublist_app_cons_r. assumption.
Qed.

Lemma Sublist_app_same_l : forall {A : Type} (xs xs' ys : list A),
    Sublist xs xs' ->
    Sublist (ys ++ xs) (ys ++ xs').
Proof.
  intros. induction ys.
  - simpl. assumption.
  - simpl. apply Sublist_eq. assumption.
Qed.

Lemma Sublist_app : forall {A : Type} (xs xs' ys ys' : list A),
    Sublist xs xs' ->
    Sublist ys ys' ->
    Sublist (xs ++ ys) (xs' ++ ys').
Proof.
  intros A xs xs' ys ys' H H0.
  generalize dependent xs. generalize dependent ys. generalize dependent ys'.
  induction xs'; intros.
  - simpl. inversion H; subst. simpl. assumption.
  - inversion H; subst; simpl in *.
    + apply Sublist_cons. apply Sublist_app_r. assumption.
    + apply Sublist_eq. apply IHxs'; try assumption.
    + specialize (IHxs' ys' ys H0).
      inversion H; subst; simpl in *.
      * pose proof (Sublist_app_r ys ys' (a :: xs')).
        simpl in H1. apply H1. assumption.
      * apply Sublist_eq. apply IHxs'; try assumption.
      * apply Sublist_cons. apply IHxs'. assumption.
Qed.
