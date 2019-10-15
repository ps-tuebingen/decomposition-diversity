(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: Names.v                                                                                  *)
(*                                                                                                *)
(**************************************************************************************************)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Program.Basics.
Import ListNotations.

(**************************************************************************************************)
(** * Definition of Names.                                                                        *)
(**************************************************************************************************)

Definition VarName := nat.

Inductive TypeName : Type := TName : string -> TypeName.

Definition Name := string.

Definition QName : Type := (TypeName * Name).

Inductive ScopedName : Type :=
  | local : QName -> ScopedName
  | global : QName -> ScopedName.

(**************************************************************************************************)
(** * Utility functions                                                                           *)
(**                                                                                               *)
(** A collection of utility functions for comparing names and looking up information in a program *)
(** skeleton or a program.                                                                        *)
(**************************************************************************************************)

Definition unscope (sn : ScopedName) : QName :=
  match sn with
  | local qn => qn
  | global qn => qn
  end.

Inductive is_local : ScopedName ->  Prop :=
  Is_local_local : forall (qn : QName), is_local (local qn).

Inductive is_global : ScopedName ->  Prop :=
  Is_global_global : forall (qn : QName), is_global (global qn).


(**************************************************************************************************)
(** ** Comparison functions                                                                       *)
(**                                                                                               *)
(** Comparison of strings, Names, QNames, ScopedNames and TypeNames.                              *)
(**************************************************************************************************)

(**************************************************************************************************)
(** *** ASCII equality                                                                            *)
(**************************************************************************************************)

Lemma eqb_sym : forall (b1 b2 : bool), eqb b1 b2 = eqb b2 b1.
Proof. intros b1 b2. destruct b1; destruct b2; tauto. Qed.

Definition eq_ascii (a1 a2 : ascii) :=
  match a1, a2 with
  | Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
    (eqb b1 c1) && (eqb b2 c2) && (eqb b3 c3) && (eqb b4 c4) &&
    (eqb b5 c5) && (eqb b6 c6) && (eqb b7 c7) && (eqb b8 c8)
  end.

Lemma eq_ascii_refl : forall (a : ascii), eq_ascii a a = true.
Proof. intros a. induction a. simpl. repeat (rewrite eqb_reflx). simpl. reflexivity. Qed.

Lemma eq_ascii_eq : forall (a1 a2 : ascii), eq_ascii a1 a2 = true <-> a1 = a2.
Proof. intros a1 a2.
       unfold iff. split.
       -destruct a1; destruct a2. simpl.
        intro H. repeat (rewrite -> andb_true_iff in * ).
        repeat (rewrite -> eqb_true_iff in * ).
        repeat(destruct H). subst. reflexivity.
       -intro. rewrite H. destruct a2. simpl. repeat (rewrite eqb_reflx). reflexivity.
Qed.

Lemma eq_ascii_symm : forall (a1 a2 : ascii), eq_ascii a1 a2 = eq_ascii a2 a1.
Proof.
  intros a1 a2. destruct a1; destruct a2; simpl.
  rewrite (eqb_sym b b7).
  rewrite (eqb_sym b0 b8).
  rewrite (eqb_sym b1 b9).
  rewrite (eqb_sym b2 b10).
  rewrite (eqb_sym b3 b11).
  rewrite (eqb_sym b4 b12).
  rewrite (eqb_sym b5 b13).
  rewrite (eqb_sym b6 b14).
  reflexivity.
Qed.

(**************************************************************************************************)
(** *** String equality                                                                           *)
(**************************************************************************************************)

Fixpoint eq_string (s1 s2 : string) :=
  match s1, s2 with
  | EmptyString,  EmptyString  => true
  | String x1 s1, String x2 s2 => eq_ascii x1 x2 && eq_string s1 s2
  | _, _                       => false
  end.

Lemma eq_string_refl : forall (s : string), eq_string s s = true.
Proof.
  intro s. induction s.
  -simpl. reflexivity.
  -simpl. rewrite IHs. rewrite eq_ascii_refl. reflexivity.
Qed.

Lemma eq_string_eq : forall (s1 s2 : string), eq_string s1 s2 = true <-> s1 = s2.
Proof.
  unfold iff. split.
  -generalize dependent s2. induction s1.
   +induction s2.
    *reflexivity.
    *intro H. simpl in H. inversion H.
   +induction s2.
    *intros. simpl in H. inversion H.
    *intros. simpl in H. rewrite andb_true_iff in H. destruct H.
     apply  eq_ascii_eq in H; subst. apply IHs1 in H0; subst.
     reflexivity.
  -intro. rewrite H. clear H. induction s2; try reflexivity. simpl. apply andb_true_iff. split; try (apply IHs2).
   +apply eq_ascii_eq. reflexivity.
Qed.

Lemma eq_string_symm : forall (s1 s2 : string), eq_string s1 s2 = eq_string s2 s1.
Proof.
  intros s1. induction s1.
  -intro s2. induction s2.
   +reflexivity.
   +reflexivity.
  -intro s2. induction s2.
   +reflexivity.
   +simpl. rewrite IHs1. rewrite eq_ascii_symm. reflexivity.
Qed.

(**************************************************************************************************)
(** *** Name equality (Name is just an Alias for string)                                          *)
(**************************************************************************************************)

Definition eq_Name (n1 n2 : Name) : bool := eq_string n1 n2.
Definition eq_Name_eq : forall (n1 n2 : Name), eq_Name n1 n2 = true <-> n1 = n2 := eq_string_eq.
Definition eq_Name_symm : forall (n1 n2 : Name), eq_Name n1 n2 = eq_Name n2 n1 := eq_string_symm.
Definition eq_Name_refl : forall (n : Name), eq_Name n n = true := eq_string_refl.

(**************************************************************************************************)
(** *** TypeName equality                                                                         *)
(**************************************************************************************************)

Definition eq_TypeName (tn1 tn2 : TypeName) : bool :=
    match tn1, tn2 with
    | (TName n1), (TName n2) => eq_Name n1 n2
    end.

Lemma eq_TypeName_eq : forall (tn1 tn2 : TypeName),
    eq_TypeName tn1 tn2 = true <-> tn1 = tn2.
Proof.
  intros t1 t2. unfold iff. split.
  -intro H. unfold eq_TypeName in H.
   destruct t1 as [s1]. destruct t2 as [s2].
   apply eq_string_eq in H; subst; reflexivity.
   -intro H. rewrite H. destruct t2. simpl. unfold eq_Name. apply eq_string_eq. reflexivity.
Qed.

Lemma eq_TypeName_refl : forall (tn : TypeName),
    eq_TypeName tn tn = true.
Proof.
  intro n. rewrite eq_TypeName_eq. reflexivity.
Qed.

Lemma eq_TypeName_symm : forall (tn1 tn2 : TypeName),
    eq_TypeName tn1 tn2 = eq_TypeName tn2 tn1.
Proof.
  intros. destruct tn1. destruct tn2. simpl. unfold eq_Name. apply eq_string_symm.
Qed.

(**************************************************************************************************)
(** *** QName equality                                                                            *)
(**************************************************************************************************)

Definition eq_QName (qn1 qn2 : QName) : bool :=
    match qn1, qn2 with
    | (tn1,n1), (tn2,n2) => eq_TypeName tn1 tn2 && eq_Name n1 n2
    end.

Lemma eq_QName_eq : forall (qn1 qn2 : QName),
    eq_QName qn1 qn2 = true <-> qn1 = qn2.
Proof.
  intros qn1 qn2. unfold iff. split.
  -intro H. destruct qn1; destruct qn2; simpl in H; rewrite andb_true_iff in H; destruct H;
              apply eq_TypeName_eq in H; apply eq_string_eq in H0; subst; auto.
  -intro H. rewrite H. unfold eq_QName. destruct qn2. apply andb_true_iff. split.
   +apply eq_TypeName_eq. reflexivity.
   +unfold eq_Name. apply eq_string_eq. reflexivity.
Qed.

Lemma eq_QName_symm : forall (qn1 qn2 : QName),
    eq_QName qn1 qn2 = eq_QName qn2 qn1.
Proof.
  intros. destruct qn1. destruct qn2. simpl. rewrite eq_TypeName_symm. rewrite eq_Name_symm. reflexivity.
Qed.

Lemma eq_QName_refl : forall (qn : QName), eq_QName qn qn = true.
Proof.
  intro qn. destruct qn. simpl. rewrite eq_TypeName_refl. rewrite eq_Name_refl. reflexivity.
Qed.

(**************************************************************************************************)
(** *** ScopedName equality                                                                       *)
(**************************************************************************************************)

Definition eq_ScopedName (sn1 sn2 : ScopedName) : bool :=
    match sn1, sn2 with
    | (local qn1), (local qn2) => eq_QName qn1 qn2
    | (global qn1), (global qn2) => eq_QName qn1 qn2
    | (local _), (global _) => false
    | (global _), (local _) => false
    end.

Lemma eq_ScopedName_refl : forall (sn : ScopedName),
    eq_ScopedName sn sn = true.
Proof.
  intro sn. destruct sn; simpl; rewrite eq_QName_eq; reflexivity.
Qed.

Lemma eq_ScopedName_eq : forall (sn1 sn2 : ScopedName),
    eq_ScopedName sn1 sn2 = true <->
    sn1 = sn2.
Proof.
  intros sn1 sn2; split; intro H2.
  destruct sn1; destruct sn2; simpl in H2; f_equal.
  +apply eq_QName_eq in H2. auto.
  +inversion H2.
  +inversion H2.
  +apply eq_QName_eq in H2. auto.
  +subst. apply eq_ScopedName_refl.
Qed.

Lemma eq_ScopedName_symm : forall (sn1 sn2 : ScopedName),
    eq_ScopedName sn1 sn2 = eq_ScopedName sn2 sn1.
Proof.
  intros sn1 sn2. destruct sn1 as [[tn1 n1] | [tn1 n1]]; destruct sn2 as [[tn2 n2] | [tn2 n2]]; simpl; try reflexivity;
                    rewrite eq_TypeName_symm; rewrite eq_Name_symm; reflexivity.
Qed.

(**************************************************************************************************)
(** *** Tactics for working with equality of names                                                *)
(**************************************************************************************************)

Ltac name_refl_tac :=
      match goal with
    | [ |- context [eq_Name ?n ?n] ] => rewrite eq_Name_refl
    | [ |- context [eq_QName ?n ?n] ] => rewrite eq_QName_refl
    | [ |- context [eq_ScopedName ?n ?n] ] => rewrite eq_ScopedName_refl
    | [ |- context [eq_TypeName ?n ?n] ] => rewrite eq_TypeName_refl
    | [ H : context [eq_Name ?n ?n] |- _] => rewrite eq_Name_refl in H
    | [ H : context [eq_QName ?n ?n] |- _] => rewrite eq_QName_refl in H
    | [ H : context [eq_ScopedName ?n ?n] |- _] => rewrite eq_ScopedName_refl in H
    | [ H : context [eq_TypeName ?n ?n] |- _] => rewrite eq_TypeName_refl in H
      end;
      try (solve [reflexivity]).

Ltac name_eq_rewrite_tac :=
  match goal with
  | [ H : eq_Name ?n1 ?n2 = true |- _] => rewrite eq_Name_eq in H
  | [ H : eq_TypeName ?n1 ?n2 = true |- _] => rewrite eq_TypeName_eq in H
  | [ H : eq_ScopedName ?n1 ?n2 = true |- _] => rewrite eq_ScopedName_eq in H
  | [ H : eq_QName ?n1 ?n2 = true |- _] => rewrite eq_QName_eq in H
  end.

Ltac name_refl_contradiction_tac :=
    let Hf := fresh
    in match goal with
    | [ H: eq_Name ?sn ?sn = false |- _ ] =>
            assert (Hf: sn = sn); [> reflexivity | apply eq_Name_eq in Hf; rewrite H in Hf; inversion Hf ]
    | [ H: eq_QName ?sn ?sn = false |- _ ] =>
            assert (Hf: sn = sn); [> reflexivity | apply eq_QName_eq in Hf; rewrite H in Hf; inversion Hf ]
    | [ H: eq_TypeName ?sn ?sn = false |- _ ] =>
            assert (Hf: sn = sn); [> reflexivity | apply eq_TypeName_eq in Hf; rewrite H in Hf; inversion Hf ]
    | [ H: eq_ScopedName ?sn ?sn = false |- _ ] =>
            assert (Hf: sn = sn); [> reflexivity | apply eq_ScopedName_eq in Hf; rewrite H in Hf; inversion Hf ]
  end.

Ltac name_eq_tac :=
  name_eq_rewrite_tac; subst; try reflexivity.

Ltac name_destruct_tac :=
  match goal with
  | [  |- context [ eq_Name ?n ?n1 ] ] => let E := fresh "E_" "_name" in destruct (eq_Name n n1) eqn:E
  | [  |- context [ eq_TypeName ?n ?n1 ] ] => let E := fresh "E_" "_name" in destruct (eq_TypeName n n1) eqn:E
  | [  |- context [ eq_QName ?n ?n1 ] ] => let E := fresh "E_" "_name" in destruct (eq_QName n n1) eqn:E
  | [  |- context [ eq_ScopedName ?n ?n1 ] ] => let E := fresh "E_" "_name" in destruct (eq_ScopedName n n1) eqn:E
  | [ _: context [ eq_Name ?n ?n1 ] |- _ ] => let E := fresh "E_" "_name" in destruct (eq_Name n n1) eqn:E
  | [ _: context [ eq_TypeName ?n ?n1 ] |- _ ] => let E := fresh "E_" "_name" in destruct (eq_TypeName n n1) eqn:E
  | [ _: context [ eq_QName ?n ?n1 ] |- _ ] => let E := fresh "E_" "_name" in destruct (eq_QName n n1) eqn:E
  | [ _: context [ eq_ScopedName ?n ?n1 ] |- _ ] => let E := fresh "E_" "_name" in destruct (eq_ScopedName n n1) eqn:E
  end.

Definition decidable (A : Type): Type :=
  forall (x y: A), {x = y} + {x <> y}.

Lemma TypeName_dec: decidable TypeName.
Proof.
  unfold decidable; intros.
  destruct (eq_TypeName x y) eqn:E.
  - name_eq_tac; auto.
  - right; intro; subst; name_refl_contradiction_tac.
Qed.

Lemma QName_dec: decidable QName.
Proof.
  unfold decidable; intros.
  destruct (eq_QName x y) eqn:E.
  - name_eq_tac; auto.
  - right; intro; subst; name_refl_contradiction_tac.
Qed.

