
Require Import Coq.Lists.List.
Import ListNotations.

Require Import CtorizeII.
Require Import DtorizeII.
Require Import AST.
Require Import Names.
Require Import Eval.
Require Import GenericLemmas.
Require Import GenericTactics.

Lemma ctorize_substitution: forall (e e' : expr) (tn : TypeName) (n : nat),
    constructorize_expr tn (substitute' n e' e) =
    substitute' n (constructorize_expr tn e')
                (constructorize_expr tn e).
Proof.
  intros.
  gen_dep n.
  induction e using expr_strong_ind; intros; simpl;
    try solve [f_equal; induction ls; simpl; auto; f_equal; inversion H; auto];
    try solve [match_destruct_tac; simpl; f_equal; auto;
               induction ls; auto; simpl; f_equal; inversion H; auto];
    try solve [f_equal; auto;
               induction es; simpl; auto; f_equal; inversion H0; auto;
               destruct a; simpl; f_equal; auto].
  destruct v; simpl; match_destruct_tac; auto.
  match_destruct_tac; simpl; auto.
Qed.

Lemma dtorize_substitution: forall (e e' : expr) (tn : TypeName) (n : nat),
    destructorize_expr tn (substitute' n e' e) =
    substitute' n (destructorize_expr tn e')
                (destructorize_expr tn e).
Proof.
  intros.
  gen_dep n.
  induction e using expr_strong_ind; intros; simpl;
    try solve [f_equal; induction ls; simpl; auto; f_equal; inversion H; auto];
    try solve [match_destruct_tac; simpl; f_equal; auto;
               induction ls; auto; simpl; f_equal; inversion H; auto];
    try solve [f_equal; auto;
               induction es; simpl; auto; f_equal; inversion H0; auto;
               destruct a; simpl; f_equal; auto].
  destruct v; simpl; match_destruct_tac; auto.
  match_destruct_tac; simpl; auto.
Qed.
