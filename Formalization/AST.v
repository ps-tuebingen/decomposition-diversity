(**************************************************************************************************)
(* Total Constructor/Destructorization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: AST.v                                                                                    *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Ascii.
Require Import String.
Require Import Bool.
Require Import Lists.List.
Require Import Coq.Program.Basics.
Import ListNotations.

Require Import Names.
Require Import OptionMonad.

(**************************************************************************************************)
(** * Abstract syntax of expressions.                                                             *)
(**                                                                                               *)
(**************************************************************************************************)
Inductive expr : Type :=
  | E_Var : VarName -> expr
  | E_Constr : ScopedName -> list expr -> expr
  | E_DestrCall : ScopedName -> expr -> list expr -> expr
  | E_FunCall : Name -> list expr -> expr
  | E_GenFunCall : ScopedName -> list expr -> expr
  | E_ConsFunCall : ScopedName -> expr -> list expr -> expr
  | E_Match : QName -> expr -> list (expr * TypeName) -> list (ScopedName * expr) -> TypeName -> expr
  | E_CoMatch : QName -> list (expr * TypeName) ->  list (ScopedName * expr) -> expr
  | E_Let : expr -> expr -> expr.

(**************************************************************************************************)
(** * Induction principle                                                                         *)
(**                                                                                               *)
(** The induction principle for expr generated by Coq is too weak. We must define our own         *)
(** induction principle.                                                                          *)
(**************************************************************************************************)
Section Expr_Induction.
  Variable P : expr -> Prop.

  Hypothesis E_Var_Case : forall (v : VarName), P (E_Var v).
  Hypothesis E_Constr_Case : forall (n : ScopedName) (ls : list expr),
      Forall P ls -> P (E_Constr n ls).
  Hypothesis E_DestrCall_Case : forall (n : ScopedName) (e : expr) (ls : list expr),
      Forall P ls -> P e -> P (E_DestrCall n e ls).
  Hypothesis E_FunCall_Case : forall (n : Name) (ls : list expr),
      Forall P ls -> P (E_FunCall n ls).
  Hypothesis E_ConsFunCall_Case : forall (sn : ScopedName) (e: expr) (ls : list expr),
      Forall P ls -> P e -> P (E_ConsFunCall sn e ls).
  Hypothesis E_GenFunCall_Case : forall (sn : ScopedName) (ls : list expr),
      Forall P ls -> P (E_GenFunCall sn ls).
  Hypothesis E_Match_Case : forall (n : QName) (e: expr)(es: list (expr * TypeName)) (ls : list (ScopedName * expr)) (tn : TypeName),
      Forall P (List.map (fun n => match n with (_,x) => x end) ls) ->
      Forall P (List.map (fun et => match et with (e,_) => e end) es) ->
      P e -> P (E_Match n e es ls tn).
  Hypothesis E_CoMatch_Case : forall (n : QName) (es: list (expr * TypeName)) (ls : list (ScopedName * expr)),
      Forall P (List.map (fun n => match n with (_,x) => x end) ls) ->
      Forall P (List.map (fun et => match et with (e,_) => e end) es) ->
      P (E_CoMatch n es ls).
  Hypothesis E_Let_Case : forall (e1 e2 : expr),
      P e1 -> P e2 -> P (E_Let e1 e2).

  Fixpoint expr_strong_ind (e : expr) : P e :=
    match e with
    | E_Var v => E_Var_Case v
    | E_Constr n ls => E_Constr_Case n ls
                                     (* Proof that: Forall P ls *)
                                     (( fix list_expr_ind (ls : list expr) : Forall P ls :=
                                          match ls with
                                          | [] => Forall_nil P
                                          | (ex :: exs) => Forall_cons ex (expr_strong_ind ex) (list_expr_ind exs)
                                          end) ls)
    | E_DestrCall n e ls => E_DestrCall_Case n e ls
                                     (* Proof that: Forall P ls *)
                                     (( fix list_expr_ind (ls : list expr) : Forall P ls :=
                                          match ls with
                                          | [] => Forall_nil P
                                          | (ex :: exs) => Forall_cons ex (expr_strong_ind ex) (list_expr_ind exs)
                                          end) ls) (expr_strong_ind e)
    | E_FunCall n ls => E_FunCall_Case n ls
                                       (* Proof that: Forall P ls *)
                                       (( fix list_expr_ind (ls : list expr) : Forall P ls :=
                                          match ls with
                                          | [] => Forall_nil P
                                          | (ex :: exs) => Forall_cons ex (expr_strong_ind ex) (list_expr_ind exs)
                                          end) ls)
    | E_ConsFunCall n e ls => E_ConsFunCall_Case n e ls
                                       (* Proof that: Forall P ls *)
                                       (( fix list_expr_ind (ls : list expr) : Forall P ls :=
                                          match ls with
                                          | [] => Forall_nil P
                                          | (ex :: exs) => Forall_cons ex (expr_strong_ind ex) (list_expr_ind exs)
                                          end) ls) (expr_strong_ind e)
    | E_GenFunCall n ls => E_GenFunCall_Case n ls
                                       (* Proof that: Forall P ls *)
                                       (( fix list_expr_ind (ls : list expr) : Forall P ls :=
                                          match ls with
                                          | [] => Forall_nil P
                                          | (ex :: exs) => Forall_cons ex (expr_strong_ind ex) (list_expr_ind exs)
                                          end) ls)
    | E_Match n e es ls tn => E_Match_Case n e es ls tn
                                     (* Proof that: Forall P (List.map (fun n => match n with (_,_,x) => x end) ls) *)
                                     (( fix list_expr_ind (ls : list (ScopedName * expr)) : Forall P (List.map (fun n => match n with (_,x) => x end) ls) :=
                                          match ls with
                                          | [] => Forall_nil P
                                          | (ex :: exs) =>
                                            match ex with
                                            | (_,ex') => Forall_cons ex' (expr_strong_ind ex') (list_expr_ind exs)
                                            end
                                          end) ls)
                                     (* Proof that: Forall P (List.map (fun n => match n with (_,x) => x end) es) *)
                                     (( fix list_expr_ind (es : list (expr * TypeName)) : Forall P (List.map (fun et => match et with (e,_) => e end) es) :=
                                          match es with
                                          | [] => Forall_nil P
                                          | (ex :: exs) =>
                                            match ex with
                                              (e,_) => Forall_cons e (expr_strong_ind e) (list_expr_ind exs)
                                            end
                                          end) es)
                                      (* Proof that: P e *)
                                     (expr_strong_ind e)
    | E_CoMatch n es ls => E_CoMatch_Case n es ls
                                        (* Proof that: Forall P (List.map (fun n => match n with (_,_,x) => x end) ls)*)
                                        (( fix list_expr_ind (ls : list (ScopedName * expr)) : Forall P (List.map (fun n => match n with (_,x) => x end) ls) :=
                                          match ls with
                                          | [] => Forall_nil P
                                          | (ex :: exs) =>
                                            match ex with
                                            | (_,ex') => Forall_cons ex' (expr_strong_ind ex') (list_expr_ind exs)
                                            end
                                          end) ls)
                                        (* Proof that: Forall P (List.map (fun n => match n with (_,x) => x end) es)*)
                                        (( fix list_expr_ind (es : list (expr * TypeName)) : Forall P (List.map (fun et => match et with (e,_) => e end) es) :=
                                          match es with
                                          | [] => Forall_nil P
                                          | (ex :: exs)  =>
                                            match ex with
                                              (e,_) => Forall_cons e (expr_strong_ind e) (list_expr_ind exs)
                                            end
                                          end) es)
    | E_Let e1 e2 => E_Let_Case e1 e2
                                (* Proof that P e1 *)
                                (expr_strong_ind e1)
                                (* Proof that P e2 *)
                                (expr_strong_ind e2)
    end.
End Expr_Induction.


(**************************************************************************************************)
(** * Substitution                                                                                *)
(**                                                                                               *)
(**************************************************************************************************)

Fixpoint substitute' (n : nat) (v e: expr) {struct e} : expr :=
  let curriedSubst := substitute' n v
  in let mapSubst := List.map curriedSubst
  in let mapBindingsSubst := List.map (fun et => match et with (e,t) => (substitute' n v e,t) end)
  in match e with
     | E_Var n' =>
       if Nat.eqb n n'
       then v
       else if Nat.ltb n n'
       then (E_Var (n'-1))
       else (E_Var n')
     | E_Constr name cargs => E_Constr name (mapSubst cargs)
     | E_DestrCall name ex dargs => E_DestrCall name (substitute' n v ex) (mapSubst dargs)
     | E_FunCall name args => E_FunCall name (mapSubst args)
     | E_GenFunCall name args => E_GenFunCall name (mapSubst args)
     | E_ConsFunCall name ex args => E_ConsFunCall name (substitute' n v ex) (mapSubst args)
     | E_Match name ex bindings cases tn => E_Match name
                                                      (substitute' n v ex)
                                                      (mapBindingsSubst bindings)
                                                      cases (* matches should be closures *)
                                                      tn
     | E_CoMatch name bindings cocases => E_CoMatch name
                                                         (mapBindingsSubst bindings)
                                                         cocases (* comatches should be closures *)
     | E_Let e1 e2 => E_Let (substitute' n v e1)
                            (substitute' (n+1) v e2)
     end.

Definition substitute (v e : expr) : expr := substitute' 0 v e.

Fixpoint multi_subst (vs : list expr) (e : expr) {struct vs} : expr :=
  match vs with
  | [] => e
  (*| (v :: vs) => substitute v (multi_subst vs e)*)
  | (v :: vs) => multi_subst vs (substitute v e)
  end.

(**************************************************************************************************)
(** * Injectivity of constructors.                                                                *)
(**                                                                                               *)
(**************************************************************************************************)

Lemma constr_injective : forall n, Injective (E_Constr n).
Proof.
  unfold Injective. intros. inversion H. reflexivity.
Qed.

Lemma funcall_injective : forall n, Injective (E_FunCall n).
Proof.
  unfold Injective. intros. inversion H. reflexivity.
Qed.

Lemma comatchfuncall_injective : forall n, Injective (E_GenFunCall n).
Proof.
  unfold Injective. intros. inversion H. reflexivity.
Qed.

Lemma matchfuncall_injective : forall n e, Injective (E_ConsFunCall n e).
Proof.
  unfold Injective. intros. inversion H. reflexivity.
Qed.

Lemma destr_injective : forall n e, Injective (E_DestrCall n e).
Proof.
  unfold Injective. intros. inversion H. reflexivity.
Qed.

Lemma comatch_injective : forall n ls,
    Injective (fun x : list (expr * TypeName) => E_CoMatch n x ls).
Proof.
  intros n ls x y H.
  inversion H. reflexivity.
Qed.

Lemma match_injective : forall n e ls tn,
    Injective (fun x : list (expr * TypeName) => E_Match n e x ls tn).
Proof.
  intros n e ls tn x y H.
  inversion H. reflexivity.
Qed.

