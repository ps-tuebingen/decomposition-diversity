(* -*- company-coq-initial-fold-state: bullets; -*- *)
(**************************************************************************************************)
(* Total Constructor/Destructorization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: InlineMatch.v                                                                            *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.

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

Fixpoint replace_cfun_call_by_match (snr : ScopedName) (cases : list (ScopedName * expr)) (bts : list TypeName)(rtype : TypeName) (e : expr) : expr :=
  match e with
  | E_Var x => E_Var x
  | E_Constr sn args => E_Constr sn (map (replace_cfun_call_by_match snr cases bts rtype) args)
  | E_DestrCall sn e' args => E_DestrCall sn (replace_cfun_call_by_match snr cases bts rtype e') (map (replace_cfun_call_by_match snr cases bts rtype) args)
  | E_FunCall n args => E_FunCall n (map (replace_cfun_call_by_match snr cases bts rtype) args)
  | E_GenFunCall sn args => E_GenFunCall sn (map (replace_cfun_call_by_match snr cases bts rtype) args)
  | E_ConsFunCall sn e' args =>
    if (eq_ScopedName snr sn)
    then E_Match (unscope sn) e' (combine args bts) cases rtype
    else E_ConsFunCall sn (replace_cfun_call_by_match snr cases bts rtype e') (map (replace_cfun_call_by_match snr cases bts rtype) args)
  | E_Match qn e' bs cs rtype' =>
    E_Match qn
            (replace_cfun_call_by_match snr cases bts rtype e')
            (map (fun exp_typ => (replace_cfun_call_by_match snr cases bts rtype (fst exp_typ), snd exp_typ)) bs)
            (map (fun sn_exp => (fst sn_exp, replace_cfun_call_by_match snr cases bts rtype (snd sn_exp))) cs)
            rtype'
  | E_CoMatch qn bs cases' =>
    E_CoMatch qn
              (map (fun exp_typ => (replace_cfun_call_by_match snr cases bts rtype (fst exp_typ), snd exp_typ)) bs)
              (map (fun sn_exp => (fst sn_exp, replace_cfun_call_by_match snr cases bts rtype (snd sn_exp))) cases')
  | E_Let e1 e2 => E_Let (replace_cfun_call_by_match snr cases bts rtype e1) (replace_cfun_call_by_match snr cases bts rtype e2)
  end.

Definition contains_no_local_cfun_call (qn: QName) (e: expr): Prop :=
  forall (e_sub e_arg : expr) (args : list expr),
    subterm e_sub e -> e_sub <> E_ConsFunCall (local qn) e_arg args.

Inductive Exactly_once {A : Type}: (A -> Prop) -> (A -> Prop) -> list A -> Prop :=
| Exactly_once_here: forall (a : A) (ls : list A) (P nP: A -> Prop),
    Forall (fun a => nP a) ls ->
    P a ->
    Exactly_once P nP (a :: ls)
| Exactly_once_there: forall (a : A) (ls : list A) (P nP: A -> Prop),
    Exactly_once P nP ls ->
    nP a ->
    Exactly_once P nP (a :: ls).

Inductive contains_one_local_cfun_call: QName ->
                                        expr ->
                                        Prop :=
| contains_one_local_cfun_call_Constr : forall qn n es,
    contains_one_local_cfun_call_list qn es ->
    contains_one_local_cfun_call qn (E_Constr n es)
| contains_one_local_cfun_call_DestrCall_e :
    forall qn n e es,
      contains_one_local_cfun_call qn e ->
      Forall (contains_no_local_cfun_call qn) es ->
      contains_one_local_cfun_call qn (E_DestrCall n e es)
| contains_one_local_cfun_call_DestrCall_es :
    forall qn n e es,
      contains_no_local_cfun_call qn e ->
      contains_one_local_cfun_call_list qn es ->
      contains_one_local_cfun_call qn (E_DestrCall n e es)
| contains_one_local_cfun_call_FunCall :
    forall qn n es,
      contains_one_local_cfun_call_list qn es ->
      contains_one_local_cfun_call qn (E_FunCall n es)
| contains_one_local_cfun_call_GenFunCall :
    forall qn n es,
      contains_one_local_cfun_call_list qn es ->
      contains_one_local_cfun_call qn (E_GenFunCall n es)
| contains_one_local_cfun_call_ConsFunCall_e :
    forall qn n e es,
      n <> local qn ->
      contains_one_local_cfun_call qn e ->
      Forall (contains_no_local_cfun_call qn) es ->
      contains_one_local_cfun_call qn (E_ConsFunCall n e es)
| contains_one_local_cfun_call_ConsFunCall_es :
    forall qn n e es,
      n <> local qn ->
      contains_no_local_cfun_call qn e ->
      contains_one_local_cfun_call_list qn es ->
      contains_one_local_cfun_call qn (E_ConsFunCall n e es)
| contains_one_local_cfun_call_ConsFunCall_here :
    forall qn e es,
      contains_no_local_cfun_call qn e ->
      Forall (contains_no_local_cfun_call qn) es ->
      contains_one_local_cfun_call qn (E_ConsFunCall (local qn) e es)
| contains_one_local_cfun_call_Match_e :
    forall qn q e bs cases t,
      contains_one_local_cfun_call qn e ->
      Forall (contains_no_local_cfun_call qn) (map fst bs) ->
      Forall (contains_no_local_cfun_call qn) (map snd cases) ->
      contains_one_local_cfun_call qn (E_Match q e bs cases t)
| contains_one_local_cfun_call_Match_bs :
    forall qn q e bs cases t,
      contains_no_local_cfun_call qn e ->
      contains_one_local_cfun_call_list qn (map fst bs) ->
      Forall (contains_no_local_cfun_call qn) (map snd cases) ->
      contains_one_local_cfun_call qn (E_Match q e bs cases t)
| contains_one_local_cfun_call_Match_cases :
    forall qn q e bs cases t,
      contains_no_local_cfun_call qn e ->
      Forall (contains_no_local_cfun_call qn) (map fst bs) ->
      contains_one_local_cfun_call_list qn (map snd cases) ->
      contains_one_local_cfun_call qn (E_Match q e bs cases t)
| contains_one_local_cfun_call_CoMatch_bs :
    forall qn q bs cocases,
      contains_one_local_cfun_call_list qn (map fst bs) ->
      Forall (contains_no_local_cfun_call qn) (map snd cocases) ->
      contains_one_local_cfun_call qn (E_CoMatch q bs cocases)
| contains_one_local_cfun_call_CoMatch_cocases :
    forall qn q bs cocases,
      Forall (contains_no_local_cfun_call qn) (map fst bs) ->
      contains_one_local_cfun_call_list qn (map snd cocases) ->
      contains_one_local_cfun_call qn (E_CoMatch q bs cocases)
| contains_one_local_cfun_call_Let_e1 :
    forall qn e1 e2,
      contains_one_local_cfun_call qn e1 ->
      contains_no_local_cfun_call qn e2 ->
      contains_one_local_cfun_call qn (E_Let e1 e2)
| contains_one_local_cfun_call_Let_e2 :
    forall qn e1 e2,
      contains_no_local_cfun_call qn e1 ->
      contains_one_local_cfun_call qn e2 ->
      contains_one_local_cfun_call qn (E_Let e1 e2)
with contains_one_local_cfun_call_list : QName -> list expr -> Prop :=
| contains_one_local_cfun_call_list_here: forall (qn : QName) (e : expr) (ls : list expr),
    Forall (fun e => contains_no_local_cfun_call qn e) ls ->
    contains_one_local_cfun_call qn e ->
    contains_one_local_cfun_call_list qn (e :: ls)
| contains_one_local_cfun_call_list_there: forall (qn : QName) (e : expr) (ls : list expr),
    contains_one_local_cfun_call_list qn ls ->
    contains_no_local_cfun_call qn e ->
    contains_one_local_cfun_call_list qn (e :: ls).

Inductive inline_ordered_cfun_1 : cfun_bods -> Prop :=
| inline_ordered_cfun_1_nil: inline_ordered_cfun_1 []
| inline_ordered_cfun_1_cons:
    forall (bods: cfun_bods) (qn : QName) (cs : cfun_bod),
      inline_ordered_cfun_1 bods ->
      Forall (fun case =>
                contains_no_local_cfun_call qn (snd case))
             cs ->
      inline_ordered_cfun_1 ( (qn, cs) :: bods).

Lemma inline_ordered_cfun_1_forall : forall (bods : cfun_bods),
    inline_ordered_cfun_1 bods
    <->
    Forall (fun (x: cfun_bod_named) =>
              Forall
                (fun case => contains_no_local_cfun_call (fst x) (snd case))
                (snd x))
           bods.
Proof.
  intros bods; split; intros.
  -induction H; subst; try apply Forall_nil.
   apply Forall_cons; try assumption.
  -induction bods; try apply inline_ordered_cfun_1_nil.
   inversion H; subst. destruct a.
   apply inline_ordered_cfun_1_cons; try assumption.
   apply IHbods; assumption.
Qed.

Inductive inline_ordered_cfun_2 : cfun_bods -> Prop :=
| inline_ordered_cfun_2_nil: inline_ordered_cfun_2 []
| inline_ordered_cfun_2_cons:
        forall (bods: cfun_bods) (qn : QName) (cs : cfun_bod),
      inline_ordered_cfun_2 bods ->
      Forall (fun bod_named =>
                Forall (fun case =>
                          contains_no_local_cfun_call qn (snd case))
                       (snd bod_named)
             ) bods ->
      inline_ordered_cfun_2 ( (qn, cs) :: bods).

Inductive inline_ordered_cfun: cfun_bods -> Prop :=
| inline_ordered_cfun_nil: inline_ordered_cfun []
| inline_ordered_cfun_cons:
    forall (bods: cfun_bods) (qn : QName) (cs : cfun_bod),
      inline_ordered_cfun bods ->
      Forall (fun bod_named =>
                Forall (fun case =>
                          contains_no_local_cfun_call qn (snd case))
                       (snd bod_named)
             ) bods ->
      Forall (fun case =>
                contains_no_local_cfun_call qn (snd case))
             cs ->
      inline_ordered_cfun ( (qn, cs) :: bods).

Lemma inline_ordered_cfun_combine : forall (bods : cfun_bods),
    inline_ordered_cfun_1 bods ->
    inline_ordered_cfun_2 bods ->
    inline_ordered_cfun bods.
Proof.
  intros. induction bods; try apply inline_ordered_cfun_nil.
  destruct a as [qn cs].
  inversion H; inversion H0; subst.
  apply inline_ordered_cfun_cons; try assumption.
  apply IHbods; try assumption.
Qed.

Fixpoint replace_local_cfun_calls (cfuns: cfun_bods) (sigs: cfun_sigs) (e : expr) : expr :=
  match cfuns with
  | [] => e
  | (bod :: bods) =>
    match sigs with
    | [] => e
    | (sig :: sigs) =>
      replace_local_cfun_calls
        bods sigs
        (replace_cfun_call_by_match (local (fst bod)) (snd bod) (snd (fst sig)) (snd sig) e)
    end
  end.

Hint Immediate in_eq.
Hint Immediate in_cons.
Hint Constructors inline_ordered_cfun.

Lemma inline_ordered_cfun_sub: forall (tot sub : cfun_bods),
    inline_ordered_cfun tot ->
    sublist sub tot ->
    inline_ordered_cfun sub.
Proof.
  intros tot sub H_inline H_sub.
  gen_induction sub tot; inversion H_sub; subst; auto.
  - inversion H_inline; subst. apply IHtot with (sub := sub) in H2; auto.
  - inversion H_inline; subst. apply IHtot with (sub := sub0) in H2; auto.
    apply inline_ordered_cfun_cons; auto.
    apply Forall_sublist with (ts := tot); auto.
Qed.

Lemma contains_no_local_cfun_call_sub: forall (e e_sub : expr) (qn : QName),
    contains_no_local_cfun_call qn e ->
    subterm e_sub e ->
    contains_no_local_cfun_call qn e_sub.
Proof.
  intros e e_sub qn H H0.
  unfold contains_no_local_cfun_call in *.
  intros. apply H. subterm_tac.
Qed.

Lemma contains_one_and_no_local_cfun_absurd: forall (e: expr) (qn : QName),
    ~ (contains_one_local_cfun_call qn e /\ contains_no_local_cfun_call qn e).
Proof.
  intros e qn.
  intro H. inversion H; clear H.
  induction e using expr_strong_ind; inversion H0; subst;
    try
      match goal with
    | [ H: Forall _ ?ls, H_ls: contains_one_local_cfun_call_list ?qn ?ls |- _ ] =>
      assert (H_one: exists x, In x ls /\ contains_one_local_cfun_call qn x);
        [> clear - H_ls; induction ls as [| head tail]; inversion H_ls; subst;
         [> exists head; auto
            | match goal with
              | [ H_tail: contains_one_local_cfun_call_list qn tail |- _ ] =>
                apply IHtail in H_tail; inversion H_tail as [x H_tail']; inversion H_tail'; eauto
              end
         ]
        |];
        assert (H_none: forall x, In x ls -> contains_no_local_cfun_call qn x);
        [> match goal with
           | [ H: contains_no_local_cfun_call qn _ |- _ ] =>
             clear - H; intros; apply contains_no_local_cfun_call_sub with (e_sub := x) in H; auto;
             subterm_tac; direct_subterm_tac
           end
        |];
        clear - H_one H_none H;
        inversion_clear H_one; inversion_clear H0; induction ls; inversion H1; inversion H; subst;
          [> IH_tac; apply H_none; auto
          |  apply IHls; auto
          ]
      end;
    try
      ( apply contains_no_local_cfun_call_sub with (e_sub := e) in H1; auto;
        subterm_tac; direct_subterm_tac);
    try
      match goal with
    | [ H: Forall _ (map _ ?ls), H_ls: contains_one_local_cfun_call_list ?qn (map snd ?ls) |- _ ] =>
      assert (H_one: exists x, In x (map snd ls) /\ contains_one_local_cfun_call qn x);
        [> clear - H_ls; induction ls as [| [_x head] tail]; inversion H_ls; subst; simpl;
         [> exists head; auto
            | match goal with
              | [ H_tail: contains_one_local_cfun_call_list qn (map snd tail) |- _ ] =>
                apply IHtail in H_tail; inversion H_tail as [x H_tail']; inversion H_tail'; eauto
              end
         ]
        |];
        assert (H_none: forall x, In x (map snd ls) -> contains_no_local_cfun_call qn x);
        [> match goal with
           | [ H: contains_no_local_cfun_call qn ?e |- _ ] =>
             match e with
             | context [ls] => idtac
             end;
             clear - H; intros; apply contains_no_local_cfun_call_sub with (e_sub := x) in H; auto;
             subterm_tac; direct_subterm_tac
           end
        |];
        clear - H_one H_none H;
        inversion_clear H_one;
        match goal with
        | [ Hp: _ /\ _ |- _ ] =>
          inversion_clear Hp
        end; induction ls;
          match goal with
          | [ Hin: In ?x _, Hx: contains_one_local_cfun_call _ ?x |- _ ] =>
            inversion Hin; inversion H; subst
          end;
          [> IH_tac; apply H_none; auto
          |  match goal with
             | [ IH: context [In ?x _ -> False] |- _ ] =>
               apply IH; simpl in H_none; auto
             end
          ]
      end;
    try
      match goal with
    | [ H: Forall _ (map _ ?ls), H_ls: contains_one_local_cfun_call_list ?qn (map fst ?ls) |- _ ] =>
      assert (H_one: exists x, In x (map fst ls) /\ contains_one_local_cfun_call qn x);
        [> clear - H_ls; induction ls as [| [head _x] tail]; inversion H_ls; subst; simpl;
         [> exists head; auto
            | match goal with
              | [ H_tail: contains_one_local_cfun_call_list qn (map fst tail) |- _ ] =>
                apply IHtail in H_tail; inversion H_tail as [x H_tail']; inversion H_tail'; eauto
              end
         ]
        |];
        assert (H_none: forall x, In x (map fst ls) -> contains_no_local_cfun_call qn x);
        [> match goal with
           | [ H: contains_no_local_cfun_call qn _ |- _ ] =>
             clear - H; intros; apply contains_no_local_cfun_call_sub with (e_sub := x) in H; auto;
             subterm_tac; direct_subterm_tac
           end
        |];
        clear - H_one H_none H;
        inversion_clear H_one;
        match goal with
        | [ Hp: _ /\ _ |- _ ] =>
          inversion_clear Hp
        end; induction ls;
          match goal with
          | [ Hin: In ?x _, Hx: contains_one_local_cfun_call _ ?x |- _ ] =>
            inversion Hin; inversion H; subst
          end;
          [> IH_tac; apply H_none; auto
          |  match goal with
             | [ IH: context [In ?x _ -> False] |- _ ] =>
               apply IH; simpl in H_none; auto
             end
          ]
    end.
  - unfold contains_no_local_cfun_call in H1.
    specialize (H1 (E_ConsFunCall (local qn) e ls) e ls).
    apply H1; auto. subterm_tac.
  - apply IHe1; auto; apply contains_no_local_cfun_call_sub with (e_sub := e1) in H1; auto;
    subterm_tac; direct_subterm_tac.
  - apply IHe2; auto; apply contains_no_local_cfun_call_sub with (e_sub := e2) in H1; auto;
      subterm_tac; direct_subterm_tac.
Qed.

Lemma contains_one_and_no_local_cfun_absurd_list: forall (qn: QName) (ls : list expr),
    ~ (Forall (contains_no_local_cfun_call qn) ls /\ contains_one_local_cfun_call_list qn ls).
Proof.
  intros. intro H. inversion H as [Hn Hy].
  induction ls; inversion Hy; subst.
  - inversion Hn; subst. pose proof contains_one_and_no_local_cfun_absurd as Hx.
    specialize (Hx a qn).
    apply Hx; auto.
  - apply IHls; auto; try Forall_tail_tac. split; auto; Forall_tail_tac.
Qed.

Lemma contains_one_local_cfun_call_list_In: forall (qn : QName) (ls : list expr),
    contains_one_local_cfun_call_list qn ls ->
    exists x, In x ls /\ contains_one_local_cfun_call qn x.
Proof.
  intros qn ls H.
  induction ls; inversion H; subst; eauto.
  apply IHls in H3. inversion H3; inversion H0; eauto.
Qed.

Lemma contains_one_local_cfun_call_implies_subterm: forall (e e_sub : expr) (qn : QName),
    contains_one_local_cfun_call qn e ->
    subterm e_sub e ->
    (contains_one_local_cfun_call qn e_sub -> exists (e_arg: expr)(args: list expr), subterm (E_ConsFunCall (local qn) e_arg args) e_sub).
Proof.
  intros e e_sub qn H_one H_sub H_one_sub;
  induction e_sub using expr_strong_ind;
    try ((let foo :=
        let sub := constr:(fun e_arg args => E_ConsFunCall (local qn) e_arg args)
        in match goal with
        | [  |- context [subterm _ ?tot] ] =>
          match tot with
          | E_DestrCall ?sn ?e ?ls =>
            exists_context_replace
              (fun e_arg args => subterm (sub e_arg args) e
                              \/ (exists x, In x ls /\ subterm (sub e_arg args) x))
          | E_FunCall ?n ?ls =>
            exists_context_replace
              (fun e_arg args => exists x, In x ls /\ subterm (sub e_arg args) x)
          | E_GenFunCall ?sn ?ls =>
            exists_context_replace
              (fun e_arg args => exists x, In x ls /\ subterm (sub e_arg args) x)
          | E_Match ?qn ?e ?bs ?cs ?rt =>
            exists_context_replace
              (fun e_arg args => subterm (sub e_arg args) e
                              \/ (exists x, In x (map fst bs) /\ subterm (sub e_arg args) x)
                              \/ (exists x, In x (map snd cs) /\ subterm (sub e_arg args) x))
          | E_CoMatch ?qn ?bs ?ccs =>
            exists_context_replace
              (fun e_arg args => (exists x, In x (map fst bs) /\ subterm (sub e_arg args) x)
                              \/ (exists x, In x (map snd ccs) /\ subterm (sub e_arg args) x))
          | E_Let ?e1 ?e2 =>
            exists_context_replace
              (fun e_arg args => subterm (sub e_arg args) e1
                              \/ subterm (sub e_arg args) e2)
          end
        end
    in foo); [> solve [subterm_reduce_tac] |]).
  - inversion H_one_sub.
  - assert (H_sub_ls': forall x, In x ls -> subterm x (E_Constr n ls));
        [> clear; intros; subterm_tac; direct_subterm_tac |].
      assert (H_sub_ls: forall x, In x ls -> subterm x e);
        [> clear - H_sub H_sub_ls'; intros x H_in;
         apply H_sub_ls' in H_in; subterm_tac |]; clear H_sub_ls' H_sub.
      inversion H_one_sub; subst.
      assert (H_ex: exists x,  In x ls /\ exists e_arg args, subterm (E_ConsFunCall (local qn) e_arg args) x).
      { clear H_one_sub; induction ls; inversion H2; subst.
        - inversion H; subst. eexists.
          esplit; try eapply H3; eauto.
        - match goal with
          | [  |- exists x, In x (?a :: ?ls) /\ ?P ] =>
            assert (Hx: (exists x, In x ls /\ P) -> exists x, In x (a :: ls) /\ P)
          end;
          [> intros; inversion H0; inversion H1; eauto |].
          apply Hx. IH_tac (try Forall_tail_tac; auto).
      }
      inversion H_ex as [x [H_in [e_arg [args H_sub]]]]. exists e_arg; exists args.
      apply Sub_Trans with (e2 := x); auto. direct_subterm_tac.
  - clear H0.
    inversion H_one_sub; subst.
    + assert (subterm e_sub e);
        [>
         match goal with
         | [ H: subterm ?m ?e |- subterm ?sub ?e ] =>
           assert (subterm sub m); [> subterm_tac; direct_subterm_tac |]
         end; subterm_tac
        |].
      apply IHe_sub in H0; auto.
      double_exists H0. left; auto.
    + apply contains_one_local_cfun_call_list_In in H5; inversion H5. inversion_clear H0.
      assert (subterm x e).
      match goal with
      | [ H: subterm ?m ?e |- subterm ?sub ?e ] =>
        assert (subterm sub m);  [> subterm_tac; direct_subterm_tac |]
      end; subterm_tac.
      clear - H H1 H2 H0.
      induction ls; inversion H1; subst.
      * inversion H; subst. apply H5 in H0; auto.
        inversion H0 as [xx [y Hxx]].
        exists xx; exists y; right; exists x; auto.
      * IH_adapter IHls ltac:(auto; Forall_tail_tac).
        clear; intro; double_exists H; inversion H; auto;
         right; double_exists H0; inversion H0; auto.
  - clear H0.
    inversion_clear H_one_sub. apply contains_one_local_cfun_call_list_In in H0; inversion_clear H0 as [x [H_in H_one_x]].
    assert (H_sub_x: subterm x (E_FunCall n ls)); [> subterm_tac; direct_subterm_tac |].
    assert (H_one_sub: subterm x e); [> subterm_tac |]; clear H_sub_x H_sub.
    induction ls; inversion H_in; subst.
    + inversion H; subst.
      apply H2 in H_one_sub; auto.
      double_exists H_one_sub; exists x; auto.
    + IH_adapter IHls ltac:(auto; Forall_tail_tac).
      clear; intro H; double_exists H; inversion H; split; auto.
  - destruct (eq_ScopedName (local qn) sn) eqn:E;
      [> apply eq_ScopedName_eq in E; rewrite E;
       do 2 eexists; eapply Sub_Refl |].
    exists_context_replace
      (fun e_arg args => subterm (E_ConsFunCall (local qn) e_arg args) e_sub \/
                      exists x, In x ls /\ subterm (E_ConsFunCall (local qn) e_arg args) x);
      [> subterm_reduce_tac |]; clear H0.
    inversion H_one_sub; subst.
    + assert (subterm e_sub e);
        [> apply subterm_trans with (e2 := E_ConsFunCall sn e_sub ls); auto;
         subterm_tac; direct_subterm_tac |].
      apply IHe_sub in H0; auto.
      double_exists H0; auto.
    + apply contains_one_local_cfun_call_list_In in H6; inversion_clear H6 as [x [H_in H_one_x]].
      assert (H_sub_x: subterm x e); [> assert (Hx: subterm x (E_ConsFunCall sn e_sub ls)); subterm_tac; direct_subterm_tac |]; clear H_sub H_one_sub.
      induction ls; inversion H_in; subst.
      * inversion H; subst. apply H2 in H_sub_x; auto.
        double_exists H_sub_x; right; eauto.
      * IH_adapter IHls ltac:(auto; Forall_tail_tac).
        clear; intro H; double_exists H; inversion H; auto;
          right; double_exists H0; inversion H0; auto.
    + let Hf := fresh
      in match goal with
         | [ H: eq_ScopedName ?sn ?sn = false |- _ ] =>
           assert (Hf: sn = sn); [> reflexivity | apply eq_ScopedName_eq in Hf; rewrite H in Hf; inversion Hf ]
         end.
  - clear H0.
    inversion_clear H_one_sub. apply contains_one_local_cfun_call_list_In in H0; inversion_clear H0 as [x [H_in H_one_x]].
    assert (H_sub_x: subterm x e); [> subterm_trans_tac; subterm_tac; direct_subterm_tac |]; clear H_sub.
    induction ls; inversion H_in; subst.
    + inversion H; subst. apply H2 in H_sub_x; auto.
      double_exists H_sub_x; eauto.
    + IH_adapter IHls ltac:(auto; Forall_tail_tac).
      clear; intro H; double_exists H; inversion H; split; auto.
  - clear H1. inversion_clear H_one_sub.
    + assert (H_sub_e: subterm e_sub e); [> subterm_trans_tac; subterm_tac; direct_subterm_tac |].
      apply IHe_sub in H_sub_e; auto.
      double_exists H_sub_e; auto.
    + apply contains_one_local_cfun_call_list_In in H2; inversion_clear H2 as [x [H_in H_one_x]].
      assert (H_sub_x: subterm x e); [> subterm_trans_tac; subterm_tac; direct_subterm_tac |].
      clear H_sub; induction es; inversion H_in; destruct a; simpl in *; subst.
      * inversion_clear H0; apply H2 in H_sub_x; auto;
          double_exists H_sub_x; eauto.
      * IH_adapter IHes ltac:(auto; Forall_tail_tac).
        clear; intro H; double_exists H; inversion H as [H0 | [H0 | H0]]; auto;
        right; left; double_exists H0; inversion H0; auto.
    + apply contains_one_local_cfun_call_list_In in H3; inversion_clear H3 as [x [H_in H_one_x]].
      assert (H_sub_x: subterm x e); [> subterm_trans_tac; subterm_tac; direct_subterm_tac |].
      clear H_sub; induction ls; inversion H_in; destruct a; simpl in *; subst.
      * inversion_clear H; apply H3 in H_sub_x; auto;
          double_exists H_sub_x; eauto.
      * IH_adapter IHls ltac:(auto; Forall_tail_tac).
        clear; intro H; double_exists H; inversion H as [H0 | [H0 | H0]]; auto;
        right; right; double_exists H0; inversion H0; auto.
  - clear H1. inversion_clear H_one_sub.
    + apply contains_one_local_cfun_call_list_In in H1; inversion_clear H1 as [x [H_in H_one_x]].
      assert (H_sub_x: subterm x e); [> subterm_trans_tac; subterm_tac; direct_subterm_tac |].
      clear H_sub; induction es; inversion H_in; destruct a; simpl in *; subst.
      * inversion_clear H0; apply H1 in H_sub_x; auto;
          double_exists H_sub_x; eauto.
      * IH_adapter IHes ltac:(auto; Forall_tail_tac).
        clear; intro H; double_exists H; inversion H; auto;
        left; double_exists H0; inversion H0; auto.
    + apply contains_one_local_cfun_call_list_In in H2; inversion_clear H2 as [x [H_in H_one_x]].
      assert (H_sub_x: subterm x e); [> subterm_trans_tac; subterm_tac; direct_subterm_tac |].
      clear H_sub; induction ls; inversion H_in; destruct a; simpl in *; subst.
      * inversion_clear H; apply H2 in H_sub_x; auto;
          double_exists H_sub_x; eauto.
      * IH_adapter IHls ltac:(auto; Forall_tail_tac).
        clear; intro H; double_exists H; inversion H; auto;
        right; double_exists H0; inversion H0; auto.
  - clear H. inversion_clear H_one_sub.
    + assert (subterm e_sub1 e); [> subterm_trans_tac; subterm_tac; direct_subterm_tac |];
      apply IHe_sub1 in H1; auto;
        double_exists H1; auto.
    + assert (subterm e_sub2 e); [> subterm_trans_tac; subterm_tac; direct_subterm_tac |];
      apply IHe_sub2 in H1; auto;
        double_exists H1; auto.
Qed.

Lemma contains_one_local_cfun_call_subterms_at_most_one_list_helper:
  forall (ls : list expr) (e_sub : expr) (qn : QName),
    Forall
      (fun e : expr =>
         contains_one_local_cfun_call qn e ->
         subterm e_sub e -> contains_one_local_cfun_call qn e_sub \/ contains_no_local_cfun_call qn e_sub) ls ->
    forall e : expr,
      subterm e_sub e ->
      In e ls ->
      contains_one_local_cfun_call_list qn ls ->
      contains_one_local_cfun_call qn e_sub \/ contains_no_local_cfun_call qn e_sub.
Proof.
  intros ls e_sub qn H e2 H0 H4 H2.
  induction ls; inversion H2; subst.
  * inversion H4; subst.
    -- inversion H; subst. apply H5; auto.
    -- right. apply contains_no_local_cfun_call_sub with (e := e2); auto.
       clear - H1 H6. induction ls; inversion H1; subst.
       ++ inversion H6; auto.
       ++ IH_tac Forall_tail_tac.
  * inversion H4; subst.
    -- right. apply contains_no_local_cfun_call_sub with (e := e2); auto.
    -- IH_tac Forall_tail_tac.
Qed.

Lemma contains_one_local_cfun_call_subterms_at_most_one: forall (e e_sub: expr) (qn: QName),
    contains_one_local_cfun_call qn e ->
    subterm e_sub e ->
    contains_one_local_cfun_call qn e_sub \/ contains_no_local_cfun_call qn e_sub.
Proof.
  intros e e_sub qn H_one H_sub.
  induction e using expr_strong_ind; inversion H_sub; subst; auto.
  - inversion H0.
  - inversion H1; subst. inversion_clear H_one.
    apply contains_one_local_cfun_call_subterms_at_most_one_list_helper with (ls := ls) (e := e2); auto.
  - inversion H1; subst; inversion_clear H_one.
    + apply IHe; auto.
    + right. apply  contains_no_local_cfun_call_sub with (e := e); auto.
    + clear - H4 H3 H0.
      induction ls; inversion H4; subst.
      * inversion H3; subst. right; apply contains_no_local_cfun_call_sub with (e := e2); auto.
      * IH_tac Forall_tail_tac.
    + apply contains_one_local_cfun_call_subterms_at_most_one_list_helper with (ls := ls) (e := e2); auto.
  - inversion H1; subst; inversion_clear H_one.
    apply contains_one_local_cfun_call_subterms_at_most_one_list_helper with (ls := ls) (e := e2); auto.
  - inversion H1; subst; inversion H_one; subst.
    (* subterm of e *)
    + apply IHe; auto.
    + right; apply contains_no_local_cfun_call_sub with (e := e); auto.
    + right; apply contains_no_local_cfun_call_sub with (e := e); auto.
    (* subterm inls *)
    + right. clear - H0 H9 H4.
      induction ls; inversion H4; subst.
      * inversion H9; subst. apply contains_no_local_cfun_call_sub with (e := e2); auto.
      * IH_tac Forall_tail_tac.
    + apply contains_one_local_cfun_call_subterms_at_most_one_list_helper with (ls := ls) (e := e2); auto.
    + clear - H4 H0 H8.
      induction ls; inversion H4; subst.
      * inversion H8; subst. right. apply contains_no_local_cfun_call_sub with (e := e2); auto.
      * IH_tac Forall_tail_tac.
  - inversion H1; subst; inversion_clear H_one.
    apply contains_one_local_cfun_call_subterms_at_most_one_list_helper with (ls := ls) (e := e2); auto.
  - inversion H2; inversion H_one; subst;
      try (right;
            match goal with
            | [ H_sub: subterm ?e_sub ?e1,
                       H_in: In ?e1 (map ?pr ?ls),
                             H_Forall: Forall (contains_no_local_cfun_call ?qn) (map ?pr ?ls) |- contains_no_local_cfun_call ?qn ?e_sub ] =>
              clear - H_sub H_in H_Forall;
              let rest := fresh "rest"
              in let ea := fresh "e"
                 in let ta := fresh "t"
                    in let a := fresh "a"
                       in induction ls as [| a rest]; inversion H_in; subst; try destruct a as [ea ta]; simpl in *;
                          [> inversion H_Forall; subst;
                           match type of ea with
                           | expr =>
                             apply contains_no_local_cfun_call_sub with (e := ea); auto
                           | _ =>
                             apply contains_no_local_cfun_call_sub with (e := ta); auto
                           end
                          | IH_tac Forall_tail_tac ]

            end).
    (* subterm of e *)
    + apply IHe; auto.
    + right; apply contains_no_local_cfun_call_sub with (e := e); auto.
    + right; apply contains_no_local_cfun_call_sub with (e := e); auto.
    (* subterm in bs (i.e. es) *)
    + clear - H0 H1 H5 H17.
      induction es; inversion H5; inversion H17; subst.
      * destruct a; simpl in *.
        inversion H0; subst. apply H3; auto.
      * destruct a; simpl in *.
        right. apply contains_no_local_cfun_call_sub with (e := e); auto.
      * clear - H6 H H1. right.
        induction es; inversion H; subst; destruct a; simpl in *.
        -- inversion H6; subst. apply contains_no_local_cfun_call_sub with (e := e); auto.
        -- IH_tac Forall_tail_tac.
      * IH_tac Forall_tail_tac.
    (* subterm in cs (i.e. ls) *)
    + clear - H H1 H5 H18.
      induction ls; inversion H5; inversion H18; subst.
      * destruct a; simpl in *.
        inversion H; subst. apply H3; auto.
      * destruct a; simpl in *.
        right. apply contains_no_local_cfun_call_sub with (e := e); auto.
      * clear - H6 H0 H1. right.
        induction ls; inversion H0; subst; destruct a; simpl in *.
        -- inversion H6; subst. apply contains_no_local_cfun_call_sub with (e := e); auto.
        -- IH_tac Forall_tail_tac.
      * IH_tac Forall_tail_tac.
  - inversion H2; inversion H_one; subst;
      try (right;
            match goal with
            | [ H_sub: subterm ?e_sub ?e1,
                       H_in: In ?e1 (map ?pr ?ls),
                             H_Forall: Forall (contains_no_local_cfun_call ?qn) (map ?pr ?ls) |- contains_no_local_cfun_call ?qn ?e_sub ] =>
              clear - H_sub H_in H_Forall;
              let rest := fresh "rest"
              in let ea := fresh "e"
                 in let ta := fresh "t"
                    in let a := fresh "a"
                       in induction ls as [| a rest]; inversion H_in; subst; try destruct a as [ea ta]; simpl in *;
                          [> inversion H_Forall; subst;
                           match type of ea with
                           | expr =>
                             apply contains_no_local_cfun_call_sub with (e := ea); auto
                           | _ =>
                             apply contains_no_local_cfun_call_sub with (e := ta); auto
                           end
                          | IH_tac Forall_tail_tac ]

            end).
    + clear - H0 H1 H5 H11. induction es; simpl in *; inversion H5; inversion_clear H11; subst.
      * destruct a; simpl in *. inversion H0; subst.
        apply H6; auto.
      * destruct a; simpl in *.
        right; apply contains_no_local_cfun_call_sub with (e := e); auto.
      * clear - H1 H H2. right.
        induction es; inversion H; destruct a; simpl in *; subst.
        -- inversion H2; subst. apply contains_no_local_cfun_call_sub with (e := e2); auto.
        -- IH_tac Forall_tail_tac.
      * IH_tac Forall_tail_tac.
    + clear - H H1 H5 H13. induction ls; simpl in *; inversion H5; inversion_clear H13; subst.
      * destruct a; simpl in *. inversion H; subst.
        apply H6; auto.
      * destruct a; simpl in *.
        right; apply contains_no_local_cfun_call_sub with (e := e); auto.
      * clear - H1 H0 H2. right.
        induction ls; inversion H0; destruct a; simpl in *; subst.
        -- inversion H2; subst. apply contains_no_local_cfun_call_sub with (e := e2); auto.
        -- IH_tac Forall_tail_tac.
      * IH_tac Forall_tail_tac.
  - inversion H0; inversion H_one; subst.
    + apply IHe1; auto.
    + right; apply contains_no_local_cfun_call_sub with (e := e1); auto.
    + right; apply contains_no_local_cfun_call_sub with (e := e2); auto.
    + apply IHe2; auto.
Qed.


Lemma subterm_implies_contains_one_local_cfun_call: forall (e e_sub : expr) (qn : QName),
    contains_one_local_cfun_call qn e ->
    subterm e_sub e ->
    (exists (e_arg: expr)(args: list expr), subterm (E_ConsFunCall (local qn) e_arg args) e_sub) ->
    contains_one_local_cfun_call qn e_sub.
Proof.
  intros e e_sub qn H_one H_sub H_sub_sub'.
  inversion_clear H_sub_sub' as [e_arg [args H_sub_sub]].
  assert (H_most: contains_one_local_cfun_call qn e_sub \/ contains_no_local_cfun_call qn e_sub);
    [> apply contains_one_local_cfun_call_subterms_at_most_one with (e := e); auto |].
  inversion H_most; auto.
  exfalso. apply contains_one_and_no_local_cfun_absurd
             with (qn := qn) (e := E_ConsFunCall (local qn) e_arg args); split.
  - apply contains_one_local_cfun_call_ConsFunCall_here.
    + apply contains_no_local_cfun_call_sub with (e := e_sub); auto;
        subterm_trans_tac; subterm_tac; direct_subterm_tac.
    + rewrite Forall_forall; intros.
      apply contains_no_local_cfun_call_sub with (e := e_sub); auto;
        subterm_trans_tac; subterm_tac; direct_subterm_tac.
  - apply contains_no_local_cfun_call_sub with (e := e_sub); auto.
Qed.

Lemma contains_no_local_cfun_call_direct_sub: forall (e : expr) (qn : QName),
    (forall (e_sub : expr), direct_subterm e_sub e -> contains_no_local_cfun_call qn e_sub) ->
    (forall (e_arg : expr) (args : list expr), e <> E_ConsFunCall (local qn) e_arg args) ->
    contains_no_local_cfun_call qn e.
Proof.
  intros e qn H_sub E.
  unfold contains_no_local_cfun_call; intros.
  inversion H; subst.
  - destruct e; intro E1; try solve [inversion E1].
    apply E in E1; auto.
  - intro E_sub.
    apply H_sub in H1. unfold contains_no_local_cfun_call in H1.
    apply H1 with (e_arg := e_arg) (args := args) in H0; auto.
Qed.

Lemma replace_cfun_call_by_match_creates_no_cfun_calls:
  forall (qn qn' : QName) (cases : list (ScopedName * expr)) (bts : list TypeName)(rtype : TypeName) (e : expr),
    contains_no_local_cfun_call qn e ->
    Forall (fun case => contains_no_local_cfun_call qn (snd case)) cases ->
    contains_no_local_cfun_call qn
                                (replace_cfun_call_by_match (local qn') cases bts rtype e).
Proof.
  intros qn qn' cases bts rtype e H_no H_cases.
  induction e using expr_strong_ind; simpl; auto.
  - assert (H_no_ls: forall x, In x ls -> contains_no_local_cfun_call qn x);
      [> intros; apply contains_no_local_cfun_call_sub with (e := E_Constr n ls); auto; subterm_tac; direct_subterm_tac |].
    clear H_no.
    apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
    intros. inversion_clear H0.
    induction ls; inversion H1; subst.
    + inversion H; subst. apply H3; auto.
    + apply IHls; auto. Forall_tail_tac.
  - assert (H_no_sub: contains_no_local_cfun_call qn e /\
                      forall x, In x ls -> contains_no_local_cfun_call qn x);
      [> split; intros; apply contains_no_local_cfun_call_sub with (e := E_DestrCall n e ls); auto; subterm_tac; direct_subterm_tac |].
    clear H_no.
    apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
    intros. inversion_clear H_no_sub as [H_no_e H_no_ls]; inversion_clear H0.
    + apply IHe; auto.
    + induction ls; inversion H1; subst.
      * inversion H; subst; apply H3; auto.
      * IH_tac ltac:(auto; Forall_tail_tac).
  - assert (H_no_ls: forall x, In x ls -> contains_no_local_cfun_call qn x);
      [> intros; apply contains_no_local_cfun_call_sub with (e := E_FunCall n ls); auto; subterm_tac; direct_subterm_tac |].
    clear H_no.
    apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
    intros. inversion_clear H0.
    induction ls; inversion H1; subst.
    + inversion H; subst. apply H3; auto.
    + apply IHls; auto. Forall_tail_tac.
  -
    match_destruct_tac.
    + match_destruct_tac.
      * name_eq_rewrite_tac; subst.
        destruct (eq_QName qn q) eqn:E_qn.
        -- name_eq_rewrite_tac; subst.
        unfold contains_no_local_cfun_call in H_no.
        specialize (H_no (E_ConsFunCall (local q) e ls) e ls).
        exfalso; apply H_no; auto; subterm_tac.
        --
      assert (H_no_sub: contains_no_local_cfun_call qn e /\
                        forall x, In x ls -> contains_no_local_cfun_call qn x);
        [> split; intros; apply contains_no_local_cfun_call_sub with (e := E_ConsFunCall (local q) e ls); auto; subterm_tac; direct_subterm_tac |].
      clear H_no.
      apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
      intros. inversion_clear H_no_sub as [H_no_e H_no_ls]; inversion_clear H0; auto.
      ++ clear H IHe; gen_induction bts ls; destruct bts; simpl in *; inversion H1; subst; auto.
         apply IHls with (bts := bts); auto; try Forall_tail_tac.
      ++ clear - H1 H_cases.
         induction cases; inversion H1; subst.
         ** inversion H_cases; auto.
         ** IH_tac Forall_tail_tac.
      * inversion E_match.
    + assert (E_sn: sn <> local qn');
      [> match_destruct_tac; intro E; inversion E; subst; name_refl_contradiction_tac |].
      assert (H_no_sub: contains_no_local_cfun_call qn e /\
                        forall x, In x ls -> contains_no_local_cfun_call qn x);
        [> split; intros; apply contains_no_local_cfun_call_sub with (e := E_ConsFunCall sn e ls); auto; subterm_tac; direct_subterm_tac |].
      destruct (eq_QName qn qn') eqn:E_qn.
      * clear H_no. name_eq_tac.
      apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E; contradiction].
      intros. inversion_clear H_no_sub as [H_no_e H_no_ls]; inversion_clear H0.
      -- apply IHe; auto.
      -- induction ls; inversion H1; subst.
        ++ inversion H; subst; apply H3; auto.
        ++ IH_tac ltac:(auto; Forall_tail_tac).
      * unfold contains_no_local_cfun_call; intros; intro E; subst.
        inversion H0; subst.
        ++ unfold contains_no_local_cfun_call in H_no.
           apply H_no with (e_sub := E_ConsFunCall (local qn) e ls) (e_arg := e) (args := ls); auto; subterm_tac.
        ++ inversion H_no_sub as [H_no_e H_no_ls]. inversion H2; subst.
           ** apply IHe in H_no_e. unfold contains_no_local_cfun_call in H_no_e.
              apply H_no_e with (e_arg := e_arg) (args := args) in H1; apply H1; auto.
           ** clear - H1 H5 H0 H H_no_ls.
              induction ls; inversion H5; subst.
              --- inversion H; subst. unfold contains_no_local_cfun_call at 2 in H4.
                  specialize H4 with (e_arg := e_arg) (args := args) (e_sub := E_ConsFunCall (local qn) e_arg args).
                  apply H4; auto.
              --- IH_tac (try Forall_tail_tac).
                  +++ subterm_trans_tac; auto; subterm_tac; direct_subterm_tac.
                  +++ intros; auto.
  - assert (H_no_ls: forall x, In x ls -> contains_no_local_cfun_call qn x); [> intros; apply contains_no_local_cfun_call_sub with (e := E_GenFunCall sn ls); auto; subterm_tac; direct_subterm_tac |].
    clear H_no.
    apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
    intros. inversion_clear H0.
    induction ls; inversion H1; subst.
    + inversion H; subst; apply H3; auto.
    + apply IHls; auto. Forall_tail_tac.
  - assert (H_no_sub: contains_no_local_cfun_call qn e /\
                      (forall x, In x (map fst es) -> contains_no_local_cfun_call qn x) /\
                      (forall x, In x (map snd ls) -> contains_no_local_cfun_call qn x));
      [> split; [> | split]; intros; apply contains_no_local_cfun_call_sub with (e := E_Match n e es ls tn); auto; subterm_tac; direct_subterm_tac |].
    clear H_no.
    apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
    intros. inversion_clear H_no_sub as [H_no_e [H_no_es H_no_ls]]; inversion_clear H1.
    + apply IHe; auto.
    + induction es; inversion H2.
      * inversion H0; subst. apply H5. destruct a; simpl in *; auto.
      * destruct a; simpl in *; apply IHes; auto; Forall_tail_tac.
    + induction ls; inversion H2.
      * inversion H; subst. apply H5. destruct a; simpl in *; auto.
      * destruct a; simpl in *; apply IHls; auto; Forall_tail_tac.
  - assert (H_no_sub: (forall x, In x (map fst es) -> contains_no_local_cfun_call qn x) /\
                      (forall x, In x (map snd ls) -> contains_no_local_cfun_call qn x));
      [> split; intros; apply contains_no_local_cfun_call_sub with (e := E_CoMatch n es ls); auto; subterm_tac; direct_subterm_tac |].
    clear H_no.
    apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
    intros. inversion_clear H_no_sub as [H_no_es H_no_ls]; inversion_clear H1.
    + induction es; inversion H2.
      * inversion H0; subst. apply H5. destruct a; simpl in *; auto.
      * destruct a; simpl in *; apply IHes; auto; Forall_tail_tac.
    + induction ls; inversion H2.
      * inversion H; subst. apply H5. destruct a; simpl in *; auto.
      * destruct a; simpl in *; apply IHls; auto; Forall_tail_tac.
  - assert (H_no_sub: contains_no_local_cfun_call qn e1 /\
                      contains_no_local_cfun_call qn e2);
      [> split; intros; apply contains_no_local_cfun_call_sub with (e := E_Let e1 e2); auto; subterm_tac; direct_subterm_tac |].
    clear H_no.
    apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
    intros; inversion_clear H_no_sub as [H_no_e1 H_no_e2]; inversion H; subst.
    + apply IHe1; auto.
    + apply IHe2; auto.
Qed.

Ltac contains_no_list_tac :=
  repeat match goal with
         | [ H: Forall (contains_no_local_cfun_call _) _ |- _ ] =>
           apply Forall_eta in H
         end;
  match goal with
  | [ H_case: Forall (fun x => contains_no_local_cfun_call ?qn (snd x)) ?cases,
              H3: In ?e_sub (map _ ?ls),
                  H11: Forall (fun x => contains_no_local_cfun_call ?qn x) ?ls
      |- contains_no_local_cfun_call ?qn ?e_sub ] =>
    clear - H_case H3 H11;
    induction ls; inversion H3; subst;
    [> inversion_clear H11; apply replace_cfun_call_by_match_creates_no_cfun_calls; auto
    |  IH_tac Forall_tail_tac]
  end.

Ltac contains_one_list_tac :=
      match goal with
      | [ H4: contains_one_local_cfun_call_list ?qn ?ls,
              H3: In ?e_sub (map (replace_cfun_call_by_match (local ?qn) ?cases ?bts ?rtype) ?ls),
                  H: Forall _ ?ls,
                     H_case: Forall (fun x => contains_no_local_cfun_call ?qn (snd x)) ?cases
          |- contains_no_local_cfun_call ?qn ?e_sub ] =>
      clear - H4 H3 H H_case;
      induction ls; inversion H3; inversion H4; subst;
      [> inversion H; subst; IH_tac
      |  apply replace_cfun_call_by_match_creates_no_cfun_calls; auto
      |  inversion H; subst;
         contains_no_list_tac
       |  IH_tac Forall_tail_tac
      ]
      end.

Ltac contains_no_list_pr_tac :=
  repeat match goal with
         | [ H: Forall (contains_no_local_cfun_call _) _ |- _ ] =>
           apply Forall_eta in H
         end;
  match goal with
  | [ H_in: In ?e_sub (map _ ?es),
            H_none: Forall (fun x => contains_no_local_cfun_call ?qn x) (map ?pr ?es),
                    H_case: Forall (fun c => contains_no_local_cfun_call ?qn (snd c)) ?cases
      |- _ ] =>
    clear - H_in H_none H_case;
    induction es; inversion H_in;
    [> inversion H_none; subst; apply replace_cfun_call_by_match_creates_no_cfun_calls; auto
    |  IH_tac Forall_tail_tac
    ]
  end.

Ltac contains_one_list_pr_tac :=
    match goal with
    | [ H_in: In ?e_sub (map ?pr (map _ ?es)),
              H_one: contains_one_local_cfun_call_list ?qn (map ?pr ?es),
                     IH: Forall _ (map _ ?es),
                         H_case: Forall (fun c => contains_no_local_cfun_call ?qn (snd c)) ?cases
        |- contains_no_local_cfun_call ?qn ?e_sub ] =>
      rewrite map_map in H_in; simpl in H_in;
        clear - H_in H_one IH H_case;
        induction es; inversion H_in; inversion H_one; subst;
          [> inversion IH; subst; IH_tac
          |  apply replace_cfun_call_by_match_creates_no_cfun_calls; auto
          |  contains_no_list_pr_tac
          |  IH_tac Forall_tail_tac
          ]
    end.

Lemma replace_cfun_call_by_match_removes_all_cfun_calls:
  forall (qn : QName) (cases : list (ScopedName * expr)) (bts : list TypeName)(rtype : TypeName) (e : expr),
    contains_one_local_cfun_call qn e ->
    Forall (fun case => contains_no_local_cfun_call qn (snd case)) cases ->
    contains_no_local_cfun_call qn
                                (replace_cfun_call_by_match (local qn) cases bts rtype e).
Proof.
  intros qn cases bts rtype e H_one H_case.
  induction e using expr_strong_ind;
    try
      (simpl; apply contains_no_local_cfun_call_direct_sub;
       [> intros;
        match goal with
        | [ H: direct_subterm _ _ |- _ ] => inversion H; inversion H_one; subst
        end
       |  solve [intros; intro E; inversion E]]).
  (* Constr *)
  - contains_one_list_tac.
  (* DestrCall *)
  - IH_tac.
  - apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
  - contains_no_list_tac.
  - contains_one_list_tac.
    (* FunCall *)
  - contains_one_list_tac.
  (* ConsFunCall *)
  - simpl. match_destruct_tac.
    + match_destruct_tac; [> | inversion E_match].
      name_eq_tac. apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E].
      intros. inversion H0; subst.
      * inversion H_one; subst; try contradiction.
        assumption.
      * inversion H_one; subst; try contradiction.
        clear - H3 H6.
        gen_induction bts ls; simpl in *; try contradiction.
        destruct bts; inversion H3.
        -- simpl in *; inversion H6; subst; auto.
        -- inversion H6; IH_auto_tac.
      * clear - H3 H_case; induction cases; inversion H3; subst.
        -- inversion H_case; subst; auto.
        -- IH_tac Forall_tail_tac.
    + assert (sn <> local qn);
        [> match_destruct_tac; intro E; inversion E; subst; name_refl_contradiction_tac |].
      apply contains_no_local_cfun_call_direct_sub;
        [> |  intros; intro E; inversion E; contradiction ].
      intros. inversion H1; inversion H_one; subst; try contradiction.
      * apply IHe; auto.
      * apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
      * contains_no_list_tac.
      * contains_one_list_tac.
  (* GenFunCall *)
  - contains_one_list_tac.
  (* Match *)
  - apply IHe; auto.
  - apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
  - apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
  - rewrite map_map in *; contains_no_list_pr_tac.
  - contains_one_list_pr_tac.
  - rewrite map_map in *; contains_no_list_pr_tac.
  - rewrite map_map in *; contains_no_list_pr_tac.
  - rewrite map_map in *; contains_no_list_pr_tac.
  - contains_one_list_pr_tac.
  (* CoMatch *)
  - contains_one_list_pr_tac.
  - rewrite map_map in *; contains_no_list_pr_tac.
  - rewrite map_map in *; contains_no_list_pr_tac.
  - contains_one_list_pr_tac.
  (* Let *)
  - apply IHe1; auto.
  - apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
  - apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
  - apply IHe2; auto.
Qed.

Definition contains_at_most_one_local_cfun_call (qn: QName) (e : expr) :=
  contains_no_local_cfun_call qn e \/
  contains_one_local_cfun_call qn e.

Definition contains_at_most_one_local_cfun_call_list (qn: QName) (l : list expr) :=
  Forall (contains_no_local_cfun_call qn) l \/
  contains_one_local_cfun_call_list qn l.

Ltac replace_keeps_different_map_list_tac :=
  match goal with
  | [ H: Forall (contains_no_local_cfun_call ?qn') ?ls |-
      Forall (contains_no_local_cfun_call ?qn') ?ls' ] =>
    rewrite map_map; simpl; rewrite <- Forall_map; rewrite <- Forall_map in H;
    match goal with
    | [ H': Forall ?P' ?es |- Forall ?Q' ?es ] =>
      match H' with
      | H =>
        apply Forall_impl with (P := P') (Q := Q'); auto;
        intros; apply replace_cfun_call_by_match_creates_no_cfun_calls; auto
      end
    end
  end.



Hint Resolve replace_cfun_call_by_match_creates_no_cfun_calls.

Ltac replace_keeps_different_list_tac :=
      match goal with
      | [ H_bts_len: forall e' ls0, subterm (E_ConsFunCall (local ?qn) e' ls0) ?e -> length ls0 = length ?bts,
            H: Forall (fun e => @?P' e -> @?Q' e) ?ls |- contains_one_local_cfun_call_list ?qn' (map ?rep ?ls) ] =>
        assert (Hx: Forall P' ls);
          [> apply Forall_forall; intros;
           match goal with
           | [ H_in: In ?x ?ls, H_sub: subterm (E_ConsFunCall ?sn ?e' ?ls0) ?x |- _ ] =>
             apply H_bts_len with (e' := e'); auto; subterm_trans_tac; subterm_tac; direct_subterm_tac
           end
          |
          pose proof (Forall_impl2 ls P' Q') as HF;
          simpl in *; apply HF  in H; auto;
          clear Hx HF
          ];
          match goal with
          | [ IH: Forall (fun e => contains_one_local_cfun_call ?qn' e -> contains_one_local_cfun_call ?qn' (?rep e)) ?ls,
                  H_one: contains_one_local_cfun_call_list ?qn' ?ls'
              |- contains_one_local_cfun_call_list ?qn' ?ls'' ] =>
            assert (E: ls = ls'); auto; try rewrite E in *; clear E;
              try (rewrite map_map; rewrite <- Forall_map in IH; simpl);
              match type of IH with
              | Forall _ ?es =>
                clear H_bts_len;
                induction es; inversion H_one; subst; simpl;
                  [> apply contains_one_local_cfun_call_list_here;
                   [> rewrite <- Forall_map;
                    match goal with
                    | [ Hx: Forall _ _ |- Forall ?Q' _ ] =>
                      try rewrite <- Forall_map in Hx;
                      match type of Hx with
                      | Forall ?P' es =>
                        solve [apply Forall_impl with (P := P'); auto]
                      end
                    end
                   |  inversion IH; auto
                   ]
                  |  apply contains_one_local_cfun_call_list_there; auto;
                     IH_tac try Forall_tail_tac
                  ]
              end
          end
      end.


Lemma replace_cfun_call_keeps_different_cfun_calls:
  forall (qn qn' : QName) (cases : list (ScopedName * expr)) (bts : list TypeName)(rtype : TypeName) (e : expr),
    qn <> qn' ->
    (forall e' ls, subterm (E_ConsFunCall (local qn) e' ls) e -> length ls = length bts) ->
    contains_one_local_cfun_call qn' e ->
    Forall (fun case => contains_no_local_cfun_call qn' (snd case)) cases ->
    contains_one_local_cfun_call qn'
                                (replace_cfun_call_by_match (local qn) cases bts rtype e).
Proof.
  intros qn qn' cases bts rtype e E_qn H_bts_len H_one H_case.
  induction e using expr_strong_ind; simpl.
  - inversion H_one.
  - apply contains_one_local_cfun_call_Constr; inversion_clear H_one. replace_keeps_different_list_tac.
  - inversion H_one; subst.
    + apply contains_one_local_cfun_call_DestrCall_e; auto.
      * apply IHe; auto.
        intros; apply H_bts_len with (e' := e').
        subterm_trans_tac; subterm_tac; direct_subterm_tac.
      * rewrite <- Forall_map.
      apply Forall_forall; intros x H_in;
        apply Forall_forall with (x := x) in H5; auto.
    + apply contains_one_local_cfun_call_DestrCall_es; auto.
      clear H_one.
      replace_keeps_different_list_tac.
  - apply contains_one_local_cfun_call_FunCall.
    inversion_clear H_one. replace_keeps_different_list_tac.
  - match_destruct_tac.
    + inversion H_one; subst.
      * apply contains_one_local_cfun_call_Match_e; auto.
        -- pose proof (map_combine_fst_sublist ls bts) as H_sub.
           apply Forall_sublist with (ts := ls); auto.
        -- rewrite <- Forall_map; auto.
      * apply contains_one_local_cfun_call_Match_bs; auto.
        -- rewrite map_fst_combine; auto.
           destruct sn; try solve [inversion E_match].
           name_eq_tac.
           apply H_bts_len with (e' := e); auto;
             subterm_tac.

           (*specialize (H_bts_len (E_ConsFunCall sn e ls) (Sub_Refl (E_ConsFunCall sn e ls))).
           inversion H_bts_len as [sn' [e'' [ls' H_len]]].*)

        -- rewrite <- Forall_map; auto.
      * name_eq_tac. contradiction.

    + assert (E_sn: sn <> local qn);
        [> match_destruct_tac; intro E; inversion E; subst; name_refl_contradiction_tac |].
      inversion_clear H_one.
      * apply contains_one_local_cfun_call_ConsFunCall_e; auto.
        -- apply IHe; auto.
           intros. apply H_bts_len with (e' := e').
           inversion_clear H3.
           ++ subterm_tac; direct_subterm_tac.
           ++ subterm_trans_tac. apply subterm_trans with (e2 := e); subterm_tac; auto; direct_subterm_tac.
        -- rewrite <- Forall_map;
             match goal with
             | [ H: Forall ?P' ?ls |- Forall ?Q' ?ls ] =>
               apply Forall_impl with (P := P') (Q := Q'); solve [auto]
             end.
      * apply contains_one_local_cfun_call_ConsFunCall_es; auto.
        replace_keeps_different_list_tac.
      * apply contains_one_local_cfun_call_ConsFunCall_here; auto.
        rewrite <- Forall_map;
        match goal with
        | [ H: Forall ?P' ?ls |- Forall ?Q' ?ls ] =>
          apply Forall_impl with (P := P') (Q := Q'); solve [auto]
        end.
  - apply contains_one_local_cfun_call_GenFunCall.
    inversion_clear H_one. replace_keeps_different_list_tac.
  - inversion_clear H_one.
    + apply contains_one_local_cfun_call_Match_e; auto; try replace_keeps_different_map_list_tac.
      apply IHe; auto;
      intros; apply H_bts_len with (e' := e');
      match goal with
      | [ H_sub: subterm (E_ConsFunCall ?sn ?e' ?ls) ?e_top |- _ ] =>
        inversion_clear H_sub;
          [> subterm_tac; direct_subterm_tac
          | subterm_trans_tac;
             apply subterm_trans with (e2 := e); subterm_tac; auto; direct_subterm_tac
          ]
      end.
    + apply contains_one_local_cfun_call_Match_bs; auto; try replace_keeps_different_map_list_tac.

      match goal with
        | [ H_bts_len: forall e' ls0, subterm (E_ConsFunCall ?sn e' ls0) ?e -> length ls0 = length ?bts,
              H: Forall (fun e => @?P' e -> @?Q' e) ?l |- contains_one_local_cfun_call_list ?qn' ?l' ] =>
          try (rewrite <- Forall_map in H; rewrite map_map; simpl in * );
            match goal with
            | [ H': Forall (fun e => @?P' e -> @?Q' e) ?ls |- contains_one_local_cfun_call_list ?qn (map ?rep ?ls) ] =>
              assert (Hx: Forall P' ls);
                [> apply Forall_forall; intros;
                 match goal with
                 | [ H_in: In ?x ?ls, H_sub: subterm (E_ConsFunCall ?sn ?e' ?ls0) ?x' |- _ ] =>
                   match x' with
                   | context [x] => idtac
                   end;
                   try (destruct x; simpl in * );
                   apply H_bts_len with (e' := e'); auto; subterm_trans_tac; subterm_tac
                 end
                |
                pose proof (Forall_impl2 ls P' Q') as HF;
                simpl in *; apply HF  in H; auto;
                clear Hx HF
                ]
            end
        end.
      * direct_subterm_tac.
      * clear H_bts_len;
          induction es; simpl in *; inversion H2; subst.
        -- apply contains_one_local_cfun_call_list_here.
           ++ rewrite <- Forall_map.
              rewrite <- Forall_map in H7;
                match type of H7 with
                | Forall ?P' _ =>
                  apply Forall_impl with (P := P'); auto
                end.
           ++ inversion H0; auto.
        -- apply contains_one_local_cfun_call_list_there; auto.
           IH_tac Forall_tail_tac.

    + apply contains_one_local_cfun_call_Match_cases; auto; try replace_keeps_different_map_list_tac.


      match goal with
        | [ H_bts_len: forall e' ls0, subterm (E_ConsFunCall ?sn e' ls0) ?e -> length ls0 = length ?bts,
              H: Forall (fun e => @?P' e -> @?Q' e) ?l |- contains_one_local_cfun_call_list ?qn' ?l' ] =>
          try (rewrite <- Forall_map in H; rewrite map_map; simpl in * );
            match goal with
            | [ H': Forall (fun e => @?P' e -> @?Q' e) ?ls |- contains_one_local_cfun_call_list ?qn (map ?rep ?ls) ] =>
              assert (Hx: Forall P' ls);
                [> apply Forall_forall; intros;
                 match goal with
                 | [ H_in: In ?x ?ls, H_sub: subterm (E_ConsFunCall ?sn ?e' ?ls0) ?x' |- _ ] =>
                   match x' with
                   | context [x] => idtac
                   end;
                   try (destruct x; simpl in * );
                   apply H_bts_len with (e' := e'); auto; subterm_trans_tac; subterm_tac
                 end
                |
                pose proof (Forall_impl2 ls P' Q') as HF;
                simpl in *; apply HF  in H; auto;
                clear Hx HF
                ]
            end
        end.
      * direct_subterm_tac.
      * clear H_bts_len;
          induction ls; simpl in *; inversion H3; subst.
        -- apply contains_one_local_cfun_call_list_here.
           ++ rewrite <- Forall_map.
              rewrite <- Forall_map in H7;
                match type of H7 with
                | Forall ?P' _ =>
                  apply Forall_impl with (P := P'); auto
                end.
           ++ inversion H; auto.
        -- apply contains_one_local_cfun_call_list_there; auto.
           IH_tac Forall_tail_tac.
  - inversion_clear H_one.
    + apply contains_one_local_cfun_call_CoMatch_bs; auto; try replace_keeps_different_map_list_tac.

      match goal with
        | [ H_bts_len: forall e' ls0, subterm (E_ConsFunCall ?sn e' ls0) ?e -> length ls0 = length ?bts,
              H: Forall (fun e => @?P' e -> @?Q' e) ?l |- contains_one_local_cfun_call_list ?qn' ?l' ] =>
          try (rewrite <- Forall_map in H; rewrite map_map; simpl in * );
            match goal with
            | [ H': Forall (fun e => @?P' e -> @?Q' e) ?ls |- contains_one_local_cfun_call_list ?qn (map ?rep ?ls) ] =>
              assert (Hx: Forall P' ls);
                [> apply Forall_forall; intros;
                 match goal with
                 | [ H_in: In ?x ?ls, H_sub: subterm (E_ConsFunCall ?sn ?e' ?ls0) ?x' |- _ ] =>
                   match x' with
                   | context [x] => idtac
                   end;
                   try (destruct x; simpl in * );
                   apply H_bts_len with (e' := e'); auto; subterm_trans_tac; subterm_tac
                 end
                |
                pose proof (Forall_impl2 ls P' Q') as HF;
                simpl in *; apply HF  in H; auto;
                clear Hx HF
                ]
            end
        end.
      * direct_subterm_tac.
      * clear H_bts_len;
          induction es; simpl in *; inversion H1; subst.
        -- apply contains_one_local_cfun_call_list_here.
           ++ rewrite <- Forall_map.
              rewrite <- Forall_map in H6;
                match type of H6 with
                | Forall ?P' _ =>
                  apply Forall_impl with (P := P'); auto
                end.
           ++ inversion H0; auto.
        -- apply contains_one_local_cfun_call_list_there; auto.
           IH_tac Forall_tail_tac.

    + apply contains_one_local_cfun_call_CoMatch_cocases; auto; try replace_keeps_different_map_list_tac.

      match goal with
        | [ H_bts_len: forall e' ls0, subterm (E_ConsFunCall ?sn e' ls0) ?e -> length ls0 = length ?bts,
              H: Forall (fun e => @?P' e -> @?Q' e) ?l |- contains_one_local_cfun_call_list ?qn' ?l' ] =>
          try (rewrite <- Forall_map in H; rewrite map_map; simpl in * );
            match goal with
            | [ H': Forall (fun e => @?P' e -> @?Q' e) ?ls |- contains_one_local_cfun_call_list ?qn (map ?rep ?ls) ] =>
              assert (Hx: Forall P' ls);
                [> apply Forall_forall; intros;
                 match goal with
                 | [ H_in: In ?x ?ls, H_sub: subterm (E_ConsFunCall ?sn ?e' ?ls0) ?x' |- _ ] =>
                   match x' with
                   | context [x] => idtac
                   end;
                   try (destruct x; simpl in * );
                   apply H_bts_len with (e' := e'); auto; subterm_trans_tac; subterm_tac
                 end
                |
                pose proof (Forall_impl2 ls P' Q') as HF;
                simpl in *; apply HF  in H; auto;
                clear Hx HF
                ]
            end
        end.
      * direct_subterm_tac.
      * clear H_bts_len;
          induction ls; simpl in *; inversion H2; subst.
        -- apply contains_one_local_cfun_call_list_here.
           ++ rewrite <- Forall_map.
              rewrite <- Forall_map in H6;
                match type of H6 with
                | Forall ?P' _ =>
                  apply Forall_impl with (P := P'); auto
                end.
           ++ inversion H; auto.
        -- apply contains_one_local_cfun_call_list_there; auto.
           IH_tac Forall_tail_tac.
  - inversion_clear H_one.
    + apply contains_one_local_cfun_call_Let_e1; auto.
      apply IHe1; auto.
      intros; apply H_bts_len with (e' := e');
        subterm_trans_tac; subterm_tac; direct_subterm_tac.
    + apply contains_one_local_cfun_call_Let_e2; auto.
      apply IHe2; auto.
      intros; apply H_bts_len with (e' := e');
        subterm_trans_tac; subterm_tac; direct_subterm_tac.
Qed.

Inductive cfun_sig_bod_paring: cfun_bods -> cfun_sigs -> Prop :=
| cfun_sig_bod_paring_nil: cfun_sig_bod_paring [] []
| cfun_sig_bod_paring_cons:
    forall (bods: cfun_bods) (sigs: cfun_sigs) (bod: cfun_bod) (sig_arg: list TypeName) (sig_rt: TypeName) (qn: QName),
      cfun_sig_bod_paring bods sigs ->
      cfun_sig_bod_paring ((qn, bod) :: bods)
                          ((qn, sig_arg, sig_rt) :: sigs).

Lemma replace_local_cfun_calls_creates_no_local_cfun_calls:
  forall (cfuns: cfun_bods) (sigs: cfun_sigs) (e: expr) (qn : QName),
    Forall (contains_no_local_cfun_call qn) (map snd (concat (map snd cfuns))) ->
    contains_no_local_cfun_call qn e ->
    contains_no_local_cfun_call qn (replace_local_cfun_calls cfuns sigs e).
Proof.
  intros cfuns sigs e qn H_cfuns H_e.
  gen_induction (e, sigs) cfuns; auto.
  simpl. destruct sigs as [| sig sigs]; auto.
  destruct a as [a_qn a_bod]; simpl in *.
  match goal with
  | [  |- contains_no_local_cfun_call ?qn (replace_local_cfun_calls _ _ ?e) ] =>
    assert (H_ind: contains_no_local_cfun_call qn e)
  end.
  { apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
    rewrite map_app in H_cfuns. apply Forall_sublist with (ss := map snd a_bod) in H_cfuns; try sublist_tac.
    apply Forall_map with (f := snd) in H_cfuns; auto.
  }
  apply IHcfuns; auto.
  rewrite map_app in H_cfuns. apply Forall_sublist with (ss := map snd (concat (map snd cfuns))) in H_cfuns; try sublist_tac.
Qed.

Lemma contains_one_list_sublist: forall (qn: QName) (sub tot : list expr),
    contains_one_local_cfun_call_list qn tot ->
    sublist sub tot ->
    contains_at_most_one_local_cfun_call_list qn sub.
Proof.
  intros qn sub tot H_one H_sub.
  gen_induction sub tot.
  inversion H_sub; subst.
  - unfold contains_at_most_one_local_cfun_call_list; left; auto.
  - destruct sub as [| x sub]; try solve [left; auto].
    inversion H_sub; subst.
    + inversion H_one; subst.
      * left. apply Forall_sublist with (ts := tot); auto.
      * apply IHtot; auto.
    + inversion H_one; subst.
      * right. apply contains_one_local_cfun_call_list_here; auto.
        apply Forall_sublist with (ts := tot); auto.
      * specialize (IHtot H3 sub H0).
        inversion IHtot.
        -- left. apply Forall_cons; auto.
        -- right. apply contains_one_local_cfun_call_list_there; auto.
Qed.

Ltac Forall_sublist_tac :=
  match goal with
  | [ H: Forall ?P ?tot |- Forall ?P ?sub ] =>
    apply Forall_sublist with (ss := sub) (ts := tot); sublist_tac
  end.

Lemma contains_one_list_app: forall (qn: QName) (l r : list expr),
    contains_one_local_cfun_call_list qn (l ++ r) <->
    (contains_one_local_cfun_call_list qn l /\ Forall (contains_no_local_cfun_call qn) r)
    \/ (Forall (contains_no_local_cfun_call qn) l /\ contains_one_local_cfun_call_list qn r).
Proof.
  intros qn l r. split; intro H.
  - induction l; simpl in *.
    + right; split; auto.
    + inversion H; subst.
      * left; split.
       -- apply contains_one_local_cfun_call_list_here; auto.
          Forall_sublist_tac.
       -- Forall_sublist_tac.
      * specialize (IHl H3). inversion IHl as [[Hl Hr] | [Hl Hr]].
        -- left; split; auto.
        apply contains_one_local_cfun_call_list_there; auto.
        -- right; auto.
  - inversion H as [[H_one_l H_no_r] | [H_no_l H_one_r]].
    + induction l; inversion H_one_l; subst; simpl.
      * apply contains_one_local_cfun_call_list_here; auto. apply Forall_app; auto.
      * apply contains_one_local_cfun_call_list_there; auto.
    + induction l; inversion H_no_l; subst; simpl; auto.
      apply contains_one_local_cfun_call_list_there; auto.
Qed.

Ltac contains_no_contradiction_tac :=
  match goal with
  | [ H: contains_no_local_cfun_call _ (E_ConsFunCall _ _ _) |- _ ] =>
    unfold contains_no_local_cfun_call in H;
    match type of H with
    | forall e_sub e_arg args, subterm e_sub (E_ConsFunCall ?qn ?e ?ls) -> e_sub <> E_ConsFunCall _ _ _  =>
      specialize (H (E_ConsFunCall qn e ls) e ls (Sub_Refl _)); contradiction
    end
  end.

Lemma replace_cfun_call_id_if_contains_none:
  forall (qn : QName) (e : expr) (cs : list (ScopedName * expr)) (ts : list TypeName) (rt : TypeName),
    contains_no_local_cfun_call qn e ->
    replace_cfun_call_by_match (local qn) cs ts rt e = e.
Proof.
  intros qn e cs ts rt H_no.
  induction e using expr_strong_ind; auto; simpl; f_equal;
    try solve
        [rewrite <- map_id;
         apply map_ext_in;
         intros a H_in; apply Forall_In with (x := a) in H; auto;
         apply H;
         apply contains_no_local_cfun_call_sub with (e_sub := a) in H_no; auto; subterm_tac; direct_subterm_tac
        ];
    try solve
        [IH_tac; apply contains_no_local_cfun_call_sub with (e_sub := e) in H_no; auto; subterm_tac; direct_subterm_tac];
    try solve
        [
          rewrite <- map_id;
          apply map_ext_in;
          intros a H_in;
          match goal with
          | [ H: Forall _ ?l', H_in: In ?a ?l |- _ ] =>
            match l' with
            | context [l] =>
              rewrite <- Forall_map in H; apply Forall_In with (x := a) in H; auto;
              let l := fresh in
              let r := fresh in
              destruct a as [l r]; unfold id; simpl; f_equal; apply H;
              match type of l with
              | expr =>
                apply contains_no_local_cfun_call_sub with (e_sub := l) in H_no
              | _ =>
                apply contains_no_local_cfun_call_sub with (e_sub := r) in H_no
              end; auto;
              subterm_tac; direct_subterm_tac
            end
          end
        ].
  - match_destruct_tac.
    + match_destruct_tac; try solve [inversion E_match].
      name_eq_tac.
      unfold contains_no_local_cfun_call in H_no.
      match goal with
      | [  |- _ = ?r ] => assert (NE: r <> r); [> apply H_no; subterm_tac
                                            | contradiction ]
      end.
    + f_equal.
      * IH_tac; apply contains_no_local_cfun_call_sub with (e_sub := e) in H_no; auto; subterm_tac; direct_subterm_tac.
      * rewrite <- map_id;
          apply map_ext_in;
          intros a H_in; apply Forall_In with (x := a) in H; auto;
            apply H;
            apply contains_no_local_cfun_call_sub with (e_sub := a) in H_no; auto; subterm_tac; direct_subterm_tac.
  - IH_tac. apply contains_no_local_cfun_call_sub with (e_sub := e1) in H_no; auto; subterm_tac; direct_subterm_tac.
  - IH_tac. apply contains_no_local_cfun_call_sub with (e_sub := e2) in H_no; auto; subterm_tac; direct_subterm_tac.
Qed.

Ltac contains_no_local_destr_tac :=
  let H_res := fresh "H_no_destr" in
  let H_in := fresh "H_in" in
  let x := fresh "x" in
  match goal with
  | [ H: contains_no_local_cfun_call ?qn ?e_full |- _ ] =>
    match e_full with
    | ?f _ ?es =>
      match f with
      | E_Constr => idtac
      | E_FunCall => idtac
      | E_GenFunCall => idtac
      | _ => fail
      end;
      assert (H_res: forall x, In x es -> contains_no_local_cfun_call qn x);
      [> intros x H_in;
       apply contains_no_local_cfun_call_sub with (e_sub := x) in H; auto; subterm_tac; direct_subterm_tac
      | clear H
      ]
    | E_DestrCall _ ?e ?es =>
      assert (H_res: contains_no_local_cfun_call qn e /\ forall x, In x es -> contains_no_local_cfun_call qn x);
      [> split;
       [> apply contains_no_local_cfun_call_sub with (e_sub := e) in H; auto; subterm_tac; direct_subterm_tac
       |  intros x H_in;
          apply contains_no_local_cfun_call_sub with (e_sub := x) in H; auto; subterm_tac; direct_subterm_tac
       ]
      | clear H
      ]
    | E_ConsFunCall ?sn ?e ?es =>
      assert (H_res: sn <> local qn /\ contains_no_local_cfun_call qn e /\ forall x, In x es -> contains_no_local_cfun_call qn x);
      [> split;
       [> let E := fresh in intro E; rewrite E in *; contains_no_contradiction_tac
       | [> split;
          [> apply contains_no_local_cfun_call_sub with (e_sub := e) in H; auto; subterm_tac; direct_subterm_tac
          |  intros x H_in;
             apply contains_no_local_cfun_call_sub with (e_sub := x) in H; auto; subterm_tac; direct_subterm_tac
          ]
         ]
       ]
      | clear H
      ]
    | E_Match _ ?e ?bs ?cs _ =>
      assert (H_res: contains_no_local_cfun_call qn e /\
                     (forall x, In x (map fst bs) -> contains_no_local_cfun_call qn x) /\
                     (forall x, In x (map snd cs) -> contains_no_local_cfun_call qn x));
      [> split;
       [> apply contains_no_local_cfun_call_sub with (e_sub := e) in H; auto; subterm_tac; direct_subterm_tac
       |  split; intros x H_in;
          apply contains_no_local_cfun_call_sub with (e_sub := x) in H; auto; subterm_tac; direct_subterm_tac
       ]
      | clear H
      ]
    | E_CoMatch _ ?bs ?cs =>
      assert (H_res: (forall x, In x (map fst bs) -> contains_no_local_cfun_call qn x) /\
                     (forall x, In x (map snd cs) -> contains_no_local_cfun_call qn x));
      [> split; intros x H_in;
       apply contains_no_local_cfun_call_sub with (e_sub := x) in H; auto; subterm_tac; direct_subterm_tac
      | clear H
      ]
    | E_Let ?e1 ?e2 =>
      assert (H_res: contains_no_local_cfun_call qn e1 /\
                     contains_no_local_cfun_call qn e2);
      [> split;
       match goal with
       | [  |- _ _ ?e ] =>
         apply contains_no_local_cfun_call_sub with (e_sub := e) in H; auto; subterm_tac; direct_subterm_tac
       end
      | clear H
      ]
    end
  end.


Fixpoint contains_no_local_cfun_call_b (qn: QName) (e : expr) {struct e} : bool :=
  match e with
  | E_Var _ => true
  | E_Constr _ es
  | E_FunCall _ es
  | E_GenFunCall _ es => forallb (contains_no_local_cfun_call_b qn) es
  | E_DestrCall _ e' es =>
    (contains_no_local_cfun_call_b qn e')
      && forallb (contains_no_local_cfun_call_b qn) es
  | E_ConsFunCall sn e' es =>
    (negb (eq_ScopedName sn (local qn)))
      && (contains_no_local_cfun_call_b qn e')
      && forallb (contains_no_local_cfun_call_b qn) es
  | E_Match _ e' bs cs _ =>
    (contains_no_local_cfun_call_b qn e')
      && (forallb (fun x => contains_no_local_cfun_call_b qn (fst x)) bs)
      && (forallb (fun x => contains_no_local_cfun_call_b qn (snd x)) cs)
  | E_CoMatch _ bs ccs =>
    (forallb (fun x => contains_no_local_cfun_call_b qn (fst x)) bs)
      && (forallb (fun x => contains_no_local_cfun_call_b qn (snd x)) ccs)
  | E_Let e1 e2 => (contains_no_local_cfun_call_b qn e1)
                    && (contains_no_local_cfun_call_b qn e2)
  end.

Lemma contains_no_local_cfun_call_b_complete: forall (qn : QName) (e : expr),
      contains_no_local_cfun_call qn e ->
      contains_no_local_cfun_call_b qn e = true.
Proof.
  intros qn e H.
  induction e using expr_strong_ind; simpl; auto;
    contains_no_local_destr_tac;
    repeat match goal with
           | [ H: _ /\ _ |- _ ] => inversion_clear H
           end;
    repeat rewrite Bool.andb_true_iff;
    repeat rewrite forallb_forall;
    repeat match goal with
           | [ H: Forall _ _ |- _ ] =>
             rewrite Forall_forall in H
           end;
    repeat split;
    auto;
    try solve
        [let x := fresh in
         let H := fresh in
         intros x H;
         match goal with
         | [  |- context [contains_no_local_cfun_call_b _ (?fn _)] ] =>
           apply in_map with (f := fn) in H; auto
         end].
  name_destruct_tac; auto.
  exfalso; apply H; name_eq_tac.
Qed.

Lemma contains_no_local_cfun_call_b_correct: forall (qn : QName) (e : expr),
    contains_no_local_cfun_call_b qn e = true ->
    contains_no_local_cfun_call qn e.
Proof.
  intros qn e H.
  induction e using expr_strong_ind;
    simpl in H;
      repeat rewrite Forall_forall in *;
      repeat rewrite Bool.andb_true_iff in *;
      repeat match goal with
             | [ H: _ /\ _ |- _ ] => inversion_clear H
             end;
      repeat rewrite forallb_forall in *;
      try solve
          [apply contains_no_local_cfun_call_direct_sub; intros; [> | intro E; inversion E];
           match goal with
           | [ H_dir: direct_subterm _ _ |- _ ] =>
             inversion H_dir; subst; auto
           end];
  try solve
      [apply contains_no_local_cfun_call_direct_sub; intros; [> | intro E; inversion E];
       match goal with
       | [ H_dir: direct_subterm _ _ |- _ ] =>
         inversion H_dir; subst; auto
       end;
       match goal with
       | [ H_in: In _ (map ?fn ?ls),
                 H_f: forall x, In x (map _ ?ls) -> _,
             H_b: forall x, In x ?ls -> _  |- _ ] =>
         apply H_f; auto;
         rewrite in_map_iff in H_in;
         inversion H_in as [_x [_E _H]]; subst; auto
       end].
  apply contains_no_local_cfun_call_direct_sub; intros.
  - inversion H1; subst; auto.
  - intro E. inversion E; subst.
    name_refl_tac. inversion H.
Qed.

Ltac replace_adds_at_most_one_ls_tac :=
    match goal with
    | [ IH: Forall _ ?ls, H_one: contains_one_local_cfun_call_list ?qn_orig ?ls, H_no: forall x, In x ?ls -> contains_no_local_cfun_call ?qn x |- _ ] =>
      let lst:= match ls with
                | map _ ?xs => xs
                | _ => ls
                end in
    induction lst; inversion H_one; subst; simpl in *;
    [>
     match goal with
     | [ H_no_ls: Forall (fun e => contains_no_local_cfun_call qn_orig e) ?ls,
                  H_one_a: contains_one_local_cfun_call qn_orig ?a |- _ ] =>
       apply contains_one_local_cfun_call_list_here; auto;
       [> rewrite <- Forall_map; apply Forall_forall; intros y H_in;
        rewrite replace_cfun_call_id_if_contains_none; auto;
        apply Forall_In with (x := y) in H_no_ls; auto
       |  inversion IH; subst; auto
       ]
     end
    |
    match goal with
    | [ H_no_a: contains_no_local_cfun_call qn_orig ?a,
                H_one_ls: contains_one_local_cfun_call_list qn_orig ?ls |- _ ] =>
      apply contains_one_local_cfun_call_list_there; auto;
      [> IH_tac auto; Forall_tail_tac
      |  rewrite replace_cfun_call_id_if_contains_none; auto
      ]
    end
    ]
    end.

Lemma replace_cfun_call_adds_at_most_one:
  forall (qn qn' : QName) (e : expr) (cs : list (ScopedName * expr)) (ts : list TypeName) (rt : TypeName),
    contains_no_local_cfun_call qn e ->
    contains_at_most_one_local_cfun_call qn' e ->
    contains_at_most_one_local_cfun_call_list qn (map snd cs) ->
    contains_at_most_one_local_cfun_call qn (replace_cfun_call_by_match (local qn') cs ts rt e).
Proof.
  intros qn qn_orig e cs ts rt H_no_qn H_most_qn'_e H_most_qn_cs.
  inversion_clear H_most_qn'_e as [H_no | H_one_e];
    try solve [rewrite replace_cfun_call_id_if_contains_none; auto;
               left; auto].
  inversion_clear H_most_qn_cs as [H_no_cs | H_one_cs];
  try solve [left; apply replace_cfun_call_by_match_creates_no_cfun_calls; auto;
             rewrite Forall_map; auto].
  right. induction e using expr_strong_ind; simpl; inversion_clear H_one_e; subst.
  - apply contains_one_local_cfun_call_Constr.
    contains_no_local_destr_tac.
    replace_adds_at_most_one_ls_tac.
  - contains_no_local_destr_tac; destruct H_no_destr as [H_no_e H_no_ls].
    apply contains_one_local_cfun_call_DestrCall_e; auto.
    rewrite <- Forall_map. apply Forall_forall.
    intros x H_in. rewrite replace_cfun_call_id_if_contains_none; auto.
    apply Forall_In with (x0 := x) in H1; auto.
  - contains_no_local_destr_tac; destruct H_no_destr as [H_no_e H_no_ls].
    apply contains_one_local_cfun_call_DestrCall_es; auto.
    + rewrite replace_cfun_call_id_if_contains_none; auto.
    + clear IHe H_no_e.
      replace_adds_at_most_one_ls_tac.
  - contains_no_local_destr_tac.
    apply contains_one_local_cfun_call_FunCall.
    replace_adds_at_most_one_ls_tac.
  - match_destruct_tac.
    + match_destruct_tac; try solve [inversion E_match].
      name_eq_tac. contradiction.
    + apply contains_one_local_cfun_call_ConsFunCall_e; auto.
      * unfold contains_no_local_cfun_call in H_no_qn.
        specialize (H_no_qn (E_ConsFunCall sn e ls) e ls).
        intro E. apply H_no_qn; try subterm_tac. rewrite E; auto.
      * IH_tac. apply contains_no_local_cfun_call_sub with (e_sub := e) in H_no_qn; auto.
        subterm_tac; direct_subterm_tac.
      * rewrite <- Forall_map. apply Forall_forall; intros y H_in.
        contains_no_local_destr_tac. inversion H_no_destr as [_ [_ H_no]].
        rewrite replace_cfun_call_id_if_contains_none; auto.
        apply Forall_In with (x := y) in H2; auto.
  - match_destruct_tac.
    + match_destruct_tac; try solve [inversion E_match].
      name_eq_tac. contradiction.
    + apply contains_one_local_cfun_call_ConsFunCall_es; auto.
      * unfold contains_no_local_cfun_call in H_no_qn.
        specialize (H_no_qn (E_ConsFunCall sn e ls) e ls).
        intro E. apply H_no_qn; try subterm_tac. rewrite E; auto.
      * contains_no_local_destr_tac; inversion H_no_destr as [_ [Hx Hy]].
        rewrite replace_cfun_call_id_if_contains_none; auto.
      * contains_no_local_destr_tac. inversion_clear H_no_destr as [_ [H_no_e H_no_ls]].
        replace_adds_at_most_one_ls_tac.
  - name_refl_tac.
    contains_no_local_destr_tac. inversion_clear H_no_destr as [_ [H_no_e H_no_ls]].
    apply contains_one_local_cfun_call_Match_cases; auto.
    rewrite <- Forall_map. apply Forall_forall; intros y H_in.
    assert (H_in': In (fst y) ls).
    { clear - H_in. gen_induction ts ls; destruct ts; inversion H_in.
      - left; destruct y; simpl in *; inversion H; auto.
      - right. IH_auto_tac.
    }
    clear H_in. apply H_no_ls; auto.
  - contains_no_local_destr_tac.
    apply contains_one_local_cfun_call_GenFunCall.
    replace_adds_at_most_one_ls_tac.
  - contains_no_local_destr_tac.
    inversion_clear H_no_destr as [H_no_e [H_no_bs H_no_cs]].
    apply contains_one_local_cfun_call_Match_e.
    + IH_tac auto.
    + rewrite map_fst_map_in_fst; rewrite <- map_map.
      rewrite <- Forall_map.
      apply Forall_forall; intros y H_in.
      apply Forall_In with (x := y) in H2; auto.
      rewrite replace_cfun_call_id_if_contains_none; auto.
    + rewrite map_snd_map_in_snd; rewrite <- map_map.
      rewrite <- Forall_map.
      apply Forall_forall; intros y H_in.
      apply Forall_In with (x := y) in H3; auto.
      rewrite replace_cfun_call_id_if_contains_none; auto.
  - contains_no_local_destr_tac.
    inversion_clear H_no_destr as [H_no_e [H_no_bs H_no_cs]].
    apply contains_one_local_cfun_call_Match_bs.
    + rewrite replace_cfun_call_id_if_contains_none; auto.
    + rewrite map_fst_map_in_fst; rewrite <- map_map.
      replace_adds_at_most_one_ls_tac.
    + rewrite map_snd_map_in_snd; rewrite <- map_map.
      rewrite <- Forall_map.
      apply Forall_forall; intros y H_in.
      apply Forall_In with (x := y) in H3; auto.
      rewrite replace_cfun_call_id_if_contains_none; auto.
  - contains_no_local_destr_tac.
    inversion_clear H_no_destr as [H_no_e [H_no_bs H_no_cs]].
    apply contains_one_local_cfun_call_Match_cases.
    + rewrite replace_cfun_call_id_if_contains_none; auto.
    + rewrite map_fst_map_in_fst; rewrite <- map_map.
      rewrite <- Forall_map.
      apply Forall_forall; intros y H_in.
      apply Forall_In with (x := y) in H2; auto.
      rewrite replace_cfun_call_id_if_contains_none; auto.
    + rewrite map_snd_map_in_snd; rewrite <- map_map.
      replace_adds_at_most_one_ls_tac.
  - contains_no_local_destr_tac.
    inversion_clear H_no_destr as [H_no_bs H_no_cs].
    apply contains_one_local_cfun_call_CoMatch_bs.
    + rewrite map_fst_map_in_fst; rewrite <- map_map.
      replace_adds_at_most_one_ls_tac.
    + rewrite map_snd_map_in_snd; rewrite <- map_map.
      rewrite <- Forall_map.
      apply Forall_forall; intros y H_in.
      apply Forall_In with (x := y) in H2; auto.
      rewrite replace_cfun_call_id_if_contains_none; auto.
  - contains_no_local_destr_tac.
    inversion_clear H_no_destr as [H_no_bs H_no_cs].
    apply contains_one_local_cfun_call_CoMatch_cocases.
    + rewrite map_fst_map_in_fst; rewrite <- map_map.
      rewrite <- Forall_map.
      apply Forall_forall; intros y H_in.
      apply Forall_In with (x := y) in H1; auto.
      rewrite replace_cfun_call_id_if_contains_none; auto.
    + rewrite map_snd_map_in_snd; rewrite <- map_map.
      replace_adds_at_most_one_ls_tac.
  - contains_no_local_destr_tac. inversion_clear H_no_destr as [H_no1 H_no2].
    apply contains_one_local_cfun_call_Let_e1.
    + IH_tac auto.
    + rewrite replace_cfun_call_id_if_contains_none; auto.
  - contains_no_local_destr_tac. inversion_clear H_no_destr as [H_no1 H_no2].
    apply contains_one_local_cfun_call_Let_e2.
    + rewrite replace_cfun_call_id_if_contains_none; auto.
    + IH_tac auto.
Qed.


Lemma replace_cfun_call_keeps_arity: forall (e : expr) (qn qn' : QName) (bod : cfun_bod) (arg : list TypeName) (rt : TypeName) (n : nat),
   (forall (e' : expr) (ls : list expr),
       subterm (E_ConsFunCall (local qn) e' ls) e ->
       length ls = n) ->
   Forall (fun b =>
             forall (e': expr) (ls : list expr),
               subterm (E_ConsFunCall (local qn) e' ls) (snd b) -> length ls = n) bod ->
   forall (e' : expr) (ls : list expr),
     subterm (E_ConsFunCall (local qn) e' ls)
             (replace_cfun_call_by_match (local qn') bod arg rt e) ->
     length ls = n.
Proof.
  intros e qn qn' bod arg rt n H H_bods.
  induction e using expr_strong_ind; intros e' ls' H_sub; simpl in *;
    match type of H_sub with
    | subterm _ ?et =>
      match et with
      | context [E_ConsFunCall] => idtac
      end
    | _ => inversion_clear H_sub
    end; try
  match goal with
  | [ H: direct_subterm _ _ |- _ ] => inversion H; subst; rename H into H_dir
  end;
    try solve
        [  try match goal with
    | [ H: In _ _ |- _ ] =>
      rewrite map_fst_map_in_fst in H || rewrite map_snd_map_in_snd in H;
      rewrite <- map_map in H
    end;
    match goal with
    | [ H_dir: direct_subterm _ _,
               H_in: In _ (map _ ?ls'),
                     Hf : Forall _ ?ls' |- _ ] =>
      let ls := match ls' with
                | map _ ?x => x
                | ?x => x
                end in
      clear H_dir; induction ls; simpl in *; inversion H_in;
        [> subst;
         let H_head := fresh Hf in
        Forall_head Hf as H_head;
        apply H_head with (e' := e'); auto;
        intros ex lsx H_subx; apply H with (e' := ex); subterm_trans_tac; subterm_tac; direct_subterm_tac
    |  IH_tac; auto; try Forall_tail_tac;
       intros ex lsx H_subx; apply H with (e' := ex);
       match goal with
       | [ H: subterm ?sub _ |- subterm ?sub _ ] =>
         inversion H; subst;
         match goal with
         | [ Hd: direct_subterm _ _ |- _ ] =>
           inversion Hd; subst;
           subterm_trans_tac; subterm_tac; direct_subterm_tac
         end
       end
    ]

    end];
  try solve
  [apply IHe with (e' := e'); auto; intros ex lsx H_subx;
      apply H with (e' := ex); subterm_trans_tac; subterm_tac; direct_subterm_tac].
  - match_destruct_tac.
    + match_destruct_tac; try solve [inversion E_H_sub_match].
      name_eq_tac.
      inversion_clear H_sub. inversion H2; subst.
      * apply H with (e' := e'); auto.
        subterm_trans_tac; subterm_tac; direct_subterm_tac.
      * clear IHe H_bods H0.
        assert (H': forall x e' ls0, In x ls -> subterm (E_ConsFunCall (local qn) e' ls0) x -> length ls0 = n).
        { intros x ex lsx H_in H_subx. apply H with (e' := ex).
          subterm_trans_tac; subterm_tac; direct_subterm_tac. }
        clear H; rename H' into H.
        gen_induction arg ls; destruct arg; simpl in *; inversion H5; subst.
        -- clear IHls. apply H with (x := e2) (e' := e'); try left; auto.
        -- apply IHls with (arg := arg); auto.
           ++ intros x ex lsx H_in H_subx. apply H with (x := x) (e' := ex); auto.
           ++ direct_subterm_tac.
      * clear IHe H0 H. induction bod; inversion H5; subst.
        -- inversion H_bods; subst. apply H3 with (e' := e'); auto.
        -- apply IHbod; auto; try Forall_tail_tac. direct_subterm_tac.
    + inversion H_sub; subst.
      * rewrite map_length.
        apply H with (e' := e); subterm_tac.
      * inversion H2; subst.
        -- apply IHe with (e' := e'); auto.
           intros ex lsx H_subx.
           apply H with (e' := ex). subterm_trans_tac; subterm_tac; direct_subterm_tac.
        -- clear H_bods IHe H_sub H2.
           assert (H_ls: forall x e' ls0, In x ls -> subterm (E_ConsFunCall (local qn) e' ls0) x -> length ls0 = n);
             [> clear - H; intros; apply H with (e' := e'); subterm_trans_tac; subterm_tac; direct_subterm_tac
             | ].
           assert (H_e: forall e' ls0, subterm (E_ConsFunCall (local qn) e' ls0) e -> length ls0 = n);
             [> clear - H; intros; apply H with (e' := e'); subterm_trans_tac; subterm_tac; direct_subterm_tac
             | ].
           clear H.
           induction ls; inversion H5; subst.
           ++ inversion H0; subst. apply H3 with (e' := e'); auto.
              intros ex lsx H_subx.
              apply H_ls with (x := a) (e' := ex); auto.
           ++ apply IHls; auto; try Forall_tail_tac.
              intros x ex lsx H_in H_subx.
              apply H_ls with (x := x) (e' := ex); auto.
  - apply IHe1 with (e' := e'); auto; intros ex lsx H_subx;
      apply H with (e' := ex); subterm_trans_tac; subterm_tac; direct_subterm_tac.
  - apply IHe2 with (e' := e'); auto; intros ex lsx H_subx;
      apply H with (e' := ex); subterm_trans_tac; subterm_tac; direct_subterm_tac.
Qed.

Lemma replace_local_cfun_calls_removes_all_local_cfun_calls:
  forall (cfuns: cfun_bods) (sigs: cfun_sigs) (e: expr),
    inline_ordered_cfun cfuns ->
    cfun_sig_bod_paring cfuns sigs ->
    Forall (fun bod =>
              contains_at_most_one_local_cfun_call_list (fst bod) (e :: map snd (concat (map snd cfuns)))) cfuns ->
    Forall (fun sig =>
              Forall (fun bod =>
                        forall (e' : expr) (ls : list expr),
                          subterm (E_ConsFunCall (local (fst (fst sig))) e' ls) bod ->
                          length ls = length (snd (fst sig)))
                     (e :: map snd (concat (map snd cfuns))))
           sigs ->
    Forall (fun bod =>
              contains_no_local_cfun_call (fst bod) (replace_local_cfun_calls cfuns sigs e)) cfuns.
Proof.
  intros cfuns sigs e H_ordered H_pairing H_at_most H_sub_len.
  assert (sublist cfuns cfuns); [> sublist_tac |].
  gen_dep H; generalize cfuns at 1 4; intro cfuns_rec; intros.
  gen_induction (cfuns, sigs) cfuns_rec; try apply Forall_nil.
  apply Forall_cons; [> | apply IHcfuns_rec; auto; try sublist_tac; try Forall_tail_tac ].
  assert (H_in: In a cfuns);
    [> clear - H; induction cfuns; inversion H; subst; auto; right; IH_tac |]; clear H.
  clear IHcfuns_rec.
  gen_induction (sigs, e) cfuns; inversion H_in; subst; destruct sigs as [| sig sigs]; try solve [inversion H_pairing].
  - simpl.
    inversion_clear H_at_most. destruct a as [a_qn a_bod]; simpl in *.
    inversion H_ordered; subst.
    inversion H.
    +
    match goal with
    | [  |- contains_no_local_cfun_call ?a_qn (_ _ _ ?e) ] =>
      assert (H_no: contains_no_local_cfun_call a_qn e)
    end.
    { apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
      inversion H1; subst; auto. }
    apply replace_local_cfun_calls_creates_no_local_cfun_calls; auto.
    rewrite map_app in H1.
    match goal with
    | [ H: Forall _ ?tot |- Forall _ ?ls ] =>
      apply Forall_sublist with (ss := ls) (ts := tot); [> assumption | ]
    end.
    rewrite <- app_nil_r. rewrite app_comm_cons. rewrite <- app_assoc.
    sublist_tac.
    + inversion H1; subst.
      * match goal with
        | [  |- contains_no_local_cfun_call ?a_qn (_ _ _ ?e) ] =>
          assert (H_no: contains_no_local_cfun_call a_qn e)
        end;
          [> apply replace_cfun_call_by_match_removes_all_cfun_calls; auto |].
        apply replace_local_cfun_calls_creates_no_local_cfun_calls; auto.
        rewrite map_app in H8. Forall_sublist_tac.
      * clear - H5 H6 H8; exfalso.
        rewrite map_app in H8.
        pose proof contains_one_and_no_local_cfun_absurd_list as Hx.
        apply contains_one_list_app in H8. inversion H8 as [[H _] | [_ H]].
        -- clear - H H6 Hx.
           specialize (Hx a_qn (map snd a_bod)).
           apply Hx; split; auto.
           rewrite Forall_map in H6; auto.
        -- clear - H H5 Hx.
           apply Forall_map in H5. apply Forall_flatten in H5.
           rewrite map_map in H5. apply Forall_map in H5.
           rewrite map_ext with (l := cfuns) (g := snd) in H5; [> | auto].
           match goal with
           | [ _: contains_one_local_cfun_call_list ?qn ?ls |- _ ] =>
             specialize (Hx qn ls); apply Hx; auto
           end.
  - simpl. apply IHcfuns; auto.
    + inversion H_ordered; auto.
    + inversion H_at_most; subst.
      match type of H3 with
      | ?t => cut t
      end; auto.
      intro H_old. clear H_at_most. apply Forall_forall. unfold cfun_bod_named in *.
      pose proof Forall_forall as HF.
      specialize HF with (l := cfuns).
      specialize (HF (fun bod => contains_at_most_one_local_cfun_call_list (fst bod) (e :: map snd (concat (map snd (a0 :: cfuns)))))).
      inversion HF as [HF' _]; clear HF. specialize (HF' H_old); clear H_old.
      intros x H_in'. specialize (HF' x H_in').
      inversion HF' as [Hx | Hx].
      * left. apply Forall_cons.
        -- inversion_clear Hx. apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
           rewrite map_app in H1.
           apply Forall_sublist with (ss := map snd (snd a0)) in H1; try sublist_tac.
           apply Forall_map; auto.
        -- inversion_clear Hx.
           rewrite map_app in H1.
           apply Forall_sublist with (ss := map snd (concat (map snd cfuns))) in H1; try sublist_tac.
      * (* we need to show that if e contains_one (fst x) cfun and x <> qn, then replace_... also contains_one (fst x) *)
        inversion_clear Hx.
        -- destruct (eq_QName (fst x) (fst a0)) eqn:E_qn.
           ++ name_eq_tac. rewrite E_qn in *.
              left. apply Forall_cons.
              ** apply replace_cfun_call_by_match_removes_all_cfun_calls; auto.
                 inversion H_ordered; subst; auto.
              ** rewrite map_app in H0.
                 apply Forall_sublist with (ss := map snd (concat (map snd cfuns))) in H0; sublist_tac.

           ++ assert (fst x <> fst a0);
              [> intro E; rewrite E in *; name_refl_contradiction_tac |].
             right. apply contains_one_local_cfun_call_list_here; auto.
              ** rewrite map_app in H0.
                 match goal with
                 | [  |- Forall _ ?ls ] =>
                   apply Forall_sublist with (ss := ls) in H0; try sublist_tac
                 end.
              ** apply replace_cfun_call_keeps_different_cfun_calls; auto.
                 ---
                   clear IHcfuns. inversion H_sub_len; subst. clear H8 H_sub_len.
                   inversion_clear H7.
                   inversion H_pairing; subst. auto.
                 --- simpl in H0; rewrite map_app in H0.
                     apply Forall_sublist with (ss := map snd (snd a0)) in H0; try sublist_tac.
                     rewrite Forall_map; auto.
        -- destruct a0 as [qn bod]; simpl in *.
           rewrite map_app in H0. apply contains_one_list_app in H0.
           inversion_clear H0 as [[H_one_bod H_no_cfuns] | [H_no_bod H_one_cfuns]].
           ++ clear IHcfuns.
              inversion_clear H2 as [H_none | H_one].
              ** inversion H_none; subst.
                 left.
                 rewrite replace_cfun_call_id_if_contains_none; auto.
              ** inversion H_one; subst.
                 --- pose proof (replace_cfun_call_adds_at_most_one (fst x) qn e bod (snd (fst sig)) (snd sig)).
                     apply H0 in H1; try solve [try right; auto]; clear H0.
                     rewrite map_app in H5.
                     apply Forall_sublist with (ss := map snd (concat (map snd cfuns))) in H5; try sublist_tac.
                     inversion H1.
                     +++ left; auto.
                     +++ right. apply contains_one_local_cfun_call_list_here; auto.
                 --- inversion H_ordered; subst.
                     assert (Forall (contains_no_local_cfun_call qn) (map snd (bod ++ concat (map snd cfuns)))).
                     { clear - H8 H9.
                       rewrite map_app; apply Forall_app.
                       - rewrite <- Forall_map; auto.
                       - rewrite <- Forall_flatten in H8.
                         rewrite <- Forall_map. auto.
                     }
                     clear - H5 H0.
                     exfalso.
                         match goal with
                     | [ H: contains_one_local_cfun_call_list ?q ?l |- _ ] =>
                       apply contains_one_and_no_local_cfun_absurd_list with (ls := l) (qn := q)
                     end; auto.
           ++ right.
              apply contains_one_local_cfun_call_list_there; auto.
              apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
              apply Forall_map; auto.
    + inversion H_pairing; auto.
    + clear IHcfuns H_in.
      inversion H_pairing; subst.
      simpl in *.
      inversion_clear H_sub_len; clear H1.
      apply Forall_forall; intros some_sig H_in.
      apply Forall_In with (x := some_sig) in H2; auto.
      inversion_clear H2.
      apply Forall_cons.
      * apply replace_cfun_call_keeps_arity; auto.
        apply Forall_sublist with (ss := map snd bod) in H3; try (rewrite map_app; sublist_tac).
        rewrite <- Forall_map in H3; auto.
      * rewrite map_app in H3.
        Forall_sublist_tac.
Qed.

(*****************************************************************************)
(** Def inline of skeleton               *************************************)
(*****************************************************************************)

Lemma new_cfun_sigs_in_dts: forall (sk: skeleton) (cfuns: cfun_sigs),
    (exists rest, cfuns ++ rest = (skeleton_cfun_sigs_l sk)) ->
    cfun_sigs_in_dts (skeleton_dts sk) cfuns.
Proof.
  intros sk cfuns H.
  pose proof (skeleton_cfun_sigs_in_dts_l sk) as H_in.
  unfold cfun_sigs_in_dts in *.
  inversion H.
  apply Forall_sublist with (ts := skeleton_cfun_sigs_l sk); auto.
  rewrite <- H0. sublist_tac.
Defined.

Lemma new_cfun_sigs_names_unique: forall (sk: skeleton) (cfuns: cfun_sigs),
    (exists rest, cfuns ++ rest = (skeleton_cfun_sigs_l sk)) ->
  cfun_sigs_names_unique cfuns.
Proof.
  intros sk cfuns H.
  pose proof (skeleton_cfun_sigs_names_unique_l sk).
  unfold cfun_sigs_names_unique in *.
  inversion H. rewrite <- H1 in *.
  unique_sublist_tac.
Defined.

Definition inline_cfuns_to_skeleton_partial (p : program) (cfuns: cfun_sigs) (E: exists rest, cfuns ++ rest = (skeleton_cfun_sigs_l (program_skeleton p))) : skeleton :=
  let old_skeleton : skeleton := program_skeleton p in
  {|
      (* Datatypes *)
      skeleton_dts := skeleton_dts old_skeleton;
      skeleton_ctors := skeleton_ctors old_skeleton;
      skeleton_dts_ctors_in_dts := skeleton_dts_ctors_in_dts old_skeleton;
      skeleton_dts_ctor_names_unique := skeleton_dts_ctor_names_unique old_skeleton;
      (* Codatatypes *)
      skeleton_cdts := skeleton_cdts old_skeleton;
      skeleton_dtors :=  skeleton_dtors old_skeleton;
      skeleton_cdts_dtors_in_cdts := skeleton_cdts_dtors_in_cdts old_skeleton;
      skeleton_cdts_dtor_names_unique := skeleton_cdts_dtor_names_unique old_skeleton;
      (* Datatypes + Codatatypes *)
      skeleton_dts_cdts_disjoint := skeleton_dts_cdts_disjoint old_skeleton;
      (* Ordinary Functions *)
      skeleton_fun_sigs := skeleton_fun_sigs old_skeleton;
      skeleton_fun_sigs_names_unique := skeleton_fun_sigs_names_unique old_skeleton;
      (* Consumer functions *)
      skeleton_cfun_sigs_g := skeleton_cfun_sigs_g old_skeleton;
      skeleton_cfun_sigs_in_dts_g := skeleton_cfun_sigs_in_dts_g old_skeleton;
      skeleton_cfun_sigs_names_unique_g := skeleton_cfun_sigs_names_unique_g old_skeleton;
      (* Only interesting part: =====> *)
      skeleton_cfun_sigs_l := cfuns;
      skeleton_cfun_sigs_in_dts_l := new_cfun_sigs_in_dts old_skeleton cfuns E;
      skeleton_cfun_sigs_names_unique_l := new_cfun_sigs_names_unique old_skeleton cfuns E;
      (* <===== *)
      (* Generator functions *)
      skeleton_gfun_sigs_g := skeleton_gfun_sigs_g old_skeleton;
      skeleton_gfun_sigs_in_cdts_g := skeleton_gfun_sigs_in_cdts_g old_skeleton;
      skeleton_gfun_sigs_names_unique_g := skeleton_gfun_sigs_names_unique_g old_skeleton;
      skeleton_gfun_sigs_l := skeleton_gfun_sigs_l old_skeleton;
      skeleton_gfun_sigs_in_cdts_l := skeleton_gfun_sigs_in_cdts_l old_skeleton;
      skeleton_gfun_sigs_names_unique_l := skeleton_gfun_sigs_names_unique_l old_skeleton;
  |}.

Definition inline_cfuns_to_skeleton (p : program) : skeleton.
  refine (inline_cfuns_to_skeleton_partial p [] _).
  simpl; eauto.
Defined.

Definition replace_local_cfun_calls_prog (p : program) : expr -> expr :=
  replace_local_cfun_calls (program_cfun_bods_l p) (skeleton_cfun_sigs_l (program_skeleton p)).


(*****************************************************************************)
(** Typechecking preservation            *************************************)
(*****************************************************************************)


Ltac inline_cfun_to_skeleton_contains_no_tac :=
      let qn := fresh in
      let H := fresh in
      match goal with
      | [ H_no: forall qn, ~In qn _ -> contains_no_local_cfun_call qn _ |- _ ] =>
        intros qn H; specialize (H_no qn H); auto;
        contains_no_local_destr_tac;
        try (let H1 := fresh in let H2 := fresh in let H3 := fresh in inversion H_no_destr as [H1 [H2 H3]] ||
            inversion H_no_destr; auto);
        simpl in *; auto;
          try (apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E ];
               intro; let Hx := fresh in intro Hx; inversion Hx; subst);
          auto
      end.

Lemma typechecking_unique_ctxt_and_type: forall (sk : skeleton) (e : expr) (args : list expr) (sn : ScopedName) (ctxt ctxt' : ctxt) (t t': TypeName),
    (sk / ctxt |- (E_ConsFunCall sn e args) : t) ->
    (sk / ctxt' |- (E_ConsFunCall sn e args) : t') ->
    t = t'.
Proof.
  intros sk e args sn ctxt ctxt' t t' H H'.
  inversion H; inversion H'; subst; inversion H9; subst; clear H9.
  - pose proof (skeleton_cfun_sigs_names_unique_g sk) as H_unique; unfold cfun_sigs_names_unique in H_unique.
    clear - H5 H14 H_unique.
    induction (skeleton_cfun_sigs_g sk); inversion H5; inversion H14; subst.
    + inversion H0; auto.
    + simpl in H_unique. inversion H_unique.
      apply in_map with (f := fun x => fst (fst x)) in H0; simpl in *. contradiction.
    + simpl in H_unique. inversion H_unique.
      apply in_map with (f := fun x => fst (fst x)) in H; simpl in *. contradiction.
    + IH_tac auto. inversion H_unique; auto.
  - pose proof (skeleton_cfun_sigs_names_unique_l sk) as H_unique; unfold cfun_sigs_names_unique in H_unique.
    clear - H5 H14 H_unique.
    induction (skeleton_cfun_sigs_l sk); inversion H5; inversion H14; subst.
    + inversion H0; auto.
    + simpl in H_unique. inversion H_unique.
      apply in_map with (f := fun x => fst (fst x)) in H0; simpl in *. contradiction.
    + simpl in H_unique. inversion H_unique.
      apply in_map with (f := fun x => fst (fst x)) in H; simpl in *. contradiction.
    + IH_tac auto. inversion H_unique; auto.
Qed.


Section Inline_partial_keeps_typecheck.
  Ltac inline_partial_keeps_typecheck_no_tac :=
    let qn := fresh in
    let H := fresh in
    match goal with
    | [ H_no: forall qn, ~In qn _ -> contains_no_local_cfun_call qn _  |- _ ] =>
      intros qn H; specialize (H_no qn H);
      contains_no_local_destr_tac;
      let rec destr_prod :=
          match goal with
          | [ H: _ /\ _ |- _ ] => inversion_clear H; destr_prod
          | _ => idtac
          end in destr_prod;
      simpl in *; auto;
      try (apply contains_no_local_cfun_call_direct_sub; [> | intros; let E:= fresh in intro E; inversion E ];
           intro; let Hx := fresh in intro Hx; inversion Hx; subst);
      auto
    end.

  Ltac x :=
    match goal with
    | [ H_f: Forall _ ?ls, H_t: _ // ?ctxt ||- ?ls :: ?cargs,
                                H_no: forall qn, ~In qn _ -> contains_no_local_cfun_call qn _ |- _ // ?ctxt ||- ?ls :: ?cargs ] =>
      clear - H_f H_t H_no;
      gen_induction cargs ls; destruct cargs; inversion H_t; subst; try apply ListTypeDeriv_Nil;
      simpl in *; apply ListTypeDeriv_Cons; auto; inversion H_f; subst;
      match goal with
      | [ H:_ |- _ ] => apply H; auto; try solve inline_partial_keeps_typecheck_no_tac
      end
    | [ H:_ |- _ ] => apply H; auto; inline_partial_keeps_typecheck_no_tac
    end.


  Lemma inline_partial_keeps_typecheck: forall (p : program) (e : expr) (cfuns : cfun_sigs) (ctxt : ctxt) (tn : TypeName)
                                          (E: exists rest, cfuns ++ rest = skeleton_cfun_sigs_l (program_skeleton p)),
      (forall qn, ~In qn (map (fun x => fst (fst x)) cfuns) -> contains_no_local_cfun_call qn e) ->
      ((program_skeleton p) / ctxt |- e : tn) ->
      (inline_cfuns_to_skeleton_partial p cfuns E) / ctxt |- e : tn.
  Proof.
    intros p e cfuns ctxt tn E_cfuns H_no H_t.
    gen_dep ctxt.
    rename tn into tn'; generalize tn' as tn.
    induction e using expr_strong_ind; intros; inversion H_t; subst.
    - apply T_Var; auto.
    - apply T_Constr with (cargs := cargs); auto; x.
    - apply T_DestrCall with (dargs := dargs); auto; x.
    - apply T_FunCall with (argts := argts); auto; x.
    - apply T_GlobalConsFunCall with (argts := argts); auto; x.
    - apply T_LocalConsFunCall with (argts := argts); auto; try x; simpl.
      + pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as H_unique.
        inversion E_cfuns as [rest E']; rewrite <- E' in *; clear E'.
        apply In_app_iff in H5; inversion H5; auto.
        unshelve epose proof (in_dec _ qn (map (fun x => fst (fst x)) cfuns)) as H_dec; [> repeat decide equality |].
        inversion H_dec; auto.
        * unfold cfun_sigs_names_unique in H_unique. rewrite map_app in H_unique.
          apply in_map with (f := fun x => fst (fst x)) in H0; simpl in H0.
          apply uniqueness_app_not_in in H_unique. rewrite Forall_forall in H_unique.
          specialize (H_unique qn H1). contradiction.
        * specialize (H_no qn H1).
          contains_no_contradiction_tac.
      + clear - H_no. intros. specialize (H_no qn0 H).
        unfold contains_no_local_cfun_call.
        intros. inversion H0; subst.
        * intro E; inversion E; subst.
          contains_no_contradiction_tac.
        * contains_no_local_destr_tac. inversion H_no_destr as [_ [H3 H4]].
          inversion H2; subst; auto.
          unfold contains_no_local_cfun_call in H4.
          specialize (H4 e2 (or_intror H7)).
          apply H4; auto.
    - apply T_GlobalGenFunCall with (argts := argts); auto; try x.
    - apply T_LocalGenFunCall with (argts := argts); auto; try x.
    - apply T_Match with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types) (ctorlist := ctorlist); auto; try x.
      + clear - H11 H0 H_no.
        gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion H11; subst; try apply ListTypeDeriv_Nil.
        simpl in *; inversion_clear H0; apply ListTypeDeriv_Cons; auto.
        * apply H; auto; inline_partial_keeps_typecheck_no_tac.
        * apply IHbindings_exprs; auto; inline_partial_keeps_typecheck_no_tac.
      + clear - H H_no H14.
        gen_induction ctorlist ls; destruct ctorlist; inversion H14; subst; try apply ListTypeDeriv'_Nil.
        simpl in *; inversion_clear H; apply ListTypeDeriv'_Cons; auto.
        * apply H0; auto; inline_partial_keeps_typecheck_no_tac.
        * apply IHls; auto; try Forall_tail_tac; inline_partial_keeps_typecheck_no_tac.
    - apply T_CoMatch with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types) (dtorlist := dtorlist); auto.
      + clear - H_no H5 H0.
        gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion H5; subst; try apply ListTypeDeriv_Nil.
        simpl in *; inversion H0; subst; apply ListTypeDeriv_Cons.
        * apply H2; auto; inline_partial_keeps_typecheck_no_tac.
        * apply IHbindings_exprs; auto; inline_partial_keeps_typecheck_no_tac.
      + clear - H_no H H11.
        gen_induction dtorlist ls; destruct dtorlist; inversion H11; subst; try apply ListTypeDeriv'_Nil.
        simpl in *; inversion H; subst; apply ListTypeDeriv'_Cons; auto.
        * apply H2; auto; inline_partial_keeps_typecheck_no_tac.
        * apply IHls; auto; inline_partial_keeps_typecheck_no_tac.
    - apply T_Let with (t1 := t1).
      + apply IHe1; auto; inline_partial_keeps_typecheck_no_tac.
      + apply IHe2; auto; inline_partial_keeps_typecheck_no_tac.
  Qed.
End Inline_partial_keeps_typecheck.

Lemma contains_at_most_one_local_cfun_call_sub: forall (qn : QName) (sub tot : expr),
    subterm sub tot ->
    contains_at_most_one_local_cfun_call qn tot ->
    contains_at_most_one_local_cfun_call qn sub.
Proof.
  intros qn sub tot H_sub H_most.
  inversion H_most.
  - left. apply (contains_no_local_cfun_call_sub _ _ _ H); auto.
  - unfold contains_at_most_one_local_cfun_call. apply or_comm.
    eapply contains_one_local_cfun_call_subterms_at_most_one; eauto.
Qed.

Ltac contains_one_constrs_tac :=
  apply contains_one_local_cfun_call_CoMatch_bs +
        apply contains_one_local_cfun_call_CoMatch_cocases +
        apply contains_one_local_cfun_call_ConsFunCall_e +
        apply contains_one_local_cfun_call_ConsFunCall_es +
        apply contains_one_local_cfun_call_ConsFunCall_here +
        apply contains_one_local_cfun_call_Constr +
        apply contains_one_local_cfun_call_DestrCall_e +
        apply contains_one_local_cfun_call_DestrCall_es +
        apply contains_one_local_cfun_call_FunCall +
        apply contains_one_local_cfun_call_GenFunCall +
        apply contains_one_local_cfun_call_Let_e1 +
        apply contains_one_local_cfun_call_Let_e2 +
        apply contains_one_local_cfun_call_Match_bs +
        apply contains_one_local_cfun_call_Match_cases +
        apply contains_one_local_cfun_call_Match_e.

Ltac contains_at_most_sub_tac :=
      match goal with
      | [ H: contains_at_most_one_local_cfun_call ?qn ?tot' |- contains_at_most_one_local_cfun_call ?qn ?sub' ] =>
        apply contains_at_most_one_local_cfun_call_sub with (sub := sub') (tot := tot'); auto; subterm_tac; direct_subterm_tac
      end.

Ltac contains_at_most_ind_tac :=
          match goal with
        | [ H_one: contains_at_most_one_local_cfun_call ?qn ?tot' |- contains_at_most_one_local_cfun_call ?qn ?sub' ] =>
          clear - H_one; inversion H_one;
          [>  contains_no_contradiction_tac ||
             (left; contains_no_local_destr_tac;
              try (let H1 := fresh in let H2 := fresh in let H3 := fresh in inversion H_no_destr as [H1 [H2 H3]]
                                                                                                    || inversion H_no_destr);
              apply contains_no_local_cfun_call_direct_sub; [> | let E := fresh in intros; intro E; inversion E];
              intros;
              match goal with
              | [ H_dir: direct_subterm _ _ |- _ ] => inversion H_dir; subst; simpl in *; auto
              end)
            |]
        end;
          match goal with
          | [ Hx: contains_one_local_cfun_call _ _ |- _ ] =>
            inversion Hx; subst;
              try solve [right; contains_one_constrs_tac; solve [auto; try Forall_tail_tac]]
          end; simpl in *;
          try match goal with
              | [ H: contains_one_local_cfun_call_list ?qn (?x :: ?xs) |- _ ] =>
                inversion H; subst
              end;
          try solve [right; contains_one_constrs_tac; solve [auto]];
          try
            (left; apply contains_no_local_cfun_call_direct_sub; [> | let E := fresh in intros; intro E; inversion E];
             intros;
             match goal with
             | [ H_dir: direct_subterm _ _ |- _ ] =>
               inversion H_dir; subst; auto
             end;
             match goal with
             | [ H_f: Forall _ _ |- _ ] =>
               rewrite Forall_forall in H_f; apply H_f; solve [auto]
             end).

Lemma inline_cfuns_to_skeleton_preserves_typechecking: forall (p : program) (ctxt: ctxt) (e : expr) (tn tn' : TypeName) (qn : QName) (cs: list (ScopedName * expr)) (ts : list TypeName) (cfuns : cfun_sigs)
  (E: exists rest, cfuns ++ rest = (skeleton_cfun_sigs_l (program_skeleton p))),
    ((program_skeleton p) / ctxt |- e : tn) ->
    (forall qn', ~ In qn' (qn :: (map (fun x =>  fst (fst x)) cfuns)) ->
           contains_no_local_cfun_call qn' e) ->
    Forall (fun case => forall qn, ~ In qn (map (fun x : QName * list TypeName * TypeName => fst (fst x)) cfuns) ->
                           contains_no_local_cfun_call qn (snd case)) cs ->
    contains_at_most_one_local_cfun_call qn e ->
    lookup_cfun_sig_l (program_skeleton p) qn = Some (qn, ts, tn') /\
    program_skeleton p / (fst qn) :: ts |- (E_Match qn (E_Var 0) (index_list 1 ts) cs tn') : tn' ->
    (inline_cfuns_to_skeleton_partial p cfuns E) / ctxt |- (replace_cfun_call_by_match (local qn) cs ts tn' e) : tn.
Proof.
  intros p ctxt e tn tn' qn cs ts cfuns E_cfuns H_t H_no H_no_cs H_one H_t_cs.
  gen_dep (tn, ctxt); induction e using expr_strong_ind; simpl; intros.
  - inversion H_t; subst. apply T_Var; auto.
  - inversion H_t; subst. apply T_Constr with (cargs := cargs); auto.
    clear H2 H_t.
    gen_induction cargs ls; destruct cargs; inversion H5; subst; try apply ListTypeDeriv_Nil. simpl.
    apply ListTypeDeriv_Cons; auto.
    + inversion H; subst. apply H2; auto; try inline_cfun_to_skeleton_contains_no_tac.
      contains_at_most_sub_tac.
    + apply IHls with (cargs := cargs); auto; try Forall_tail_tac; try inline_cfun_to_skeleton_contains_no_tac.
      contains_at_most_ind_tac.
  - inversion H_t; subst. apply T_DestrCall with (dargs := dargs); auto.
    + apply IHe; auto; try inline_cfun_to_skeleton_contains_no_tac.
      contains_at_most_sub_tac.
    + clear H5 H_t.
    gen_induction dargs ls; destruct dargs; inversion H8; subst; try apply ListTypeDeriv_Nil. simpl.
    apply ListTypeDeriv_Cons; auto.
    * inversion H; subst. apply H2; auto.
      clear IHls H H2 H3; try inline_cfun_to_skeleton_contains_no_tac.
      contains_at_most_sub_tac.
    * apply IHls with (dargs := dargs); auto; try Forall_tail_tac; try inline_cfun_to_skeleton_contains_no_tac.
      contains_at_most_ind_tac.
  - inversion H_t; subst. apply T_FunCall with (argts := argts); auto.
    clear H4 H_t.
    gen_induction argts ls; destruct argts; inversion H6; subst; try apply ListTypeDeriv_Nil. simpl.
    apply ListTypeDeriv_Cons; auto.
    + inversion H; subst. apply H2; auto.
      clear IHls H H2 H3; try inline_cfun_to_skeleton_contains_no_tac.
      contains_at_most_sub_tac.
    + apply IHls with (argts := argts); auto; try Forall_tail_tac; try inline_cfun_to_skeleton_contains_no_tac.
      contains_at_most_ind_tac.
  - match_destruct_tac.
    + match_destruct_tac; try solve [inversion E_match]; simpl.
      inversion H_t; subst.
      name_eq_tac.
      inversion_clear H_t_cs as [H_lookup H_t_cs'].
      apply In_cfun_sig_lookup_cfun_sig_l in H5;
        rewrite H5 in H_lookup; inversion H_lookup; subst argts tn'; clear H_lookup;
          apply lookup_cfun_sig_in_cfun_sig_l in H5.
      inversion H_t_cs'; subst.
      apply T_Match with (bindings_exprs := ls) (bindings_types := ts) (ctorlist := ctorlist); auto.
      * assert (H_no': contains_no_local_cfun_call q e).
        { inversion H_one.
          - contains_no_contradiction_tac.
          - inversion H0; subst; auto. contradiction.
        }
        pose proof (replace_cfun_call_id_if_contains_none q e cs ts tn H_no') as E.
        rewrite E in *; clear E.
        apply IHe; auto; try inline_cfun_to_skeleton_contains_no_tac.
        left; auto.
      * assert (H_no': forall x, In x ls -> contains_no_local_cfun_call q x).
        { clear - H_one. intros; inversion H_one.
          - contains_no_contradiction_tac.
          - inversion H0; subst; try contradiction.
            rewrite Forall_forall in H5; auto.
        }
        clear - H H_no H8 H_no' H_one.
        generalize ts H8; clear H8; induction ls; intros ts0 H8; destruct ts0; inversion H8; subst; try apply ListTypeDeriv_Nil.
        apply ListTypeDeriv_Cons.
        -- inversion H; subst.
           pose proof (replace_cfun_call_id_if_contains_none q a cs ts tn (H_no' a (or_introl (eq_refl a)))) as E.
           rewrite E in *.
           apply H2; auto; try inline_cfun_to_skeleton_contains_no_tac.
           contains_at_most_sub_tac.
        -- apply IHls; auto; try Forall_tail_tac.
           intros. specialize (H_no qn' H0); auto.
           apply contains_no_local_cfun_call_direct_sub.
           ++ intros.
              contains_no_local_destr_tac. inversion H_no_destr as [_ [Hx Hy]].
              inversion H1; subst; auto.
           ++ intros.
              match goal with
              | [ H: contains_no_local_cfun_call _ (E_ConsFunCall _ _ _) |- _ ] =>
                unfold contains_no_local_cfun_call in H;
                  match type of H with
                  | forall e_sub e_arg args, subterm e_sub (E_ConsFunCall ?qn ?e ?ls) -> e_sub <> E_ConsFunCall _ _ _  =>
                    specialize (H (E_ConsFunCall qn e ls) e ls (Sub_Refl _))
                  end
              end.
              intro E. inversion E; subst. contradiction.
           ++ contains_at_most_ind_tac.
      * clear H H_no IHe H_t H_t_cs' H14.
        gen_induction ctorlist cs; destruct ctorlist; inversion H16; subst; try apply ListTypeDeriv'_Nil.
        simpl in *; inversion H_no_cs; subst; apply ListTypeDeriv'_Cons.
        -- assert (E: bindings_types = ts); [> | rewrite E in *; clear E].
           { clear - H11 H13. gen_dep (1, fst q :: ts).
             gen_induction (bindings_exprs, ts) bindings_types; destruct bindings_exprs; inversion H13; subst; destruct ts; auto; inversion H11; subst.
             f_equal. apply IHbindings_types with (bindings_exprs := bindings_exprs) (n := S n) (l := l); auto.
           }
           apply inline_partial_keeps_typecheck; auto.
        -- apply IHcs; auto. Forall_tail_tac.
    + inversion H_t; subst; clear H_t.
      * apply T_GlobalConsFunCall with (argts := argts); auto.
        -- apply IHe; auto; [> | contains_at_most_sub_tac].
           intros. specialize (H_no qn' H0); auto.
           contains_no_local_destr_tac. inversion H_no_destr as [_ [Hx Hy]]; auto.
        -- clear H5.
           gen_induction argts ls; destruct argts; inversion H8; subst; try apply ListTypeDeriv_Nil; simpl.
           inversion H; subst.
           apply ListTypeDeriv_Cons; auto.
           ++ apply H2; auto; [> | contains_at_most_sub_tac].
              intros. specialize (H_no qn' H0); auto.
              contains_no_local_destr_tac.
              inversion H_no_destr. apply H4; auto.
           ++ apply IHls; auto; [> | contains_at_most_ind_tac].
              intros. specialize (H_no qn' H0); auto.
              contains_no_local_destr_tac.
              apply contains_no_local_cfun_call_direct_sub; [> | intros; intro E; inversion E ].
              inversion H_no_destr as [_ [H1 H4]]. intros. inversion H6; subst; auto.
      * assert (H_dec: (exists x, In x cfuns /\ fst (fst x) = qn0) \/ ~ In qn0 (map (fun x => fst (fst x)) cfuns)).
        { clear. induction cfuns; simpl; auto.
          inversion IHcfuns.
          - inversion H as [x [Hin E]]; eauto.
          - pose proof (QName_dec (fst (fst a)) qn0).
            inversion H0; eauto.
            right. intro. inversion H2; auto.
        }
        inversion H_dec.
        -- inversion H0 as [x [H_in E]]; subst.
           apply T_LocalConsFunCall with (argts := argts); auto.
           ++ simpl. inversion E_cfuns.
              destruct x as [[qn' ts'] t]; simpl in *.
              pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as H_unique.
              unfold cfun_sigs_names_unique in H_unique.
              rewrite <- H1 in *.
              clear - H5 H_in H_unique.
              induction cfuns; inversion H_in; subst.
              ** left. simpl in *. inversion H_unique; subst.
                 inversion H5; auto.
                 apply in_map with (f := fun x => fst (fst x)) in H. simpl in *.
                 contradiction.
              ** right. IH_tac (try inversion H_unique; subst; auto).
                 inversion H5; auto; subst.
                 apply in_map with (f := fun x => fst (fst x)) in H; simpl in *.
                 exfalso; apply H2. In_sublist_tac.
           ++ apply IHe; auto; [> | contains_at_most_sub_tac ].
              intros. specialize (H_no qn' H1); auto.
              contains_no_local_destr_tac; inversion H_no_destr as [_ [Hx Hy]]; auto.
           ++ clear H5.
              assert (H_no': forall qn', ~ In qn' (qn :: (map (fun x => fst (fst x)) cfuns)) -> contains_no_local_cfun_call qn' e /\ forall x, In x ls -> contains_no_local_cfun_call qn' x).
              { intros. specialize (H_no qn' H1); contains_no_local_destr_tac; inversion H_no_destr as [_ [Hx Hy]]; auto. }
              clear H_no.
              gen_induction argts ls; destruct argts; inversion H8; subst; try apply ListTypeDeriv_Nil.
              simpl in *; apply ListTypeDeriv_Cons.
              ** inversion H; subst. apply H3; auto; [> | contains_at_most_sub_tac].
                 intros. specialize (H_no' qn' H1).
                 inversion H_no'; auto.
              ** apply IHls; try Forall_tail_tac; auto;
                   [> | intros; specialize (H_no' qn' H1);
                        inversion H_no';
                        split; auto].
                 clear - H_one.
                 inversion H_one.
                 --- left. unfold contains_no_local_cfun_call; intros.
                     inversion H0; subst.
                     +++ intro E. inversion E; subst.
                         contains_no_contradiction_tac.
                     +++ contains_no_local_destr_tac. inversion H_no_destr as [_ [H H3]].
                         inversion H2; subst; auto.
                         specialize (H3 e2 (or_intror H6)).
                         unfold contains_no_local_cfun_call in H3.
                         apply H3; auto.
                 --- match goal with
                     | [ Hx: contains_one_local_cfun_call _ _ |- _ ] =>
                       inversion Hx; subst;
                         try solve [right; contains_one_constrs_tac; solve [auto; try Forall_tail_tac]]
                     end;
                       try match goal with
                           | [ H: contains_one_local_cfun_call_list ?qn (?x :: ?xs) |- _ ] =>
                             inversion H; subst
                           end;
                       try solve [right; contains_one_constrs_tac; solve [auto]];
                       try
                         (left; apply contains_no_local_cfun_call_direct_sub; [> | let E := fresh in intros; intro E; inversion E; subst; contradiction];
                          intros;
                          match goal with
                          | [ H_dir: direct_subterm _ _ |- _ ] =>
                            inversion H_dir; subst; auto
                          end;
                          match goal with
                          | [ H_f: Forall _ _ |- _ ] =>
                            rewrite Forall_forall in H_f; apply H_f; auto
                          end).
        -- assert (Hx: ~ In qn0 (qn :: (map (fun x => fst (fst x)) cfuns)));
             [> let Hx := fresh in intro Hx; inversion Hx; subst; try name_refl_contradiction_tac; auto |].
          specialize (H_no _ Hx).
          apply replace_cfun_call_by_match_creates_no_cfun_calls with (qn' := qn) (cases := cs) (bts := ts) (rtype := tn') in H_no; auto.
           ++ simpl in H_no. rewrite E_match in H_no.
              unfold contains_no_local_cfun_call in H_no.
              match goal with
              | [  |- _ / _ |- (E_ConsFunCall ?qn ?e ?ls) : _ ] =>
                specialize (H_no (E_ConsFunCall qn e ls) e ls)
              end.
              exfalso; apply H_no; auto. subterm_tac.
           ++ match goal with
              | [ H: Forall ?P' cs |- Forall ?Q' cs ] =>
                apply Forall_impl with (P := P'); auto
              end.
  - inversion H_t; subst;
      [> apply T_GlobalGenFunCall with (argts := argts) | apply T_LocalGenFunCall with (argts := argts) ]; auto;
        clear H4 H_t;
        gen_induction argts ls; destruct argts; inversion H6; subst; try apply ListTypeDeriv_Nil; simpl;
          [>
           apply ListTypeDeriv_Cons; auto;
           [> inversion H; subst; apply H2; auto; [> | contains_at_most_sub_tac ];
            clear IHls H H2 H3;
            intros; specialize (H_no qn' H); auto;
            contains_no_local_destr_tac;
            apply H_no_destr; auto
           | apply IHls with (argts := argts); auto; try Forall_tail_tac;
             try inline_cfun_to_skeleton_contains_no_tac; contains_at_most_ind_tac
           ]
             .. ].
  - inversion H_t; subst. apply T_Match with (bindings_exprs := map (replace_cfun_call_by_match (local qn) cs ts tn') bindings_exprs) (bindings_types := bindings_types) (ctorlist := ctorlist); auto.
    + apply IHe; auto;
        try inline_cfun_to_skeleton_contains_no_tac.
      contains_at_most_sub_tac.
    + rewrite map_combine_fst; auto.
    + clear H14 H_t.
      gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion H11; try apply ListTypeDeriv_Nil; subst.
      simpl; simpl in H0; apply ListTypeDeriv_Cons.
      * inversion H0; subst.
        apply H3; auto;
          try inline_cfun_to_skeleton_contains_no_tac.
        contains_at_most_sub_tac.
      * apply IHbindings_exprs; auto; try Forall_tail_tac;
          try inline_cfun_to_skeleton_contains_no_tac.
        contains_at_most_ind_tac.
    + clear - H13.
      gen_induction ctorlist ls; destruct ctorlist; inversion H13; try apply Forall_nil; subst.
      simpl. apply Forall_cons; auto.
      destruct p. destruct a; auto.
    + rewrite map_map. rewrite map_length. simpl.
      clear - H H14 H_no H_one.
      gen_induction ctorlist ls; destruct ctorlist; inversion H14; try apply ListTypeDeriv'_Nil; subst.
      simpl. inversion_clear H. apply ListTypeDeriv'_Cons; auto.
      * apply H0; auto;
          try inline_cfun_to_skeleton_contains_no_tac.
        contains_at_most_sub_tac.
      * apply IHls; auto;
          try inline_cfun_to_skeleton_contains_no_tac.
        contains_at_most_ind_tac.
  - inversion H_t; subst. apply T_CoMatch with (bindings_exprs := map (replace_cfun_call_by_match (local qn) cs ts tn') bindings_exprs) (bindings_types := bindings_types) (dtorlist := dtorlist); auto.
    + rewrite map_combine_fst; auto.
    + clear H11 H_t.
      gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion H5; try apply ListTypeDeriv_Nil; subst.
      simpl; apply ListTypeDeriv_Cons.
      * inversion H0; subst.
        apply H3; auto;
          try inline_cfun_to_skeleton_contains_no_tac.
        contains_at_most_sub_tac.
      * apply IHbindings_exprs; auto; try Forall_tail_tac;
          try inline_cfun_to_skeleton_contains_no_tac.
        contains_at_most_ind_tac.
    + clear - H10.
      gen_induction dtorlist ls; destruct dtorlist; inversion H10; try apply Forall_nil; subst.
      simpl. apply Forall_cons; auto.
      do 2 destruct p. destruct a; auto.
    + rewrite map_map. simpl.
      clear - H H11 H_no H_one.
      gen_induction dtorlist ls; destruct dtorlist; inversion H11; try apply ListTypeDeriv'_Nil; subst.
      simpl. inversion_clear H. apply ListTypeDeriv'_Cons; auto.
      * apply H0; auto;
          try inline_cfun_to_skeleton_contains_no_tac.
        contains_at_most_sub_tac.
      * apply IHls; auto;
          try inline_cfun_to_skeleton_contains_no_tac.
        contains_at_most_ind_tac.
  - inversion H_t; subst.
    apply T_Let with (t1 := t1);
      match goal with
      | [ H: _ |- _ ] =>
        apply H; auto; try inline_cfun_to_skeleton_contains_no_tac; contains_at_most_sub_tac
      end.
Qed.



Lemma inline_cfuns_to_skeleton_partial_eq:
  forall (p : program) (cfuns: cfun_sigs) (e: expr) (ctxt : ctxt) (tn : TypeName)
    (E E': exists rest, cfuns ++ rest = skeleton_cfun_sigs_l (program_skeleton p)),
    inline_cfuns_to_skeleton_partial p cfuns E  / ctxt |- e : tn ->
    inline_cfuns_to_skeleton_partial p cfuns E' / ctxt |- e : tn.
Proof.
  intros p cfuns e ctxt tn E E' H_t.
  generalize dependent tn. generalize dependent ctxt.
  induction e using expr_strong_ind; intros ctxt tn' H_t; inversion H_t; subst; auto.
  - apply T_Var; auto.
  - apply T_Constr with (cargs := cargs); auto.
    clear H_t H2.
    gen_induction cargs ls; destruct cargs; inversion H5; inversion H; subst; try apply ListTypeDeriv_Nil.
    apply ListTypeDeriv_Cons; auto.
  - apply T_DestrCall with (dargs := dargs); auto.
    clear - H8 H.
    gen_induction dargs ls; destruct dargs; inversion H8; inversion H; subst; try apply ListTypeDeriv_Nil.
    apply ListTypeDeriv_Cons; auto.
  - apply T_FunCall with (argts := argts); auto.
    clear H_t H4.
    gen_induction argts ls; destruct argts; inversion H6; inversion H; subst; try apply ListTypeDeriv_Nil.
    apply ListTypeDeriv_Cons; auto.
  - apply T_GlobalConsFunCall with (argts := argts); auto.
    clear H_t H5.
    gen_induction argts ls; destruct argts; inversion H8; inversion H; subst; try apply ListTypeDeriv_Nil.
    apply ListTypeDeriv_Cons; auto.
  - apply T_LocalConsFunCall with (argts := argts); auto.
    clear H_t H5.
    gen_induction argts ls; destruct argts; inversion H8; inversion H; subst; try apply ListTypeDeriv_Nil.
    apply ListTypeDeriv_Cons; auto.
  - apply T_GlobalGenFunCall with (argts := argts); auto.
    clear H_t H4.
    gen_induction argts ls; destruct argts; inversion H6; inversion H; subst; try apply ListTypeDeriv_Nil.
    apply ListTypeDeriv_Cons; auto.
  - apply T_LocalGenFunCall with (argts := argts); auto.
    clear H_t H4.
    gen_induction argts ls; destruct argts; inversion H6; inversion H; subst; try apply ListTypeDeriv_Nil.
    apply ListTypeDeriv_Cons; auto.
  - apply T_Match with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types) (ctorlist := ctorlist); auto; subst.
    + clear - H0 H11.
      gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion H11; inversion H0; subst;
        try apply ListTypeDeriv_Nil.
      apply ListTypeDeriv_Cons; auto.
    + clear - H H14.
      gen_induction ctorlist ls; destruct ctorlist; inversion H14; inversion H; subst; try apply ListTypeDeriv'_Nil.
      simpl. apply ListTypeDeriv'_Cons; auto.
  - apply T_CoMatch with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types) (dtorlist := dtorlist); auto; subst.
    + clear - H0 H5.
      gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion H5; inversion H0; subst;
        try apply ListTypeDeriv_Nil.
      apply ListTypeDeriv_Cons; auto.
    + clear - H H11.
      gen_induction dtorlist ls; destruct dtorlist; inversion H11; inversion H; subst; try apply ListTypeDeriv'_Nil.
      simpl. apply ListTypeDeriv'_Cons; auto.
  - eapply T_Let; eauto.
Qed.

Lemma inline_cfuns_to_skeleton_partial_full_ListTypeDeriv_helper:
  forall (sk sk' : skeleton) (ctxt: ctxt) (es : list expr) (ts: list TypeName),
    Forall (fun e => forall c t, sk / c |- e : t -> sk' / c |- e : t) es ->
    sk  // ctxt ||- es :: ts ->
    sk' // ctxt ||- es :: ts.
Proof.
  intros sk sk' ctxt es ts H_f H_t.
  gen_induction ts es; destruct ts; inversion H_t; inversion H_f; subst; try apply ListTypeDeriv_Nil.
  apply ListTypeDeriv_Cons; auto.
Qed.

Lemma inline_cfuns_to_skeleton_partial_full_ListTypeDeriv_bindings_helper:
  forall (sk sk' : skeleton) (ctxt: ctxt) (es : list expr) (ts: list TypeName),
    Forall (fun e => forall c t, sk / c |- e : t -> sk' / c |- e : t) (map fst (combine es ts)) ->
    sk  // ctxt ||- es :: ts ->
    sk' // ctxt ||- es :: ts.
Proof.
  intros sk sk' ctxt es ts H_f H_t.
  gen_induction ts es; destruct ts; inversion H_t; inversion H_f; subst; try apply ListTypeDeriv_Nil.
  apply ListTypeDeriv_Cons; auto.
Qed.

Lemma inline_cfuns_to_skeleton_partial_full_ListTypeDeriv'_helper:
  forall {A : Type} (sk sk' : skeleton) (ctxts: list A) (cs : list (ScopedName * expr)) (ts: list TypeName) (f: A -> ctxt),
    Forall (fun e => forall c t, sk / c |- e : t -> sk' / c |- e : t) (map snd cs) ->
    sk  /// map f ctxts |||- map snd cs ::: ts ->
    sk' /// map f ctxts |||- map snd cs ::: ts.
Proof.
  intros A sk sk' ctxts es ts f H_f H_t.
  gen_induction (ctxts, ts) es; destruct ts; destruct ctxts; inversion H_t; inversion H_f; subst; try apply ListTypeDeriv'_Nil.
  simpl.
  apply ListTypeDeriv'_Cons; auto.
Qed.

Ltac typeDeriv_apply_tac :=
  multimatch goal with
  | [  |- _ / _ |- (E_Var _) : _ ] => apply T_Var
  | [ cargs: list TypeName |- _ / _ |- (E_Constr _ _) : _ ] =>
    apply (T_Constr _ _ _ _ cargs)
  | [ dargs: list TypeName |- _ / _ |- (E_DestrCall _ _ _) : _ ] =>
    apply (T_DestrCall _ _ _ _ _ dargs)
  | [ args: list TypeName |- _ / _ |- (E_FunCall _ _) : _ ] =>
    apply (T_FunCall _ _ _ _ args)
  | [ args: list TypeName |- _ / _ |- (E_GenFunCall _ _) : _ ] =>
    apply (T_GlobalGenFunCall _ _ _ _ args) +
    apply (T_LocalGenFunCall _ _ _ _ args)
  | [ args: list TypeName |- _ / _ |- (E_ConsFunCall _ _ _) : _ ] =>
    apply (T_GlobalConsFunCall _ _ _ _ _ args) +
    apply (T_LocalConsFunCall _ _ _ _ _ args)
  | [ b_exprs: list expr,
               b_types: list TypeName,
                        ctorlist: list (ScopedName * list TypeName)
      |- _ / _ |- (E_Match _ _ _ _ _) : _ ] =>
    apply (T_Match _ _ _ _ b_exprs b_types _ _ _ ctorlist)
  | [ b_exprs: list expr,
               b_types: list TypeName,
                        dtorlist: list (ScopedName * list TypeName * TypeName)
      |- _ / _ |- (E_CoMatch _ _ _) : _ ] =>
    apply (T_CoMatch _ _ _ dtorlist b_exprs b_types)
  | [ t: TypeName |- _ / _ |- (E_Let _ _) : _ ] =>
    apply (T_Let _ _ _ _ t)
  end.

Lemma inline_cfuns_to_skeleton_partial_full:
  forall (p : program) (e : expr) (ctxt: ctxt) (tn: TypeName)
    (E: exists rest, (skeleton_cfun_sigs_l (program_skeleton p)) ++ rest = skeleton_cfun_sigs_l (program_skeleton p)),
    (program_skeleton p / ctxt |- e : tn) ->
    inline_cfuns_to_skeleton_partial p (skeleton_cfun_sigs_l (program_skeleton p)) E / ctxt |- e : tn.
Proof.
  intros p e ctxt tn E_sigs H_t.
  generalize dependent tn; generalize dependent ctxt.
  induction e using expr_strong_ind; intros; inversion H_t; subst; clear H_t;
    try typeDeriv_apply_tac; auto;
      try solve [apply (inline_cfuns_to_skeleton_partial_full_ListTypeDeriv_helper (program_skeleton p)); auto];
      try solve [apply (inline_cfuns_to_skeleton_partial_full_ListTypeDeriv_bindings_helper (program_skeleton p)); auto];
      try solve [apply inline_cfuns_to_skeleton_partial_full_ListTypeDeriv'_helper with (sk := program_skeleton p); auto].
Qed.

Lemma inline_partial_reflects_typecheck: forall (p : program) (e : expr) (cfuns : cfun_sigs) (ctxt : ctxt) (tn : TypeName)
                                        (E: exists rest, cfuns ++ rest = skeleton_cfun_sigs_l (program_skeleton p)),
    (inline_cfuns_to_skeleton_partial p cfuns E) / ctxt |- e : tn ->
    ((program_skeleton p) / ctxt |- e : tn).
Proof.
  intros p e cfuns ctxt tn E_cfuns H_t.
  gen_dep tn.
  gen_dep ctxt.
  induction e using expr_strong_ind; intros; inversion H_t; subst; clear H_t;
    try typeDeriv_apply_tac; auto;
      try solve [apply (inline_cfuns_to_skeleton_partial_full_ListTypeDeriv_helper (inline_cfuns_to_skeleton_partial p cfuns E_cfuns)); auto];
      try solve [apply (inline_cfuns_to_skeleton_partial_full_ListTypeDeriv_bindings_helper (inline_cfuns_to_skeleton_partial p cfuns E_cfuns)); auto];
      try solve [apply inline_cfuns_to_skeleton_partial_full_ListTypeDeriv'_helper with (sk := inline_cfuns_to_skeleton_partial p cfuns E_cfuns); auto].
  simpl in *. inversion E_cfuns. rewrite <- H0. In_sublist_tac.
Qed.

Lemma contains_only_local_cfuns_if_tc: forall (sk: skeleton) (e : expr) (tn : TypeName) (ctxt : ctxt) (qn : QName),
    (sk / ctxt |- e : tn) ->
    ~In qn (map (fun x => fst (fst x)) (skeleton_cfun_sigs_l sk)) ->
    contains_no_local_cfun_call qn e.
Proof.
  intros sk e tn ctxt qn H_t nH_in.
  gen_dep (ctxt, tn);
    induction e using expr_strong_ind; intros;
      try match goal with
          | [  |- contains_no_local_cfun_call _ (E_ConsFunCall ?sn _ _) ] =>
            destruct sn
          end;
    try (apply contains_no_local_cfun_call_direct_sub; [> | solve [let E := fresh in intros; intro E; inversion E]];
      intros; match goal with
              | [ H_dir: direct_subterm _ _ |- _ ] => inversion H_dir; subst
              end);
    inversion_clear H_t; subst;
    try solve
        [match goal with
         | [ H:_  |- _ ] => eapply H; eauto
         end];
    try solve
        [match goal with
         | [ H_in: In ?esub ?ls,
                   H_t: _ // _ ||- ?ls :: ?cargs,
                        H_f: Forall _ ?ls |- contains_no_local_cfun_call ?qn ?esub ] =>
           clear - H_in H_f H_t; gen_induction cargs ls; destruct cargs; inversion H_in; inversion H_t; inversion H_f; subst; IH_auto_tac
         end];
    try solve
        [match goal with
         | [ H_in: In ?esub (map _ (combine ?exs ?ts)),
                   H_t: _ // _ ||- ?es :: ?ts,
                        H_f: Forall _ (map _ (combine ?es ?ts)) |- _ ] =>
           clear - H_in H_f H_t; gen_induction ts exs; destruct ts; simpl in *; inversion H_t; inversion H_in; inversion H_f; subst; eauto
         end];
    try solve
        [match goal with
         | [ H_in: In ?esub (map _ ?ls),
                   H_t: _ /// map _ ?ctxts |||- map _ ?ls ::: _,
                        H_f: Forall _ (map _ ?ls)
             |- contains_no_local_cfun_call _ ?esub ] =>
           clear - H_in H_f H_t;
           gen_induction ctxts ls; destruct ctxts; inversion H_t; inversion H_in; inversion H_f; subst; eauto
         end].
  apply contains_no_local_cfun_call_direct_sub.
  - intros. inversion H3; subst; try solve [eapply IHe; eauto].
    clear - H H6 H2.
    gen_induction argts ls; destruct argts; inversion H6; inversion H2; inversion H; subst; eauto.
  - intros. intro E; inversion E; subst.
    apply in_map with (f := fun x => fst (fst x)) in H0; simpl in *; auto.
Qed.

Lemma replace_creates_from_cases: forall (e : expr) (cs : list (ScopedName * expr)) (argts : list TypeName) (rt : TypeName) (qn qn_rep : QName),
    contains_one_local_cfun_call qn_rep e ->
    contains_no_local_cfun_call qn e ->
    contains_one_local_cfun_call_list qn (map snd cs) ->
    contains_one_local_cfun_call qn (replace_cfun_call_by_match (local qn_rep) cs argts rt e).
Proof.
  intros e cs argts rt qn qn_rep H_one_e H_no_e H_one_cs.
  induction e using expr_strong_ind; simpl;
    inversion_clear H_one_e; contains_no_local_destr_tac;
      let rec foo :=
          match goal with
          | [ H: _ /\ _ |- _ ] => inversion_clear H; foo
          | _ => idtac
          end in
      foo;
        subst;
        try solve
            [contains_one_constrs_tac;
             try solve [rewrite replace_cfun_call_id_if_contains_none; auto];
             induction ls; simpl;
             try solve [match goal with
                        | [ H: contains_one_local_cfun_call_list _ [] |- _ ] => inversion H
                        end];
             let H_head := fresh "H_head" in
             let H_tail := fresh "H_tail" in
             inversion_clear H as [|_x _y H_head H_tail];
             match goal with
             | [ H: contains_one_local_cfun_call_list _ (_ :: _) |- _ ] =>
               inversion H; subst
             end;
             [> apply contains_one_local_cfun_call_list_here; auto;
              rewrite <- Forall_map;
              match goal with
              | [ H_f: Forall _ ?ls |- Forall _ ?ls ] =>
                rewrite Forall_forall; intros;
                rewrite Forall_forall in H_f
              end;
              rewrite replace_cfun_call_id_if_contains_none; eauto
             | apply contains_one_local_cfun_call_list_there; auto;
               rewrite replace_cfun_call_id_if_contains_none; auto
            ]].
  - contains_one_constrs_tac; auto.
    rewrite <- Forall_map. rewrite Forall_forall; intros.
    rewrite Forall_forall in H1.
    rewrite replace_cfun_call_id_if_contains_none; auto.
  - match_destruct_tac;
      [> match_destruct_tac; inversion E_match;
       name_eq_tac; contradiction|].
    apply contains_one_local_cfun_call_ConsFunCall_e; auto.
    rewrite <- Forall_map. rewrite Forall_forall; intros.
    rewrite Forall_forall in H2.
    rewrite replace_cfun_call_id_if_contains_none; auto.
  - match_destruct_tac;
      [> match_destruct_tac; inversion E_match;
       name_eq_tac; contradiction|].
    apply contains_one_local_cfun_call_ConsFunCall_es; auto;
      [> rewrite replace_cfun_call_id_if_contains_none; auto |].
    clear E_match. induction ls; inversion H2; subst; simpl; inversion_clear H.
    + apply contains_one_local_cfun_call_list_here; auto.
      rewrite <- Forall_map; rewrite Forall_forall; intros.
      rewrite Forall_forall in H9.
      rewrite replace_cfun_call_id_if_contains_none; auto.
    + apply contains_one_local_cfun_call_list_there; auto.
      rewrite replace_cfun_call_id_if_contains_none; auto.
  - name_refl_tac.
    apply contains_one_local_cfun_call_Match_cases; auto.
    rewrite Forall_forall; intros. apply H5.
    apply In_sublist with (tot := ls) in H3; auto.
    apply map_combine_fst_sublist.
  - apply contains_one_local_cfun_call_Match_e; auto;
      rewrite map_map; simpl; rewrite <- Forall_map; rewrite Forall_forall; intros;
        match goal with
        | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
          rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f
        end;
        rewrite replace_cfun_call_id_if_contains_none; auto;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; in_map_tac; auto
          end.
  - apply contains_one_local_cfun_call_Match_bs; auto;
      try rewrite replace_cfun_call_id_if_contains_none; auto;
        try (rewrite map_map; simpl; rewrite <- Forall_map; rewrite Forall_forall; intros;
        match goal with
        | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
          rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f
        end;
        rewrite replace_cfun_call_id_if_contains_none; auto;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; in_map_tac; auto
          end).
    rewrite map_map; simpl.
    match goal with
    | [ H_one: contains_one_local_cfun_call_list _ (map _ ?ls) |- contains_one_local_cfun_call_list _ (map _ ?ls) ] =>
      induction ls; simpl; inversion H_one; subst
    end.
    + apply contains_one_local_cfun_call_list_here.
      * rewrite <- Forall_map; rewrite Forall_forall; intros;
          match goal with
          | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
            rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f;
              rewrite replace_cfun_call_id_if_contains_none; auto
          end;
        match goal with
        | [ H: _ |- _ ] =>
          apply H; in_map_tac; auto
        end.
      * match goal with
        | [ H_f: Forall _ (map _ (?a :: _)) |- contains_one_local_cfun_call _ (replace_cfun_call_by_match _ _ _ _ (_ ?a)) ] =>
          inversion_clear H_f as [|_x _y Hx _];
            apply Hx; auto
        end;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; simpl; solve [auto]
          end.
    + apply contains_one_local_cfun_call_list_there; auto.
      * IH_tac auto;
          try match goal with
              | [ H_f: forall x, In x (map _ (_ :: ?ls)) -> _ |- forall x, In x (map _ ?ls) -> _ ] =>
                rewrite <- Forall_forall; rewrite <- Forall_forall in H_f
              end;
          Forall_tail_tac.
      * rewrite replace_cfun_call_id_if_contains_none; auto;
        match goal with
        | [ H: _ |- _ ] =>
          apply H; in_map_tac; auto
        end.
  - apply contains_one_local_cfun_call_Match_cases; auto;
      try rewrite replace_cfun_call_id_if_contains_none; auto;
        try (rewrite map_map; simpl; rewrite <- Forall_map; rewrite Forall_forall; intros;
        match goal with
        | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
          rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f
        end;
        rewrite replace_cfun_call_id_if_contains_none; auto;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; in_map_tac; auto
          end).
    rewrite map_map; simpl.
    match goal with
    | [ H_one: contains_one_local_cfun_call_list _ (map _ ?ls) |- contains_one_local_cfun_call_list _ (map _ ?ls) ] =>
      induction ls; simpl; inversion H_one; subst
    end.
    + apply contains_one_local_cfun_call_list_here.
      * rewrite <- Forall_map; rewrite Forall_forall; intros;
          match goal with
          | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
            rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f;
              rewrite replace_cfun_call_id_if_contains_none; auto
          end;
        match goal with
        | [ H: _ |- _ ] =>
          apply H; in_map_tac; auto
        end.
      * match goal with
        | [ H_f: Forall _ (map _ (?a :: _)) |- contains_one_local_cfun_call _ (replace_cfun_call_by_match _ _ _ _ (_ ?a)) ] =>
          inversion_clear H_f as [|_x _y Hx _];
            apply Hx; auto
        end;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; simpl; solve [auto]
          end.
    + apply contains_one_local_cfun_call_list_there; auto.
      * IH_tac auto;
          try match goal with
              | [ H_f: forall x, In x (map _ (_ :: ?ls)) -> _ |- forall x, In x (map _ ?ls) -> _ ] =>
                rewrite <- Forall_forall; rewrite <- Forall_forall in H_f
              end;
          Forall_tail_tac.
      * rewrite replace_cfun_call_id_if_contains_none; auto;
        match goal with
        | [ H: _ |- _ ] =>
          apply H; in_map_tac; auto
        end.
  - apply contains_one_local_cfun_call_CoMatch_bs; auto;
      try rewrite replace_cfun_call_id_if_contains_none; auto;
        try (rewrite map_map; simpl; rewrite <- Forall_map; rewrite Forall_forall; intros;
        match goal with
        | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
          rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f
        end;
        rewrite replace_cfun_call_id_if_contains_none; auto;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; in_map_tac; auto
          end).
    rewrite map_map; simpl.
    match goal with
    | [ H_one: contains_one_local_cfun_call_list _ (map _ ?ls) |- contains_one_local_cfun_call_list _ (map _ ?ls) ] =>
      induction ls; simpl; inversion H_one; subst
    end.
    + apply contains_one_local_cfun_call_list_here.
      * rewrite <- Forall_map; rewrite Forall_forall; intros;
          match goal with
          | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
            rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f;
              rewrite replace_cfun_call_id_if_contains_none; auto
          end;
        match goal with
        | [ H: _ |- _ ] =>
          apply H; in_map_tac; auto
        end.
      * match goal with
        | [ H_f: Forall _ (map _ (?a :: _)) |- contains_one_local_cfun_call _ (replace_cfun_call_by_match _ _ _ _ (_ ?a)) ] =>
          inversion_clear H_f as [|_x _y Hx _];
            apply Hx; auto
        end;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; simpl; solve [auto]
          end.
    + apply contains_one_local_cfun_call_list_there; auto.
      * IH_tac auto;
          try match goal with
              | [ H_f: forall x, In x (map _ (_ :: ?ls)) -> _ |- forall x, In x (map _ ?ls) -> _ ] =>
                rewrite <- Forall_forall; rewrite <- Forall_forall in H_f
              end;
          Forall_tail_tac.
      * rewrite replace_cfun_call_id_if_contains_none; auto;
        match goal with
        | [ H: _ |- _ ] =>
          apply H; in_map_tac; auto
        end.
  - apply contains_one_local_cfun_call_CoMatch_cocases; auto;
      try rewrite replace_cfun_call_id_if_contains_none; auto;
        try (rewrite map_map; simpl; rewrite <- Forall_map; rewrite Forall_forall; intros;
        match goal with
        | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
          rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f
        end;
        rewrite replace_cfun_call_id_if_contains_none; auto;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; in_map_tac; auto
          end).
    rewrite map_map; simpl.
    match goal with
    | [ H_one: contains_one_local_cfun_call_list _ (map _ ?ls) |- contains_one_local_cfun_call_list _ (map _ ?ls) ] =>
      induction ls; simpl; inversion H_one; subst
    end.
    + apply contains_one_local_cfun_call_list_here.
      * rewrite <- Forall_map; rewrite Forall_forall; intros;
          match goal with
          | [ H_in: In _ ?ls, H_f: Forall _ (map _ ?ls) |- _ ] =>
            rewrite <- Forall_map in H_f; rewrite Forall_forall in H_f;
              rewrite replace_cfun_call_id_if_contains_none; auto
          end;
        match goal with
        | [ H: _ |- _ ] =>
          apply H; in_map_tac; auto
        end.
      * match goal with
        | [ H_f: Forall _ (map _ (?a :: _)) |- contains_one_local_cfun_call _ (replace_cfun_call_by_match _ _ _ _ (_ ?a)) ] =>
          inversion_clear H_f as [|_x _y Hx _];
            apply Hx; auto
        end;
          match goal with
          | [ H: _ |- _ ] =>
            apply H; simpl; solve [auto]
          end.
    + apply contains_one_local_cfun_call_list_there; auto.
      * IH_tac auto;
          try match goal with
              | [ H_f: forall x, In x (map _ (_ :: ?ls)) -> _ |- forall x, In x (map _ ?ls) -> _ ] =>
                rewrite <- Forall_forall; rewrite <- Forall_forall in H_f
              end;
          Forall_tail_tac.
      * rewrite replace_cfun_call_id_if_contains_none; auto;
        match goal with
        | [ H: _ |- _ ] =>
          apply H; in_map_tac; auto
        end.
  - contains_one_constrs_tac; auto;
      solve [rewrite replace_cfun_call_id_if_contains_none; auto].
  - contains_one_constrs_tac; auto;
      solve [rewrite replace_cfun_call_id_if_contains_none; auto].
Qed.

Lemma no_cfuns_outside_inline_tc: forall (p: program) (e : expr) (tn : TypeName) (ctxt : ctxt)
  (cfuns: cfun_sigs) (E: exists rest, cfuns ++ rest = skeleton_cfun_sigs_l (program_skeleton p)),
    (program_skeleton p / ctxt |- e : tn) ->
    (forall qn, ~In qn (map (fun x => fst (fst x)) cfuns) -> contains_no_local_cfun_call qn e) ->
    (inline_cfuns_to_skeleton_partial p cfuns E) / ctxt |- e : tn.
Proof.
  intros p e tn ctxt cfuns E H_t nH_in.
  gen_dep (tn, ctxt).
  induction e using expr_strong_ind; intros; inversion H_t; subst; clear H_t;
      try solve
          [typeDeriv_apply_tac; eauto;
           try match goal with
           | [ H_f: Forall _ ?ls, H_t: _ // _ ||- ?ls :: ?cargs |- _ // _ ||- ?ls :: ?cargs ] =>
             clear - H_f H_t nH_in; gen_induction cargs ls; destruct cargs; inversion H_t; inversion H_f; subst;
             [> apply ListTypeDeriv_Nil
             | apply ListTypeDeriv_Cons; eauto
             ]
           end;
           match goal with
           | [ Hx: _ |- _ ] =>
             eapply Hx; eauto; clear - nH_in;
             let qnx := fresh in
             let Hxx := fresh in
             intros qnx Hxx;
             specialize (nH_in qnx Hxx);
             contains_no_local_destr_tac;
             try inversion H_no_destr;
             try (let H1 := fresh in let H2 := fresh in let H3 := fresh in inversion H_no_destr as [H1 [H2 H3]]);
             eauto;
             try (apply contains_no_local_cfun_call_direct_sub;
                  [> | let E := fresh in intros; intro E; inversion E]; intros;
                  match goal with
                  | [ H_dir: direct_subterm _ _ |- _ ] =>
                    inversion H_dir; eauto
                  end)
           end].

  - inversion E as [rest E']; rewrite <- E' in *.
    apply in_app_iff in H5. inversion H5.
    + typeDeriv_apply_tac; auto.
      * apply IHe; auto.
        intros.
        specialize (nH_in qn0 H1). contains_no_local_destr_tac; inversion H_no_destr as [_ [Hx Hy]]; auto.
      * apply in_map with (f := fun x => fst (fst x)) in H0. simpl in H0.
        clear - H nH_in H0 H8.
        gen_induction argts ls; destruct argts; inversion H8; inversion H; subst;
          [> apply ListTypeDeriv_Nil | apply ListTypeDeriv_Cons ].
        -- eapply H12; eauto.
           clear - nH_in. intros. specialize (nH_in qn0 H).
           contains_no_local_destr_tac. inversion H_no_destr as [_ [Hx Hy]]; auto.
        -- eapply IHls; eauto. clear - nH_in H0.
           intros. specialize (nH_in qn0 H).
           contains_no_local_destr_tac. inversion H_no_destr as [_ [H1 H2]].
           apply contains_no_local_cfun_call_direct_sub.
           ++ intros. inversion H3; subst; auto.
           ++ intros. intro E. inversion E; subst. auto.
    + pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as H_unique.
      unfold cfun_sigs_names_unique in H_unique.
      apply in_map with (f := fun x => fst (fst x)) in H0; simpl in *.
      rewrite <- E' in *.
      assert (Hx: ~ In qn (map (fun x => fst (fst x)) cfuns)).
      { clear - H0 H_unique.
        intro.
        induction cfuns; inversion H; subst.
        - inversion H_unique; subst.
          apply H3. In_sublist_tac.
        - inversion H_unique; subst.
          apply IHcfuns; auto.
      }
      specialize (nH_in qn Hx).
      contains_no_contradiction_tac.
  - typeDeriv_apply_tac; auto.
    + apply IHe; auto.
      intros. specialize (nH_in qn H1).
      contains_no_local_destr_tac. inversion H_no_destr; auto.
    + clear - H0 nH_in H11.
      gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion H11; inversion H0;
        subst; [> apply ListTypeDeriv_Nil | apply ListTypeDeriv_Cons ].
      * apply H10; auto.
        intros. specialize (nH_in qn H). contains_no_local_destr_tac.
        inversion H_no_destr as [_ [Hx _]]. simpl in *; auto.
      * apply IHbindings_exprs; auto.
        intros. specialize (nH_in qn H). contains_no_local_destr_tac.
        apply contains_no_local_cfun_call_direct_sub; [> | intros; let E := fresh in intro E; inversion E].
        inversion H_no_destr as [Hx1 [Hx2 Hx3]]. simpl in *; auto.
        intros. inversion H1; subst; auto.
    + clear - H nH_in H14.
      gen_induction ctorlist ls; destruct ctorlist; inversion H14; inversion H; subst;
        [> apply ListTypeDeriv'_Nil | simpl in *; apply ListTypeDeriv'_Cons ].
      * apply H11; auto.
        intros. specialize (nH_in qn H0); contains_no_local_destr_tac.
        inversion H_no_destr as [_ [_ Hx]]; simpl in *; auto.
      * apply IHls; auto.
        intros. specialize (nH_in qn H0); contains_no_local_destr_tac.
        inversion_clear H_no_destr as [Hx1 [Hx2 Hx3]].
        apply contains_no_local_cfun_call_direct_sub; [> | intros; let E := fresh in intro E; inversion E].
        intros. inversion H1; subst; simpl in *; auto.
  - typeDeriv_apply_tac; auto.
    + clear - H0 nH_in H5. rename H5 into H11.
      gen_induction bindings_types bindings_exprs; destruct bindings_types; inversion H11; inversion H0;
        subst; [> apply ListTypeDeriv_Nil | apply ListTypeDeriv_Cons ].
      * apply H10; auto.
        intros. specialize (nH_in qn H). contains_no_local_destr_tac.
        inversion H_no_destr. simpl in *; auto.
      * apply IHbindings_exprs; auto.
        intros. specialize (nH_in qn H). contains_no_local_destr_tac.
        apply contains_no_local_cfun_call_direct_sub; [> | intros; let E := fresh in intro E; inversion E].
        inversion H_no_destr. simpl in *; auto.
        intros. inversion H3; subst; auto.
    + clear - H nH_in H11. rename H11 into H14.
      gen_induction dtorlist ls; destruct dtorlist; inversion H14; inversion H; subst;
        [> apply ListTypeDeriv'_Nil | simpl in *; apply ListTypeDeriv'_Cons ].
      * apply H11; auto.
        intros. specialize (nH_in qn H0); contains_no_local_destr_tac.
        inversion H_no_destr; simpl in *; auto.
      * apply IHls; auto.
        intros. specialize (nH_in qn H0); contains_no_local_destr_tac.
        inversion_clear H_no_destr.
        apply contains_no_local_cfun_call_direct_sub; [> | intros; let E := fresh in intro E; inversion E].
        intros. inversion H3; subst; simpl in *; auto.
Qed.

Lemma contains_one_local_list_app: forall (qn : QName) (l r: list expr),
    contains_one_local_cfun_call_list qn (l ++ r) ->
    (contains_one_local_cfun_call_list qn l /\ Forall (contains_no_local_cfun_call qn) r)
    \/ contains_one_local_cfun_call_list qn r /\ Forall (contains_no_local_cfun_call qn) l.
Proof.
  intros qn l r H.
  induction l; simpl in *.
  - right; split; auto.
  - inversion H; subst.
    + left. split; try Forall_sublist_tac.
      apply contains_one_local_cfun_call_list_here; auto; Forall_sublist_tac.
    + specialize (IHl H3). inversion IHl as [[Hl Hr] | [Hr Hl]].
      * left. split; auto. apply contains_one_local_cfun_call_list_there; auto.
      * right. split; auto.
Qed.

Lemma contains_at_most_sublist: forall (qn : QName) (sub tot: list expr),
    sublist sub tot ->
    contains_at_most_one_local_cfun_call_list qn tot ->
    contains_at_most_one_local_cfun_call_list qn sub.
Proof.
  intros qn sub tot H_sub H_most.
  inversion_clear H_most.
  - left. Forall_sublist_tac.
  - gen_induction sub tot; inversion_clear H; inversion H_sub; subst; try solve [left; apply Forall_nil].
    + left. Forall_sublist_tac.
    + right. apply contains_one_local_cfun_call_list_here; auto.
      Forall_sublist_tac.
    + apply IHtot; try right; auto.
    + specialize (IHtot H0 sub0 H3).
      inversion IHtot.
      * left. apply Forall_cons; auto.
      * right. apply contains_one_local_cfun_call_list_there; auto.
Qed.


Ltac contains_at_most_sublist_tac :=
  match goal with
  | [ H: contains_at_most_one_local_cfun_call_list ?qn' ?tot' |-
      contains_at_most_one_local_cfun_call_list ?qn' ?sub' ] =>
    apply contains_at_most_sublist with (sub := sub') (tot := tot'); auto; try sublist_tac
  end.

Lemma inline_cfuns_to_skeleton_preserves_typechecking_list_helper: forall (p : program) (ctxt : ctxt) (e: expr) (tn : TypeName) (cfun_bods_inlined : cfun_bods) (cfun_sigs_inlined cfun_sigs_remaining: cfun_sigs)
             (E_sigs: cfun_sigs_remaining ++ cfun_sigs_inlined = skeleton_cfun_sigs_l (program_skeleton p)),
    map fst cfun_bods_inlined = map (fun x => fst (fst x)) cfun_sigs_inlined ->
    ((program_skeleton p) / ctxt |- e : tn) ->
    inline_ordered_cfun cfun_bods_inlined ->
    Forall (fun qn => contains_at_most_one_local_cfun_call_list qn (e :: map snd (flat_map snd cfun_bods_inlined))) (map (fun x => fst (fst x)) (cfun_sigs_inlined)) ->
    cfun_bods_l_typecheck (program_skeleton p) cfun_bods_inlined ->
    (inline_cfuns_to_skeleton_partial
       p cfun_sigs_remaining
       (ex_intro (fun rest => cfun_sigs_remaining ++ rest = skeleton_cfun_sigs_l (program_skeleton p))
                 cfun_sigs_inlined E_sigs))
      / ctxt |- (replace_local_cfun_calls cfun_bods_inlined cfun_sigs_inlined e) : tn.
Proof.
  intros p ctxt e tn cfun_bods_inlined cfun_sigs_inlined cfun_sigs_remaining E_sigs E_fst H_t H_inline H_most H_t_bods.
  gen_induction (e, cfun_sigs_remaining, cfun_bods_inlined) cfun_sigs_inlined.
  - assert (E_sigs' : cfun_sigs_remaining = skeleton_cfun_sigs_l (program_skeleton p)).
    { rewrite <- E_sigs. rewrite app_nil_r; auto. }
    subst.
    apply inline_cfuns_to_skeleton_partial_full.
    destruct cfun_bods_inlined; try solve [inversion E_fst].
    simpl; auto.
  - destruct cfun_bods_inlined; try solve [inversion E_fst].
    simpl.
    simpl in E_fst. inversion E_fst as [[E_head E_tail]]; clear E_fst.
    assert (E_assoc: (cfun_sigs_remaining ++ [a]) ++ cfun_sigs_inlined = skeleton_cfun_sigs_l (program_skeleton p));
      [> rewrite <- app_assoc; simpl; auto|].
    inversion H_inline; subst. inversion H_t_bods as [|_x _y H_t_head H_t_tail]; subst; clear H_t_bods.
    specialize (IHcfun_sigs_inlined
                  cfun_bods_inlined E_tail H1 H_t_tail (cfun_sigs_remaining ++ [a]) E_assoc).
    simpl in *.
    specialize (IHcfun_sigs_inlined (replace_cfun_call_by_match (local qn) cs (snd (fst a)) (snd a) e)).
    match type of IHcfun_sigs_inlined with
    | ?x -> ?y =>
      assert (Hx: x); [> | specialize (IHcfun_sigs_inlined Hx); cut y; auto]
    end.
    {
      assert (Ex: exists rest, (skeleton_cfun_sigs_l (program_skeleton p)) ++ rest = skeleton_cfun_sigs_l (program_skeleton p));
      [> eexists; eapply app_nil_r |].
      apply inline_partial_reflects_typecheck with (cfuns := (skeleton_cfun_sigs_l (program_skeleton p))) (E := Ex).
      apply inline_cfuns_to_skeleton_preserves_typechecking; auto.
      - intro. simpl. intros. apply contains_only_local_cfuns_if_tc with (qn := qn') in H_t; auto.
      - inversion H_t_head as [qnt [argst [tt [H_lookup H_tt]]]].
        inversion H_tt; subst.
        clear - H15.
        gen_induction ctorlist cs; destruct ctorlist; inversion H15; subst; try apply Forall_nil.
        apply Forall_cons; try eapply IHcs; eauto.
        intros.
        apply contains_only_local_cfuns_if_tc with (qn := qn) in H3; auto.
      - inversion H_most; subst.
        inversion H4.
        + inversion H; subst; left; auto.
        + inversion H; subst; left + right; solve [auto].
      - inversion H_t_head as [qnt [argst [tt [H_lookup H_tt]]]].
        assert (E: (qnt, argst, tt) = a);
          [> | subst; simpl in *; auto].
        clear - E_sigs H_lookup E_head.
        pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as H_unique.
        unfold cfun_sigs_names_unique in H_unique.
        destruct a as [[a_qn a_args] a_t]; simpl in *; subst.
        assert (lookup_cfun_sig_l (program_skeleton p) a_qn = Some (a_qn, a_args, a_t)).
        { rewrite <- In_cfun_sig_lookup_cfun_sig_l.
          rewrite <- E_sigs; clear E_sigs. induction cfun_sigs_remaining; simpl; auto; try right; auto.
        }
        rewrite H in H_lookup. inversion H_lookup; auto.
    }
    intros.
    + match type of H with
      | ?x -> ?y => assert (Hxxx: x); [> | specialize (H Hxxx); clear Hxxx]
      end.
      {
        inversion H_most as [|_x _y H_at_a H_at]; subst.
        inversion H_inline as [|_x _y _z H_inline_tail H_no_inlined H_no_cs]; subst.
        assert (E_sigs' : exists rest, rest ++ cfun_sigs_inlined = skeleton_cfun_sigs_l (program_skeleton p) /\ In a rest);
          [> eexists; split; eauto; apply in_app_iff; auto |].
        clear - H_at H_at_a H_inline_tail H_no_inlined H_no_cs E_tail H_t_tail H_t E_sigs' H_most.
        gen_induction cfun_bods_inlined cfun_sigs_inlined; inversion H_at;
          destruct cfun_bods_inlined as [| bod bods]; inversion E_tail; subst;
            [> apply Forall_nil | simpl in *; apply Forall_cons ].
        - inversion_clear H1.
          + left. inversion H; subst.
            apply Forall_cons; auto.
            * apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
              rewrite <- Forall_map in H6.
              Forall_sublist_tac.
            * rewrite <- Forall_map in H6.
              rewrite <- Forall_map.
              Forall_sublist_tac.
          + inversion H; subst.
            * right.
              apply contains_one_local_cfun_call_list_here;
                [> rewrite <- Forall_map in *; Forall_sublist_tac |].
              apply replace_cfun_call_keeps_different_cfun_calls; auto.
              -- clear - E_sigs'.
                 inversion_clear E_sigs' as [rest [E_sigs H_in]].
                 pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as H_unique.
                 unfold cfun_sigs_names_unique in H_unique.
                 rewrite <- E_sigs in *; clear E_sigs.
                 induction rest; inversion H_in; subst.
                 ++ inversion H_unique; subst.
                    intro E. apply H1.
                    rewrite E. rewrite map_app. simpl.
                    apply in_app_iff; right. auto.
                 ++ inversion H_unique; subst; auto.
              -- intros.
                 pose proof (subterm_typechecks _ _ _ _ _ H_t H0) as H_t_sub.
                 inversion H_t_sub as [ctx' [t' H_t']].
                 inversion H_t'; subst.
                 assert (length argts = length ls);
                   [> clear - H14;
                    gen_induction argts ls; destruct argts; inversion H14; subst; auto;
                    simpl; f_equal; auto |].
                 assert (E: argts = snd (fst a)); [> | rewrite E in *; auto].
                 clear - H11 E_sigs'.
                 inversion_clear E_sigs' as [rest [E_sigs H_in]].
                 pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as H_unique.
                 rewrite <- E_sigs in *.
                 unfold cfun_sigs_names_unique in H_unique.
                 destruct a as [[a_n a_ts] a_t]. simpl in *. clear E_sigs.
                 induction rest; inversion H_in; subst.
                 ++ inversion H11; try solve [inversion H; auto].
                    apply in_map with (f := fun x => fst (fst x)) in H; simpl in H.
                    inversion H_unique; subst. contradiction.
                 ++ simpl in H_unique. inversion H_unique; subst.
                    inversion H11; subst.
                    ** simpl in *.
                       exfalso. apply H2.
                       apply in_map with (f := fun x => fst (fst x)) in H; simpl in H.
                       In_sublist_tac.
                    ** apply IHrest; auto.
              -- rewrite <- Forall_map in H6.
                 Forall_sublist_tac.
            * rewrite map_app in H6.
              apply contains_one_local_list_app in H6.
              inversion H6 as [[H_one_cs H_no_rest] | [H_one_rest H_no_cs']].
              -- inversion H_at_a; inversion H0; subst;
                   try solve [left; apply Forall_cons; auto;
                              rewrite replace_cfun_call_id_if_contains_none;
                              auto].
                 right. apply contains_one_local_cfun_call_list_here; auto.
                 apply replace_creates_from_cases; auto.
              -- right. apply contains_one_local_cfun_call_list_there; auto.
                 apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
                 rewrite Forall_map; auto.
        - rewrite Forall_forall; intros.
          inversion H_most as [| _x _y Hyy [|_xx _yy _ Hxx]]; subst.
          rewrite Forall_forall in Hxx. specialize (Hxx x H).
          rename H into H_in.
          clear - Hyy Hxx E_sigs' H_in H_t.
          assert (H_most: contains_at_most_one_local_cfun_call (fst (fst a))  e); [> | clear Hyy].
          { inversion Hyy.
            - inversion H; subst; left; auto.
            - inversion H; subst; left + right; solve [auto].
          }
          inversion_clear H_most.
          + rewrite replace_cfun_call_id_if_contains_none; auto.
            contains_at_most_sublist_tac.
          +  inversion_clear Hxx.
             * left. apply Forall_cons.
               -- inversion H0; subst.
                  apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
                  rewrite map_app in H4. rewrite Forall_map. Forall_sublist_tac.
               -- inversion_clear H0. rewrite map_app in H2; Forall_sublist_tac.
             * right. inversion H0; subst.
               -- apply contains_one_local_cfun_call_list_here;
                    [> rewrite map_app in H4; inversion H4; Forall_sublist_tac |].
                  apply replace_cfun_call_keeps_different_cfun_calls; auto.
                  ++ inversion E_sigs' as [rest [E H_in']].
                     pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as H_unique.
                     unfold cfun_sigs_names_unique in H_unique.
                     rewrite <- E in *.
                     rewrite map_app in H_unique.
                     apply unique_app_switch with (l1 := []) in H_unique; simpl in H_unique.
                     inversion H_unique; subst.
                     apply uniqueness_app_not_in in H6.
                     rewrite Forall_forall in H6.
                     specialize (H6 _ H_in).
                     intro E'.
                     apply H6. apply in_map with (f := fun x => fst (fst x)) in H_in'.
                     rewrite E' in *; auto.
                  ++ intros.
                     eapply subterm_typechecks in H1; eauto.
                     inversion H1 as [ctx [t H_t']].
                     inversion H_t'; subst.
                     assert (E: length ls = length argts);
                       [> clear - H12;
                        gen_induction argts ls; destruct argts; auto;
                        inversion H12; subst; simpl; f_equal; auto
                       | rewrite E; clear E].
                     assert (E: argts = snd (fst a)); [> | rewrite E; auto].
                     assert (H_inx: In a (skeleton_cfun_sigs_l (program_skeleton p))).
                     { inversion E_sigs' as [rest [Ex H_inx]].
                       rewrite <- Ex in *.
                       In_sublist_tac.
                     }
                     destruct a as [[a_n a_ts] a_t]; simpl in *.
                     rewrite In_cfun_sig_lookup_cfun_sig_l in H_inx.
                     rewrite In_cfun_sig_lookup_cfun_sig_l in H9.
                     rewrite H9 in H_inx. inversion H_inx; auto.
                  ++ rewrite map_app in H4. rewrite Forall_map. Forall_sublist_tac.
               -- rewrite map_app in H4.
                  apply contains_one_local_list_app in H4.
                  inversion H4 as [[H_one_cs H_no_bods] | [H_one_bods H_no_cs]].
                  ++ apply contains_one_local_cfun_call_list_here; auto.
                     apply replace_creates_from_cases; auto.
                  ++ apply contains_one_local_cfun_call_list_there; auto.
                     apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
                     rewrite Forall_map; auto.
      }
      apply inline_partial_keeps_typecheck.
      * intros.
        destruct (eq_QName qn qn0) eqn:E_qn.
        -- name_eq_tac.
           apply replace_local_cfun_calls_creates_no_local_cfun_calls; auto.
           ++ rewrite <- Forall_map.
              rewrite Forall_flatten. auto.
           ++ assert (H_at: contains_at_most_one_local_cfun_call (fst (fst a)) e).
              { inversion H_most; subst; auto.
                inversion H6; inversion H4; subst; left + right; solve [auto].
              }
              inversion H_at.
              ** apply replace_cfun_call_by_match_creates_no_cfun_calls; auto.
              ** apply replace_cfun_call_by_match_removes_all_cfun_calls; auto.
        --
          eapply contains_only_local_cfuns_if_tc with (qn := qn0) in H; eauto.
          ++ simpl in *. intro H_in. apply H0.
             rewrite map_app in H_in; apply in_app_iff in H_in; inversion H_in; auto.
             simpl in H4. inversion H4; try contradiction. subst.
             name_refl_contradiction_tac.
      * apply inline_partial_reflects_typecheck in H; auto.
Qed.

Lemma inline_cfuns_to_skeleton_preserves_typechecking_list: forall (p : program) (ctxt: ctxt) (e : expr) (tn : TypeName),
    ((program_skeleton p) / ctxt |- e : tn) ->
    (* not helpful, since there is no "at most one" condition in prog: *)
    (*term_in_original_prog e p -> *)
    (* Forall (fun qn => contains_at_most_one_local_cfun_call qn e)
           (map (fun x => fst (fst x)) (skeleton_cfun_sigs_l (program_skeleton p))) -> *)
    Forall
      (fun qn : QName =>
         contains_at_most_one_local_cfun_call_list qn (e :: map snd (flat_map snd (program_cfun_bods_l p))))
      (map (fun x : QName * list TypeName * TypeName => fst (fst x)) (skeleton_cfun_sigs_l (program_skeleton p))) ->
    inline_ordered_cfun (program_cfun_bods_l p) ->
    (inline_cfuns_to_skeleton p) / ctxt |- (replace_local_cfun_calls_prog p e) : tn.
Proof.
  intros.

  apply inline_cfuns_to_skeleton_preserves_typechecking_list_helper; auto.
  - pose proof (program_has_all_cfun_bods_l p).
    unfold has_all_cfun_bods in *; auto.
  - apply (program_cfun_bods_typecheck_l p).
Qed.

(*****************************************************************************)
(** Def inline of whole program          *************************************)
(*****************************************************************************)

Definition local_cfuns_only_used_once (p : program) : Prop :=
  Forall (fun qn =>
            contains_at_most_one_local_cfun_call_list
              qn
              (map snd (program_fun_bods p) ++
                   map snd (flat_map snd (program_cfun_bods_g p)) ++
                   map snd (flat_map snd (program_cfun_bods_l p)) ++
                   map snd (flat_map snd (program_gfun_bods_g p)) ++
                   map snd (flat_map snd (program_gfun_bods_l p)))
         ) (map (fun x => fst (fst x)) (skeleton_cfun_sigs_l (program_skeleton p))).


Definition new_skeleton (p : program) : skeleton :=
  inline_cfuns_to_skeleton p.

Definition new_fun_bods (p : program) : fun_bods :=
  map (fun x => (fst x, replace_local_cfun_calls_prog p (snd x))) (program_fun_bods p).

Lemma new_has_all_fun_bods: forall (p : program),
    has_all_fun_bods (skeleton_fun_sigs (program_skeleton p)) (program_fun_bods p) ->
    has_all_fun_bods (skeleton_fun_sigs (new_skeleton p))
                     (new_fun_bods p).
Proof.
  intros p H.
  unfold has_all_fun_bods in *.
  simpl in *.
  unfold new_fun_bods. rewrite map_map. simpl. auto.
Qed.

Lemma new_fun_bods_typecheck: forall (p : program),
    (fun_bods_typecheck (program_skeleton p) (program_fun_bods p)) ->
    local_cfuns_only_used_once p ->
    inline_ordered_cfun (program_cfun_bods_l p) ->
    fun_bods_typecheck (new_skeleton p) (new_fun_bods p).
Proof.
  intros p H H_once H_inline.
  unfold fun_bods_typecheck in *. unfold new_fun_bods.
  rewrite <- Forall_map.
  rewrite Forall_forall; intros; rewrite Forall_forall in H.
  specialize (H _ H0).
  inversion H as [n [args [t [H_lookup H_t]]]].
  map_tac ltac:(fun x=> exists x) (n, args, t).
  simpl in *.
  split.
  - destruct x. simpl in *.
    assert (E: n0 = n);
      [> apply lookup_fun_sig_name_correct in H_lookup; auto | subst ].
    rewrite <- In_fun_sig_lookup_fun_sig.
    rewrite <- In_fun_sig_lookup_fun_sig in H_lookup. simpl. auto.
  - apply inline_cfuns_to_skeleton_preserves_typechecking_list; auto.
    clear - H_once H0.
    unfold local_cfuns_only_used_once in H_once.
    rewrite Forall_forall; intros; rewrite Forall_forall in H_once;
      specialize (H_once _ H).
    contains_at_most_sublist_tac.
    match goal with
    | [  |- sublist (?x :: ?rx) (?ly ++ ?ry) ] =>
      pose proof (sublist_app [x] rx ly ry)
    end.
    simpl in H1. apply H1; try sublist_tac.
    apply sublist_singleton_In; in_map_tac; auto.
Qed.

Definition new_cfun_bods_g (p : program) : cfun_bods :=
  map (fun x => (fst x, map (fun y => (fst y, replace_local_cfun_calls_prog p (snd y))) (snd x))) (program_cfun_bods_g p).

Lemma new_has_all_cfun_bods_g: forall (p : program),
    has_all_cfun_bods (skeleton_cfun_sigs_g (program_skeleton p)) (program_cfun_bods_g p) ->
    has_all_cfun_bods (skeleton_cfun_sigs_g (new_skeleton p)) (new_cfun_bods_g p).
Proof.
  intros p H.
  simpl. unfold new_cfun_bods_g.
  unfold has_all_cfun_bods in *. rewrite map_map; simpl. auto.
Qed.

Lemma new_cfun_bods_typecheck_g: forall (p : program),
    (cfun_bods_g_typecheck (program_skeleton p) (program_cfun_bods_g p)) ->
    local_cfuns_only_used_once p ->
    inline_ordered_cfun (program_cfun_bods_l p) ->
    cfun_bods_g_typecheck (new_skeleton p) (new_cfun_bods_g p).
Proof.
  intros p H H_once H_inline.
  unfold cfun_bods_g_typecheck in *. unfold new_cfun_bods_g.
  rewrite <- Forall_map.
  rewrite Forall_forall; intros; rewrite Forall_forall in H.
  specialize (H _ H0).
  inversion H as [n [args [t [H_lookup H_t]]]].
  map_tac ltac:(fun x=> exists x) (n, args, t).
  simpl in *.
  split.
  - destruct x. simpl in *.
    assert (E: q = n);
      [> apply lookup_cfun_sig_name_correct_g in H_lookup; auto | subst ].
    rewrite <- In_cfun_sig_lookup_cfun_sig_g.
    rewrite <- In_cfun_sig_lookup_cfun_sig_g in H_lookup. simpl. auto.
  - inversion H_t; subst.
    apply T_Match with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types) (ctorlist := ctorlist); auto.
    + inversion H6; subst. apply T_Var; auto.
    + clear - H9 H11.
      generalize H9. generalize args at 1. clear H9.
      gen_induction (bindings_types, 1) bindings_exprs; destruct bindings_types; destruct args0; simpl in H9; inversion H9; inversion H11; try apply ListTypeDeriv_Nil; subst.
      apply ListTypeDeriv_Cons.
      * inversion H7; subst; apply T_Var; auto.
      * eapply IHbindings_exprs; eauto.
    + clear - H13.
      gen_induction ctorlist (snd x); destruct ctorlist; simpl in H13; inversion H13; subst; simpl; try apply Forall_nil.
      apply Forall_cons; auto.
      destruct a; destruct p0; auto.
    + clear - H_once H_inline H14 H0.
      repeat rewrite map_map. simpl.
      rewrite map_length.
      assert (Hx: forall y, In y (snd x) -> In y (flat_map snd (program_cfun_bods_g p)));
        [> intros; apply in_flat_map; eexists; split; eauto |].
      gen_induction ctorlist (snd x); destruct ctorlist; inversion H14; subst; try apply ListTypeDeriv'_Nil.
      simpl; apply ListTypeDeriv'_Cons; auto.
      apply inline_cfuns_to_skeleton_preserves_typechecking_list; auto.
      clear - H_once H0 Hx.
      unfold local_cfuns_only_used_once in H_once.
      rewrite Forall_forall; intros; rewrite Forall_forall in H_once;
        specialize (H_once _ H).
      contains_at_most_sublist_tac.
      match goal with
      | [  |- sublist (?x :: ?rx) (?ly ++ ?my ++ ?ry) ] =>
        pose proof (sublist_app [x] rx (ly ++ my) ry)
      end.
      simpl in H1. rewrite <- app_assoc in H1. apply H1; try sublist_tac.
      specialize (Hx a (or_introl (eq_refl a))).
      apply in_map with (f := snd) in Hx.
      apply sublist_singleton_In in Hx. rewrite <- app_nil_r. rewrite <- app_assoc. apply sublist_app_extend_cov; auto.
Qed.

Definition new_cfun_bods_l (p : program) : cfun_bods := [].

Lemma new_has_all_cfun_bods_l: forall (p : program),
    has_all_cfun_bods (skeleton_cfun_sigs_l (new_skeleton p)) (new_cfun_bods_l p).
Proof.
  intros p.
  simpl. unfold new_cfun_bods_l.
  unfold has_all_cfun_bods in *. auto.
Qed.

Lemma new_cfun_bods_typecheck_l: forall (p : program),
    cfun_bods_l_typecheck (new_skeleton p) (new_cfun_bods_l p).
Proof.
  intros p.
  unfold cfun_bods_l_typecheck. unfold new_cfun_bods_l. auto.
Qed.

Lemma contains_at_most_one_local_cfun_call_list_swap: forall (qn : QName) (l r : list expr),
    contains_at_most_one_local_cfun_call_list qn (l ++ r) ->
    contains_at_most_one_local_cfun_call_list qn (r ++ l).
Proof.
  intros qn l r H.
  inversion H.
  - left. apply Forall_app; Forall_sublist_tac.
  - right.
    apply contains_one_list_app in H0.
    inversion H0 as [[H_one_l H_no_r] | [H_no_l H_one_r]];
      apply contains_one_list_app; auto.
Qed.

Definition new_gfun_bods_g (p : program) : gfun_bods :=
  map (fun x => (fst x, map (fun y => (fst y, replace_local_cfun_calls_prog p (snd y))) (snd x))) (program_gfun_bods_g p).

Lemma new_has_all_gfun_bods_g: forall (p : program),
    has_all_gfun_bods (skeleton_gfun_sigs_g (program_skeleton p)) (program_gfun_bods_g p) ->
    has_all_gfun_bods (skeleton_gfun_sigs_g (new_skeleton p)) (new_gfun_bods_g p).
Proof.
  intros p H.
  simpl. unfold new_gfun_bods_g.
  unfold has_all_gfun_bods in *. rewrite map_map; simpl. auto.
Qed.

Lemma new_gfun_bods_typecheck_g: forall (p : program),
    (gfun_bods_g_typecheck (program_skeleton p) (program_gfun_bods_g p)) ->
    local_cfuns_only_used_once p ->
    inline_ordered_cfun (program_cfun_bods_l p) ->
    gfun_bods_g_typecheck (new_skeleton p) (new_gfun_bods_g p).
Proof.
  intros p H H_once H_inline.
  unfold gfun_bods_g_typecheck in *. unfold new_gfun_bods_g.
  rewrite <- Forall_map.
  rewrite Forall_forall; intros; rewrite Forall_forall in H.
  specialize (H _ H0).
  inversion H as [n [args [H_lookup H_t]]].
  map_tac ltac:(fun x=> exists x) (n, args).
  simpl in *.
  split.
  - destruct x. simpl in *.
    assert (E: q = n);
      [> apply lookup_gfun_sig_name_correct_g in H_lookup; auto | subst ].
    rewrite <- In_gfun_sig_lookup_gfun_sig_g.
    rewrite <- In_gfun_sig_lookup_gfun_sig_g in H_lookup. simpl. auto.
  - inversion H_t; subst.
    apply T_CoMatch with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types) (dtorlist := dtorlist); auto.
    + clear - H4 H5. rename H4 into H9; rename H5 into H11.
      generalize H9. generalize args at 1. clear H9.
      gen_induction (bindings_types, 0) bindings_exprs; destruct bindings_types; destruct args0; simpl in H9; inversion H9; inversion H11; try apply ListTypeDeriv_Nil; subst.
      apply ListTypeDeriv_Cons.
      * inversion H7; subst; apply T_Var; auto.
      * eapply IHbindings_exprs; eauto.
    + clear - H9. rename H9 into H13.
      gen_induction dtorlist (snd x); destruct dtorlist; simpl in H13; inversion H13; subst; simpl; try apply Forall_nil.
      apply Forall_cons; auto.
      destruct a; repeat destruct p0; auto.
    + clear - H_once H_inline H10 H0. rename H10 into H14.
      repeat rewrite map_map. simpl.
      assert (Hx: forall y, In y (snd x) -> In y (flat_map snd (program_gfun_bods_g p)));
        [> intros; apply in_flat_map; eexists; split; eauto |].
      gen_induction dtorlist (snd x); destruct dtorlist; inversion H14; subst; try apply ListTypeDeriv'_Nil.
      simpl; apply ListTypeDeriv'_Cons; auto.
      apply inline_cfuns_to_skeleton_preserves_typechecking_list; auto.
      clear - H_once H0 Hx.
      unfold local_cfuns_only_used_once in H_once.
      rewrite Forall_forall; intros; rewrite Forall_forall in H_once;
        specialize (H_once _ H).
      match goal with
      | [  |- contains_at_most_one_local_cfun_call_list ?qn (?x :: ?xs) ] =>
        pose proof (contains_at_most_one_local_cfun_call_list_swap qn xs [x]) as H_swap
      end.
      simpl in H_swap. apply H_swap.
      contains_at_most_sublist_tac.
      do 2 rewrite app_assoc.
      apply sublist_app; try sublist_tac.
      specialize (Hx a (or_introl (eq_refl a))).
      apply in_map with (f := snd) in Hx.
      apply sublist_singleton_In in Hx. rewrite <- app_nil_l. apply sublist_app_extend_cov; auto.
Qed.

Definition new_gfun_bods_l (p : program) : gfun_bods :=
  map (fun x => (fst x, map (fun y => (fst y, replace_local_cfun_calls_prog p (snd y))) (snd x))) (program_gfun_bods_l p).

Lemma new_has_all_gfun_bods_l: forall (p : program),
    has_all_gfun_bods (skeleton_gfun_sigs_l (program_skeleton p)) (program_gfun_bods_l p) ->
    has_all_gfun_bods (skeleton_gfun_sigs_l (new_skeleton p)) (new_gfun_bods_l p).
Proof.
  intros p H.
  simpl. unfold new_gfun_bods_l.
  unfold has_all_gfun_bods in *. rewrite map_map; simpl. auto.
Qed.

Lemma new_gfun_bods_typecheck_l: forall (p : program),
    (gfun_bods_l_typecheck (program_skeleton p) (program_gfun_bods_l p)) ->
    local_cfuns_only_used_once p ->
    inline_ordered_cfun (program_cfun_bods_l p) ->
    gfun_bods_l_typecheck (new_skeleton p) (new_gfun_bods_l p).
Proof.
  intros p H H_once H_inline.
  unfold gfun_bods_l_typecheck in *. unfold new_gfun_bods_l.
  rewrite <- Forall_map.
  rewrite Forall_forall; intros; rewrite Forall_forall in H.
  specialize (H _ H0).
  inversion H as [n [args [H_lookup H_t]]].
  map_tac ltac:(fun x=> exists x) (n, args).
  simpl in *.
  split.
  - destruct x. simpl in *.
    assert (E: q = n);
      [> apply lookup_gfun_sig_name_correct_l in H_lookup; auto | subst ].
    rewrite <- In_gfun_sig_lookup_gfun_sig_l.
    rewrite <- In_gfun_sig_lookup_gfun_sig_l in H_lookup. simpl. auto.
  - inversion H_t; subst.
    apply T_CoMatch with (bindings_exprs := bindings_exprs) (bindings_types := bindings_types) (dtorlist := dtorlist); auto.
    + clear - H4 H5. rename H4 into H9; rename H5 into H11.
      generalize H9. generalize args at 1. clear H9.
      gen_induction (bindings_types, 0) bindings_exprs; destruct bindings_types; destruct args0; simpl in H9; inversion H9; inversion H11; try apply ListTypeDeriv_Nil; subst.
      apply ListTypeDeriv_Cons.
      * inversion H7; subst; apply T_Var; auto.
      * eapply IHbindings_exprs; eauto.
    + clear - H9. rename H9 into H13.
      gen_induction dtorlist (snd x); destruct dtorlist; simpl in H13; inversion H13; subst; simpl; try apply Forall_nil.
      apply Forall_cons; auto.
      destruct a; repeat destruct p0; auto.
    + clear - H_once H_inline H10 H0. rename H10 into H14.
      repeat rewrite map_map. simpl.
      assert (Hx: forall y, In y (snd x) -> In y (flat_map snd (program_gfun_bods_l p)));
        [> intros; apply in_flat_map; eexists; split; eauto |].
      gen_induction dtorlist (snd x); destruct dtorlist; inversion H14; subst; try apply ListTypeDeriv'_Nil.
      simpl; apply ListTypeDeriv'_Cons; auto.
      apply inline_cfuns_to_skeleton_preserves_typechecking_list; auto.
      clear - H_once H0 Hx.
      unfold local_cfuns_only_used_once in H_once.
      rewrite Forall_forall; intros; rewrite Forall_forall in H_once;
        specialize (H_once _ H).
      match goal with
      | [  |- contains_at_most_one_local_cfun_call_list ?qn (?x :: ?xs) ] =>
        pose proof (contains_at_most_one_local_cfun_call_list_swap qn xs [x]) as H_swap
      end.
      simpl in H_swap. apply H_swap.
      contains_at_most_sublist_tac.
      do 3 rewrite app_assoc.
      apply sublist_app; try sublist_tac.
      specialize (Hx a (or_introl (eq_refl a))).
      apply in_map with (f := snd) in Hx.
      apply sublist_singleton_In in Hx. auto.
Qed.

Lemma match_names_unique_after_inline_match: forall (p : program),
    match_names_unique (program_fun_bods p)
                       (program_cfun_bods_g p ++ program_cfun_bods_l p)
                       (program_gfun_bods_g p ++ program_gfun_bods_l p) ->
    match_names_unique (new_fun_bods p)
                       (new_cfun_bods_g p ++ new_cfun_bods_l p)
                       (new_gfun_bods_g p ++ new_gfun_bods_l p).
Proof.
  intros p H.
  unfold match_names_unique in *.
  repeat rewrite map_app.
  repeat rewrite map_map.
  repeat rewrite concat_app.
  unfold new_fun_bods.
  unfold new_cfun_bods_l; simpl; rewrite app_nil_r.
Admitted. (* check Results.v for details on missing proofs *)

(* this is just a stub to keep naming consistent in this file while providing a more sensible name in the Results.v file *)
Lemma new_match_names_unique: forall (p : program),
    match_names_unique (program_fun_bods p)
                       (program_cfun_bods_g p ++ program_cfun_bods_l p)
                       (program_gfun_bods_g p ++ program_gfun_bods_l p) ->
    match_names_unique (new_fun_bods p)
                       (new_cfun_bods_g p ++ new_cfun_bods_l p)
                       (new_gfun_bods_g p ++ new_gfun_bods_l p).
Proof.
    apply match_names_unique_after_inline_match.
Qed.

Lemma comatch_names_unique_after_inline_match: forall (p : program),
    comatch_names_unique (program_fun_bods p)
                       (program_cfun_bods_g p ++ program_cfun_bods_l p)
                       (program_gfun_bods_g p ++ program_gfun_bods_l p) ->
    comatch_names_unique (new_fun_bods p)
                       (new_cfun_bods_g p ++ new_cfun_bods_l p)
                       (new_gfun_bods_g p ++ new_gfun_bods_l p).
Proof.
  intros p H.
  unfold comatch_names_unique in *.
  repeat rewrite map_app.
  repeat rewrite map_map.
  repeat rewrite concat_app.
  apply uniqueness_app_3way.
  - unfold new_fun_bods. rewrite map_map; simpl.
Admitted. (* check Results.v for details on missing proofs *)

(* this is just a stub to keep naming consistent in this file while providing a more sensible name in the Results.v file *)
Lemma new_comatch_names_unique: forall (p : program),
    comatch_names_unique (program_fun_bods p)
                       (program_cfun_bods_g p ++ program_cfun_bods_l p)
                       (program_gfun_bods_g p ++ program_gfun_bods_l p) ->
    comatch_names_unique (new_fun_bods p)
                       (new_cfun_bods_g p ++ new_cfun_bods_l p)
                       (new_gfun_bods_g p ++ new_gfun_bods_l p).
Proof.
    apply comatch_names_unique_after_inline_match.
Qed.

(* Note this assumes that the input program contains no functions annotated as local. *)
(*    (If there are local consumer functions, this just returns the original program.) *)
(*  *)
Definition inline_cfuns_to_program (p : program)
           (H_once: local_cfuns_only_used_once p)
           (H_inline: inline_ordered_cfun (program_cfun_bods_l p)): program :=
      {|
        (* Skeleton *)
        program_skeleton := new_skeleton p;
        (* Ordinary functions *)
        program_fun_bods := new_fun_bods p;
        program_has_all_fun_bods := new_has_all_fun_bods p (program_has_all_fun_bods p);
        program_fun_bods_typecheck := new_fun_bods_typecheck p (program_fun_bods_typecheck p) H_once H_inline;
        (* Consumer functions *)
        program_cfun_bods_g := new_cfun_bods_g p;
        program_has_all_cfun_bods_g := new_has_all_cfun_bods_g p (program_has_all_cfun_bods_g p);
        program_cfun_bods_typecheck_g := new_cfun_bods_typecheck_g p (program_cfun_bods_typecheck_g p) H_once H_inline;
        program_cfun_bods_l := new_cfun_bods_l p;
        program_has_all_cfun_bods_l := new_has_all_cfun_bods_l p;
        program_cfun_bods_typecheck_l := new_cfun_bods_typecheck_l p;
        (* Generator functions *)
        program_gfun_bods_g := (new_gfun_bods_g p);
        program_has_all_gfun_bods_g := new_has_all_gfun_bods_g p (program_has_all_gfun_bods_g p);
        program_gfun_bods_typecheck_g := new_gfun_bods_typecheck_g p (program_gfun_bods_typecheck_g p)  H_once H_inline;
        program_gfun_bods_l := new_gfun_bods_l p;
        program_has_all_gfun_bods_l := new_has_all_gfun_bods_l p (program_has_all_gfun_bods_l p);
        program_gfun_bods_typecheck_l := new_gfun_bods_typecheck_l p (program_gfun_bods_typecheck_l p) H_once H_inline;
        (* Uniqueness conditions *)
        program_match_names_unique := new_match_names_unique p (program_match_names_unique p);
        program_comatch_names_unique := new_comatch_names_unique p (program_comatch_names_unique p);
      |}
.
