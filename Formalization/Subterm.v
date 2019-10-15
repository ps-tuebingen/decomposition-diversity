(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: Subterm.v                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import AST.
Require Import Names.
Require Import GenericLemmas.
Require Import GenericTactics.
Require Import Skeleton.
Require Import ProgramDef.
Require Import Typechecker.

(* e is a subterm of e' *)
Inductive direct_subterm : expr -> expr -> Prop :=
  | Sub_Constr : forall e n es, In e es -> direct_subterm e (E_Constr n es)
  | Sub_DestrCall_e0 : forall e n es, direct_subterm e (E_DestrCall n e es)
  | Sub_DestrCall_es : forall e n e0 es, In e es -> direct_subterm e (E_DestrCall n e0 es)
  | Sub_FunCall : forall e n es, In e es -> direct_subterm e (E_FunCall n es)
  | Sub_GenFunCall : forall e n es, In e es -> direct_subterm e (E_GenFunCall n es)
  | Sub_ConsFunCall_e0 : forall e n es, direct_subterm e (E_ConsFunCall n e es)
  | Sub_ConsFunCall_es : forall e n e0 es, In e es -> direct_subterm e (E_ConsFunCall n e0 es)
  | Sub_Match_e0 : forall e q bs cases t, direct_subterm e (E_Match q e bs cases t)
  | Sub_Match_bs : forall e q e0 bs cases t, In e (map fst bs) -> direct_subterm e (E_Match q e0 bs cases t)
  | Sub_Match_cases : forall e q e0 bs cases t, In e (map snd cases) -> direct_subterm e (E_Match q e0 bs cases t)
  | Sub_CoMatch_bs : forall e q bs cocases, In e (map fst bs) -> direct_subterm e (E_CoMatch q bs cocases)
  | Sub_CoMatch_cocases : forall e q bs cocases, In e (map snd cocases) -> direct_subterm e (E_CoMatch q bs cocases)
  | Sub_Let_e1 : forall e e2, direct_subterm e (E_Let e e2)
  | Sub_Let_e2 : forall e e1, direct_subterm e (E_Let e1 e).

Inductive subterm : expr -> expr -> Prop :=
  | Sub_Refl : forall e, subterm e e
  | Sub_Trans : forall e1 e2 e3, subterm e1 e2 -> direct_subterm e2 e3 -> subterm e1 e3.

Remark subterm_switch_Trans : forall e1 e2 e3,
  direct_subterm e1 e2 -> subterm e2 e3 -> subterm e1 e3.
Proof.
intros. induction H0.
- apply Sub_Trans with (e2:=e1); try apply Sub_Refl. assumption.
- apply Sub_Trans with (e2:=e2); auto.
Qed.

Definition term_in_prog (e : expr) (p : program) :=
  Exists (fun x => subterm e (snd x)) (program_fun_bods p) \/
  Exists (fun x => Exists (fun y => subterm e (snd y)) (snd x)) (program_cfun_bods_g p) \/
  Exists (fun x => Exists (fun y => subterm e (snd y)) (snd x)) (program_cfun_bods_l p) \/
  Exists (fun x => Exists (fun y => subterm e (snd y)) (snd x)) (program_gfun_bods_g p) \/
  Exists (fun x => Exists (fun y => subterm e (snd y)) (snd x)) (program_gfun_bods_l p).

(* Original program means here: before the lift transformation, thus there are no local funs. *)
Definition term_in_original_prog (e : expr) (p : program) :=
  Exists (fun x => subterm e (snd x)) (program_fun_bods p) \/
  Exists (fun x => Exists (fun y => subterm e (snd y)) (snd x)) (program_cfun_bods_g p) \/
  Exists (fun x => Exists (fun y => subterm e (snd y)) (snd x)) (program_gfun_bods_g p).

Lemma subterm_typechecks : forall e e' p ctx t,
  p / ctx |- e : t ->
  subterm e' e ->
  exists ctx' t', p / ctx' |- e' : t'.
Proof.
intros. generalize dependent t. generalize dependent ctx. induction H0; intros.
- exists ctx. exists t. auto.
- inversion H; subst.
  + inversion H1; subst. clear - IHsubterm H2 H8. generalize dependent cargs. induction es; [inversion H2|]; intros.
    unfold In in H2. destruct H2; subst.
    * destruct cargs; inversion H8; subst. eapply IHsubterm with (t:=t). eauto.
    * inversion H8; subst. eapply IHes; eauto.
  + inversion H1; subst. eapply IHsubterm. eauto.
  + inversion H1; subst. clear - IHsubterm H2 H11. generalize dependent dargs. induction es; [inversion H2|]; intros.
    unfold In in H2. destruct H2; subst.
    * destruct dargs; inversion H11; subst. eapply IHsubterm with (t:=t). eauto.
    * inversion H11; subst. eapply IHes; eauto.
  + inversion H1; subst. clear - IHsubterm H2 H9. generalize dependent argts. induction es; [inversion H2|]; intros.
    unfold In in H2. destruct H2; subst.
    * destruct argts; inversion H9; subst. eapply IHsubterm with (t:=t). eauto.
    * inversion H9; subst. eapply IHes; eauto.
  + inversion H1; subst.
    * clear - IHsubterm H2 H9. generalize dependent argts. induction es; [inversion H2|]; intros.
      unfold In in H2. destruct H2; subst.
      -- destruct argts; inversion H9; subst. eapply IHsubterm with (t:=t). eauto.
      -- inversion H9; subst. eapply IHes; eauto.
    * clear - IHsubterm H2 H9. generalize dependent argts. induction es; [inversion H2|]; intros.
      unfold In in H2. destruct H2; subst.
      -- destruct argts; inversion H9; subst. eapply IHsubterm with (t:=t). eauto.
      -- inversion H9; subst. eapply IHes; eauto.
  + inversion H1; subst; eapply IHsubterm; eauto.
  + inversion H1; subst.
    * clear - IHsubterm H2 H11. generalize dependent argts. induction es; [inversion H2|]; intros.
      unfold In in H2. destruct H2; subst.
      -- destruct argts; inversion H11; subst. eapply IHsubterm with (t:=t). eauto.
      -- inversion H11; subst. eapply IHes; eauto.
    * clear - IHsubterm H2 H11. generalize dependent argts. induction es; [inversion H2|]; intros.
      unfold In in H2. destruct H2; subst.
      -- destruct argts; inversion H11; subst. eapply IHsubterm with (t:=t). eauto.
      -- inversion H11; subst. eapply IHes; eauto.
  + inversion H1; subst; eapply IHsubterm; eauto.
  + inversion H1; subst. clear - IHsubterm H2 H13. generalize dependent bindings_types. induction bindings_exprs; intros; [inversion H2|].
    rewrite in_map_iff in H2. destruct H2. destruct H. inversion H13; subst. simpl in H0. destruct H0; subst.
    * eapply IHsubterm with (t0:=t). eauto.
    * eapply IHbindings_exprs; eauto. apply in_map. auto.
  + inversion H1; subst. clear - IHsubterm H2 H16.
    generalize dependent (map (fun ctor : ScopedName * list TypeName => snd ctor ++ bindings_types) ctorlist).
    generalize dependent (repeat t (length cases)). induction cases; intros; [inversion H2|].
    rewrite in_map_iff in H2. destruct H2. destruct H. simpl in H0. destruct H0; subst.
    * inversion H16; subst. eapply IHsubterm. eauto.
    * inversion H16; subst. eapply IHcases; eauto. apply in_map. auto.
  + inversion H1; subst. clear - IHsubterm H2 H7. generalize dependent bindings_types. induction bindings_exprs; intros; [inversion H2|].
    rewrite in_map_iff in H2. destruct H2. destruct H. inversion H7; subst. simpl in H0. destruct H0; subst.
    * eapply IHsubterm with (t0:=t). eauto.
    * eapply IHbindings_exprs; eauto. apply in_map. auto.
  + inversion H1; subst. clear - IHsubterm H2 H13.
    generalize dependent (map (fun dtor => snd (fst dtor) ++ bindings_types) dtorlist).
    generalize dependent (map snd dtorlist). induction cocases; intros; [inversion H2|].
    rewrite in_map_iff in H2. destruct H2. destruct H. simpl in H0. destruct H0; subst.
    * inversion H13; subst. eapply IHsubterm. eauto.
    * inversion H13; subst. eapply IHcocases; eauto. apply in_map. auto.
  + inversion H1; subst. eapply IHsubterm; eauto.
  + inversion H1; subst. eapply IHsubterm; eauto.
Qed.

Lemma term_in_original_prog_typechecks : forall p e,
  term_in_original_prog e p ->
  exists ctx t, (program_skeleton p) / ctx |- e : t.
Proof.
intros. unfold term_in_original_prog in H. destruct H; [| destruct H].
- rewrite Exists_exists in H. do 2 (destruct H).
  pose proof (program_fun_bods_typecheck p). unfold fun_bods_typecheck in H1.
  rewrite Forall_forall in H1. pose proof (H1 _ H).
  do 4 (destruct H2). eapply subterm_typechecks; eauto.
- rewrite Exists_exists in H. do 2 (destruct H).
  pose proof (program_cfun_bods_typecheck_g p). unfold cfun_bods_g_typecheck in H1.
  rewrite Forall_forall in H1. pose proof (H1 _ H).
  do 4 (destruct H2). rewrite Exists_exists in H0. do 2 (destruct H0).
  eapply subterm_typechecks; eauto.
  apply Sub_Trans with (e2:=snd x3); auto.
  apply Sub_Match_cases. apply in_map. auto.
- rewrite Exists_exists in H. do 2 (destruct H).
  pose proof (program_gfun_bods_typecheck_g p). unfold gfun_bods_g_typecheck in H1.
  rewrite Forall_forall in H1. pose proof (H1 _ H).
  do 4 (destruct H2). rewrite Exists_exists in H0. do 2 (destruct H0).
  eapply subterm_typechecks; eauto.
  apply Sub_Trans with (e2:=snd x2); auto.
  apply Sub_CoMatch_cocases. apply in_map. auto.
Qed.

(* Subterm - term in original prog compatibility facts *)

Ltac subterm_term_in_original_prog_tac S :=
  intros;
  match goal with [ H : term_in_original_prog _ _ |- _ ] =>
  destruct H; [|destruct H];
  [rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
   rewrite Forall_forall; intros; unfold term_in_original_prog; left;
   rewrite Exists_exists; exists x; split; auto;
   eapply subterm_switch_Trans; eauto;
   apply S; auto | | ];
  rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
  rewrite Exists_exists in xSub; destruct xSub as [y [yIn ySub]];
  rewrite Forall_forall; intros; unfold term_in_original_prog; right;
  [left | right];
  rewrite Exists_exists; exists x; split; auto;
  rewrite Exists_exists; exists y; split; auto;
  eapply subterm_switch_Trans; eauto;
  apply S; auto
  end.

Ltac subterm_term_in_original_prog_tac_e0 S :=
  intros;
  match goal with [ H : term_in_original_prog _ _ |- _ ] =>
  destruct H; [|destruct H];
  [rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
   unfold term_in_original_prog; left;
   rewrite Exists_exists; exists x; split; auto;
   eapply subterm_switch_Trans; eauto;
   apply S; auto | | ];
  rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
  rewrite Exists_exists in xSub; destruct xSub as [y [yIn ySub]];
  unfold term_in_original_prog; right;
  [left | right];
  rewrite Exists_exists; exists x; split; auto;
  rewrite Exists_exists; exists y; split; auto;
  eapply subterm_switch_Trans; eauto;
  apply S; auto
  end.

Ltac subterm_term_in_original_prog_tac_bs E S flag :=
  intros p n;
  (match flag with true => intros e0 | _ => idtac end);
  intros bs ts ls;
  (match flag with true => intros t | _ => idtac end);
  intros Len H;
  destruct H; [|destruct H];
  [rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
   rewrite Forall_forall; intros; unfold term_in_original_prog; left;
   rewrite Exists_exists; exists x; split; auto;
   (match flag with
    | true => eapply subterm_switch_Trans with (e2:=E n _ (combine bs ts) ls _)
    | _ => apply subterm_switch_Trans with (e2:=E n (combine bs ts) ls)
    end); eauto;
   apply S; rewrite map_fst_combine; auto | | ];
  rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
  rewrite Exists_exists in xSub; destruct xSub as [y [yIn ySub]];
  rewrite Forall_forall; intros; unfold term_in_original_prog; right;
  [left | right];
  rewrite Exists_exists; exists x; split; auto;
  rewrite Exists_exists; exists y; split; auto;
  (match flag with
   | true => eapply subterm_switch_Trans with (e2:=E n _ (combine bs ts) ls _)
   | _ => apply subterm_switch_Trans with (e2:=E n (combine bs ts) ls)
   end); eauto;
  apply S; rewrite map_fst_combine; auto.

Fact subterm_term_in_original_prog_Constr : forall p n ls,
  term_in_original_prog (E_Constr n ls) p ->
  Forall (fun a : expr => term_in_original_prog a p) ls.
Proof. subterm_term_in_original_prog_tac Sub_Constr. Qed.

Fact subterm_term_in_original_prog_FunCall : forall p n ls,
  term_in_original_prog (E_FunCall n ls) p ->
  Forall (fun a : expr => term_in_original_prog a p) ls.
Proof. subterm_term_in_original_prog_tac Sub_FunCall. Qed.

Fact subterm_term_in_original_prog_GenFunCall : forall p n ls,
  term_in_original_prog (E_GenFunCall n ls) p ->
  Forall (fun a : expr => term_in_original_prog a p) ls.
Proof. subterm_term_in_original_prog_tac Sub_GenFunCall. Qed.

Fact subterm_term_in_original_prog_DestrCall_es : forall p n ls e0,
  term_in_original_prog (E_DestrCall n e0 ls) p ->
  Forall (fun a : expr => term_in_original_prog a p) ls.
Proof. subterm_term_in_original_prog_tac Sub_DestrCall_es. Qed.

Fact subterm_term_in_original_prog_ConsFunCall_es : forall p n ls e0,
  term_in_original_prog (E_ConsFunCall n e0 ls) p ->
  Forall (fun a : expr => term_in_original_prog a p) ls.
Proof. subterm_term_in_original_prog_tac Sub_ConsFunCall_es. Qed.

Fact subterm_term_in_original_prog_DestrCall_e0 : forall p n ls e0,
  term_in_original_prog (E_DestrCall n e0 ls) p -> term_in_original_prog e0 p.
Proof. subterm_term_in_original_prog_tac_e0 Sub_DestrCall_e0. Qed.

Fact subterm_term_in_original_prog_ConsFunCall_e0 : forall p n ls e0,
  term_in_original_prog (E_ConsFunCall n e0 ls) p -> term_in_original_prog e0 p.
Proof. subterm_term_in_original_prog_tac_e0 Sub_ConsFunCall_e0. Qed.

Fact subterm_term_in_original_prog_Match_e0 : forall p n e bs ts ls t,
  term_in_original_prog (E_Match n e (combine bs ts) ls t) p -> term_in_original_prog e p.
Proof. subterm_term_in_original_prog_tac_e0 Sub_Match_e0. Qed.

Fact subterm_term_in_original_prog_Match_bs : forall p n e bs ts ls t,
  length bs = length ts ->
  term_in_original_prog (E_Match n e (combine bs ts) ls t) p ->
  Forall (fun a : expr => term_in_original_prog a p) bs.
Proof. subterm_term_in_original_prog_tac_bs E_Match Sub_Match_bs true. Qed.

Fact subterm_term_in_original_prog_CoMatch_bs : forall p n bs ts ls,
  length bs = length ts ->
  term_in_original_prog (E_CoMatch n (combine bs ts) ls) p ->
  Forall (fun a : expr => term_in_original_prog a p) bs.
Proof. subterm_term_in_original_prog_tac_bs E_CoMatch Sub_CoMatch_bs false. Qed.

Fact subterm_term_in_original_prog_Match_cases : forall p n e bs ts ls t,
  term_in_original_prog (E_Match n e (combine bs ts) ls t) p ->
  Forall (fun a : expr => term_in_original_prog a p) (map snd ls).
Proof. subterm_term_in_original_prog_tac Sub_Match_cases. Qed.

Fact subterm_term_in_original_prog_CoMatch_cocases : forall p n bs ts ls,
  term_in_original_prog (E_CoMatch n (combine bs ts) ls) p ->
  Forall (fun a : expr => term_in_original_prog a p) (map snd ls).
Proof. subterm_term_in_original_prog_tac Sub_CoMatch_cocases. Qed.

Fact subterm_term_in_original_prog_Let_e1 : forall p e1 e2,
  term_in_original_prog (E_Let e1 e2) p -> term_in_original_prog e1 p.
Proof.
intros. destruct H; [|destruct H];
[rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
 unfold term_in_original_prog; left; rewrite Exists_exists; exists x; split; auto;
 eapply subterm_switch_Trans; eauto; apply Sub_Let_e1 | | ];
 rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
 rewrite Exists_exists in xSub; destruct xSub as [y [yIn ySub]];
 unfold term_in_original_prog; right; [left | right]; rewrite Exists_exists; exists x; split; auto;
 rewrite Exists_exists; exists y; split; auto;
 eapply subterm_switch_Trans; eauto; apply Sub_Let_e1.
Qed.

Fact subterm_term_in_original_prog_Let_e2 : forall p e1 e2,
  term_in_original_prog (E_Let e1 e2) p -> term_in_original_prog e2 p.
Proof.
intros. destruct H; [|destruct H];
[rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
 unfold term_in_original_prog; left; rewrite Exists_exists; exists x; split; auto;
 eapply subterm_switch_Trans; eauto; apply Sub_Let_e2 | | ];
 rewrite Exists_exists in H; destruct H as [x [xIn xSub]];
 rewrite Exists_exists in xSub; destruct xSub as [y [yIn ySub]];
 unfold term_in_original_prog; right; [left | right]; rewrite Exists_exists; exists x; split; auto;
 rewrite Exists_exists; exists y; split; auto;
 eapply subterm_switch_Trans; eauto; apply Sub_Let_e2.
Qed.

Ltac list_type_deriv_induction_tac :=
  match goal with
  | [ Sub : (forall _, _ -> term_in_original_prog _ _), IH : (Forall _ ?es)  , H : (?sk1 // ?ctxt ||- ?es :: ?ts) |- (?sk2 // ?ctxt ||- (map _ ?es) :: ?ts) ] =>
    clear - IH H Sub;
    let H_length := fresh "H_length"
    in pose proof (listTypeDeriv_lemma sk1 ctxt es ts H) as H_length;
       rewrite PeanoNat.Nat.eqb_eq in H_length; generalize dependent ts;
       induction es;intros;  destruct ts; try (solve [inversion H_length]);
       try apply ListTypeDeriv_Nil;
       inversion IH; subst; clear IH;
       inversion H; subst; clear H;
       apply ListTypeDeriv_Cons; try auto using in_eq, in_cons
  end.

Ltac list_type_deriv_induction_2_tac :=
  match goal with
  | [ Sub : (forall _, _ -> term_in_original_prog _ _), IH : (Forall _ (map _ (combine ?es ?ts)))  , H : (?sk1 // ?ctxt ||- ?es :: ?ts) |- (?sk2 // ?ctxt ||- (map _ ?es) :: ?ts) ] =>
    clear - IH H Sub;
    let H_length := fresh "H_length"
    in pose proof (listTypeDeriv_lemma sk1 ctxt es ts H) as H_length;
       rewrite PeanoNat.Nat.eqb_eq in H_length; generalize dependent ts;
       induction es;intros;  destruct ts; try (solve [inversion H_length]);
       try apply ListTypeDeriv_Nil;
       inversion IH; subst; clear IH;
       inversion H; subst; clear H;
       apply ListTypeDeriv_Cons; try auto using in_eq, in_cons
  end.

Lemma subterm_trans: forall (e1 e2 e3 : expr),
    subterm e1 e2 ->
    subterm e2 e3 ->
    subterm e1 e3.
Proof.
  intros e1 e2 e3 H H0.
  induction H; subst; try assumption.
  IH_tac. apply subterm_switch_Trans with (e2 := e0); auto.
Qed.

Ltac subterm_tac :=
  match goal with
  | [ Hl: subterm ?el ?em, Hr: subterm ?em ?er |- subterm ?el ?er ] =>
    apply subterm_trans with (e2 := em); assumption
  | [  |- subterm ?sub ?top ] =>
    apply Sub_Refl ||
          (apply Sub_Trans with (e2 := sub);
    [> apply Sub_Refl | ])
  end.

Ltac direct_subterm_tac :=
  match goal with
  | [  |- direct_subterm ?sub ?top ] =>
    multimatch top with
    | E_Constr _ ?ls =>
      apply Sub_Constr
    | E_DestrCall _ ?e ?ls =>
      apply Sub_DestrCall_e0 || apply Sub_DestrCall_es
    | E_FunCall _ ?ls =>
      apply Sub_FunCall
    | E_ConsFunCall _ ?e ?ls =>
      apply Sub_ConsFunCall_e0 || apply Sub_ConsFunCall_es
    | E_GenFunCall _ ?ls =>
      apply Sub_GenFunCall
    | E_Match _ ?e ?bs ?cs ?rt =>
      match sub with
      | e => apply Sub_Match_e0
      | _ => match goal with
            | [ Hin: In ?sub' ?ls |- _ ] =>
              match sub' with
              | (_, _) => idtac
              | _ => destruct sub'
              end;
              match ls with
              | context [?xs] =>
                match bs with
                | context [xs] =>  apply Sub_Match_bs;
                                  simpl; try apply In_fst in Hin
                end
                || match cs with
                  | context [xs] => apply Sub_Match_cases;
                                   simpl; try apply In_snd in Hin
                  end
              end
            end
      end
      + (apply Sub_Match_bs + apply Sub_Match_cases); simpl
    | E_CoMatch _ ?bs ?ccs =>
      match goal with
      | [ Hin: In ?sub' ?ls |- _ ] =>
        match sub' with
        | (_, _) => idtac
        | _ => destruct sub'
        end;
        match ls with
          context [?xs] =>
          match bs with
          | context [xs] =>  apply Sub_CoMatch_bs;
                            simpl; try apply In_fst in Hin
          end
          || match ccs with
            | context [xs] => apply Sub_CoMatch_cocases;
                             simpl; try apply In_snd in Hin
            end
        end
      end
      + (apply Sub_CoMatch_bs + apply Sub_CoMatch_cocases); simpl
    | E_Let ?e1 ?e2 =>
      apply Sub_Let_e1 || apply Sub_Let_e2
    end; solve [auto]
  end.

Lemma subterm_reduce_Constr: forall (sn : ScopedName) (ls : list expr) (e_sub : expr),
    (exists x, In x ls /\ subterm e_sub x) ->
    subterm e_sub (E_Constr sn ls).
Proof.
  intros sn ls e_sub H.
  inversion H as [x [H_in H_sub]].
  assert (subterm x (E_Constr sn ls)); subterm_tac; direct_subterm_tac.
Qed.


Lemma subterm_reduce_DestrCall: forall (sn : ScopedName) (e_sub e : expr) (ls : list expr),
    subterm e_sub e \/ (exists x, In x ls /\ subterm e_sub x) ->
    subterm e_sub (E_DestrCall sn e ls).
Proof.
  intros sn e_sub e ls H.
  inversion H.
  - assert (subterm e (E_DestrCall sn e ls)); subterm_tac; direct_subterm_tac.
  - inversion H0 as [x [Hin Hsub]].
    assert (subterm x (E_DestrCall sn e ls)); subterm_tac; direct_subterm_tac.
Qed.

Lemma subterm_reduce_ConsFunCall: forall (sn : ScopedName) (e_sub e : expr) (ls : list expr),
    subterm e_sub e \/ (exists x, In x ls /\ subterm e_sub x) ->
    subterm e_sub (E_ConsFunCall sn e ls).
Proof.
  intros sn e_sub e ls H.
  inversion H.
  - assert (subterm e (E_ConsFunCall sn e ls)); subterm_tac; direct_subterm_tac.
  - inversion H0 as [x [Hin Hsub]].
    assert (subterm x (E_ConsFunCall sn e ls)); subterm_tac; direct_subterm_tac.
Qed.

Lemma subterm_reduce_GenFunCall: forall (sn : ScopedName) (ls : list expr) (e_sub : expr),
    (exists x, In x ls /\ subterm e_sub x) ->
    subterm e_sub (E_GenFunCall sn ls).
Proof.
  intros sn ls e_sub H.
  inversion H as [x [H_in H_sub]].
  assert (subterm x (E_GenFunCall sn ls)); subterm_tac; direct_subterm_tac.
Qed.

Lemma subterm_reduce_FunCall: forall (n : Name) (ls : list expr) (e_sub : expr),
    (exists x, In x ls /\ subterm e_sub x) ->
    subterm e_sub (E_FunCall n ls).
Proof.
  intros n ls e_sub H.
  inversion H as [x [H_in H_sub]].
  assert (subterm x (E_FunCall n ls)); subterm_tac; direct_subterm_tac.
Qed.

Lemma subterm_reduce_Match: forall (qn : QName) (e_sub e : expr) (bs : list (expr * TypeName)) (cs : list (ScopedName * expr)) (rt : TypeName),
    subterm e_sub e
    \/ (exists x, In x (map fst bs) /\ subterm e_sub x)
    \/ (exists x, In x (map snd cs) /\ subterm e_sub x)
    ->
    subterm e_sub (E_Match qn e bs cs rt).
Proof.
  intros qn e_sub e bs cs rt H.
  inversion H as [H0 | [H0 | H0]];
  [> assert (subterm e (E_Match qn e bs cs rt)); subterm_tac; direct_subterm_tac
  | inversion H0 as [x [Hin Hsub]];
      assert (subterm x (E_Match qn e bs cs rt)); subterm_tac; direct_subterm_tac
  .. ].
Qed.

Lemma subterm_reduce_CoMatch: forall (qn : QName) (bs : list (expr * TypeName)) (ccs : list (ScopedName * expr)) (e_sub : expr),
    (exists x, In x (map fst bs) /\ subterm e_sub x) \/
    (exists x, In x (map snd ccs) /\ subterm e_sub x)
    ->
    subterm e_sub (E_CoMatch qn bs ccs).
Proof.
  intros qn bs ccs e_sub H.
  inversion H as [H0 | H0]; inversion H0 as [x [Hin Hsub]];
   assert (subterm x (E_CoMatch qn bs ccs)); subterm_tac; direct_subterm_tac.
Qed.

Lemma subterm_reduce_Let: forall (e_sub e1 e2 : expr),
    subterm e_sub e1 \/ subterm e_sub e2 ->
    subterm e_sub (E_Let e1 e2).
Proof.
  intros e_sub e1 e2 H.
  inversion H.
  - assert (subterm e1 (E_Let e1 e2)); subterm_tac; direct_subterm_tac.
  - assert (subterm e2 (E_Let e1 e2)); subterm_tac; direct_subterm_tac.
Qed.

Ltac subterm_reduce_tac :=
  match goal with
  | [  |- subterm _ (E_Constr _ _) ] =>
    apply subterm_reduce_Constr; eauto
  | [  |- subterm _ (E_DestrCall _ _ _) ] =>
    apply subterm_reduce_DestrCall; eauto
  | [  |- subterm _ (E_ConsFunCall _ _ _) ] =>
    apply subterm_reduce_ConsFunCall; eauto
  | [  |- subterm _ (E_GenFunCall _ _) ] =>
    apply subterm_reduce_GenFunCall; eauto
  | [  |- subterm _ (E_FunCall _ _) ] =>
    apply subterm_reduce_FunCall; eauto
  | [  |- subterm _ (E_Match _ _ _ _ _) ] =>
    apply subterm_reduce_Match; eauto
  | [  |- subterm _ (E_CoMatch _ _ _) ] =>
    apply subterm_reduce_CoMatch; eauto
  | [  |- subterm _ (E_Let _ _) ] =>
    apply subterm_reduce_Let; eauto
  end.

Ltac subterm_trans_tac :=
  match goal with
  | [ H: subterm ?l ?m |- subterm ?l ?r ] =>
    apply subterm_trans with (e2 := m); [> apply H |]
  | [ H: subterm ?m ?r |- subterm ?l ?r ] =>
    apply subterm_trans with (e2 := m); [> | apply H]
  end.
