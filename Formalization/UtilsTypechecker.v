(**************************************************************************************************)
(* Total Constructor/Destructorization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: UtilsTypechecker.v                                                                       *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.omega.Omega.

Require Import AST.
Require Import Names.
Require Import GenericLemmas.
Require Import GenericTactics.
Require Import Skeleton.
Require Import ProgramDef.
Require Import Eval.
Require Export Typechecker.



Lemma preservation_in_list : forall (p : program) (e e' : expr) (left right : list expr) (cargs : list TypeName),
    program_skeleton p // [] ||- (left ++ [e] ++ right) :: cargs ->
    Forall
      (fun e1 : expr =>
         forall t : TypeName,
           program_skeleton p / [] |- e1 : t -> forall e2 : expr, [p |- e1 ==> e2] -> program_skeleton p / [] |- e2 : t)
      (left ++ [e] ++ right) ->
    [ p |- e ==> e' ] ->
    program_skeleton p // [] ||- (left ++ [e'] ++ right) :: cargs.
Proof.
  intros p e e' left right cargs Ht Hall Heval.
  generalize dependent cargs.
  induction left.
  -intros. simpl. simpl in Ht.
   inversion Hall as [|_x _l Hhead Htail]; subst. inversion Ht; subst.
   apply ListTypeDeriv_Cons; try assumption.
   apply Hhead; try assumption.
  -intros. inversion Ht; subst.
   apply ListTypeDeriv_Cons; try assumption.
   apply IHleft; try assumption.
   inversion Hall. assumption.
Qed.

Lemma typeDerivList_lenghts_eq : forall (sk : skeleton) (exs : list expr) (ts : list TypeName),
    (sk // [] ||- exs :: ts) ->
    List.length exs = List.length ts.
Proof.
  intros. generalize dependent ts.
  induction exs.
  -intros. inversion H. reflexivity.
  -intros. induction ts; try solve [inversion H].
   simpl. f_equal. inversion H. apply IHexs; try assumption.
Qed.

Lemma weaken_nth_option : forall {X : Type} (xsBase xs : list X) (x : X) (n : nat),
    Some x = nth_option n xsBase ->
    Some x = nth_option n (xsBase ++ xs).
Proof.
  intros X xsBase xs x n H.
  generalize dependent n. induction xsBase; intros.
  -destruct n; try solve [inversion H].
  -destruct n; try solve [inversion H; reflexivity].
   simpl. simpl in H. apply IHxsBase. assumption.
Qed.

Lemma weaken_listDeriv:
  forall (sk : skeleton) (ls : list expr),
    Forall
      (fun e : expr =>
         forall (ctxBase ctx : list TypeName) (t : TypeName),
           sk / ctxBase |- e : t -> sk / (ctxBase ++ ctx) |- e : t) ls ->
    forall ctxBase ctx argts : list TypeName,
      sk // ctxBase ||- ls :: argts -> sk // (ctxBase ++ ctx) ||- ls :: argts.
Proof.
  intros sk ls H ctxBase ctx argts H7.
  generalize dependent argts; induction ls; intros;
    try solve [destruct argts; try solve [inversion H7]; apply ListTypeDeriv_Nil].
  destruct argts; try solve [inversion H7].
  inversion H. inversion H7. apply ListTypeDeriv_Cons.
  * apply H2. assumption.
  * apply IHls; try assumption.
Qed.

Lemma weaken_bindings:
  forall (sk : skeleton) (bindings_exprs : list expr) (bindings_types : list TypeName),
    Forall
      (fun e : expr =>
         forall (ctxBase ctx : list TypeName) (t : TypeName),
           sk / ctxBase |- e : t -> sk / (ctxBase ++ ctx) |- e : t)
      (map (fun et : expr * TypeName => let (e, _) := et in e) (combine bindings_exprs bindings_types)) ->
    forall ctxBase ctx : list TypeName,
      sk // ctxBase ||- bindings_exprs :: bindings_types ->
      sk // (ctxBase ++ ctx) ||- bindings_exprs :: bindings_types.
Proof.
  intros sk bindings_exprs bindings_types H_ind ctxBase ctx H.
  generalize dependent bindings_exprs; induction bindings_types; intros;
    destruct bindings_exprs; try solve [inversion H].
  - apply ListTypeDeriv_Nil.
  - inversion H. inversion H_ind. apply ListTypeDeriv_Cons.
    + apply H10; assumption.
    + apply IHbindings_types with (bindings_exprs := bindings_exprs); try assumption.
Qed.

Lemma weaken_typederiv : forall (sk : skeleton) (t : TypeName) (ctx ctxBase : list TypeName) (e : expr),
    (sk / ctxBase |- e : t) ->
    sk / (ctxBase ++ ctx) |- e : t.
Proof.
  intros sk t ctx ctxBase e H.
  generalize dependent t. generalize dependent ctx. generalize dependent ctxBase.
  induction e using expr_strong_ind; intros.
  (* E_Var *)
  - apply T_Var. inversion H. apply weaken_nth_option. assumption.
  (* E_Constr *)
  - inversion H0. subst.
    simpl. apply T_Constr with (cargs := cargs); try assumption; try reflexivity.
    clear H0 H3.
    generalize dependent cargs. induction ls; intros.
    + destruct cargs; try solve [inversion H6]. apply ListTypeDeriv_Nil.
    + destruct cargs; try solve [inversion H6]. apply ListTypeDeriv_Cons.
      * inversion H. apply H2 with (ctxBase := ctxBase) (ctx := ctx) (t := t).
        inversion H6. assumption.
      * inversion H. apply IHls; try assumption. inversion H6. assumption.
  (* E_DestrCall *)
  - inversion H0; subst.
    apply T_DestrCall with (dargs := dargs); try assumption.
    + apply IHe. assumption.
    + clear H0 H6.
      generalize dependent dargs. induction ls; intros.
      * destruct dargs; try solve [inversion H9]. apply ListTypeDeriv_Nil.
      * destruct dargs; try solve [inversion H9]. apply ListTypeDeriv_Cons.
        -- inversion H. apply H2 with (ctxBase := ctxBase). inversion H9. assumption.
        -- inversion H. apply IHls; try assumption. inversion H9. assumption.
  (* E_FunCall *)
  - inversion H0; subst.
    apply T_FunCall with (argts := argts); try assumption.
    apply weaken_listDeriv; assumption.
  (* E_MatchFunCall *)
  - let solve_tac :=
        (apply T_GlobalConsFunCall with (argts := argts) || apply T_LocalConsFunCall with (argts := argts)) ; try assumption;
          [> apply IHe; try assumption
          | apply weaken_listDeriv; assumption]
    in
    inversion H0; subst;
      [> solve_tac | solve_tac].
  (* E_MatchFunCall *)
  - inversion H0; subst;
      (apply T_GlobalGenFunCall with (argts := argts) || apply T_LocalGenFunCall with (argts := argts));
      try assumption;
    apply weaken_listDeriv; try assumption.
  (* E_Match *)
  - inversion H1; subst.
    apply T_Match with
        (bindings_exprs := bindings_exprs)
        (bindings_types := bindings_types)
        (ctorlist := ctorlist);
      try assumption; try reflexivity.
    + apply IHe; assumption.
    + apply weaken_bindings; assumption.
  (* E_CoMatch *)
  - inversion H1; subst.
    apply T_CoMatch with
        (bindings_exprs := bindings_exprs)
        (bindings_types := bindings_types)
        (dtorlist := dtorlist);
      try assumption; try reflexivity.
    apply weaken_bindings; assumption.
  (* E_Let *)
  - inversion H; subst.
    apply T_Let with (t1 := t1).
    + apply IHe1; assumption.
    + apply IHe2 with (ctxBase := t1 :: ctxBase); assumption.
Qed.

Lemma nth_option_eq : forall {X : Type} (xs xs': list X) (x : X),
    nth_option (List.length xs) (xs ++ [x] ++ xs') = Some x.
Proof.
  intros X xs x.
  induction xs; try reflexivity.
  simpl. apply IHxs.
Qed.

Lemma nth_option_lt : forall {X : Type} (xs xs' : list X) (x : X) (n : nat),
    List.length xs <? n = true ->
    nth_option n (xs ++ [x] ++ xs') = nth_option (n - 1) (xs ++ xs').
Proof.
  intros X xs xs' x n H.
  generalize dependent n; induction xs; intros; try reflexivity.
  -simpl. destruct n; try solve [inversion H].
   simpl. rewrite <- minus_n_O. reflexivity.
  -destruct n; try solve [inversion H]. simpl.
   assert (Hsimpl : nth_option (n - 0) (a :: xs ++ xs') = nth_option (n - 1) (xs ++ xs')).
   destruct n; try solve [inversion H]. simpl. rewrite <- minus_n_O. reflexivity.
   rewrite Hsimpl. apply IHxs. simpl in H. unfold Nat.ltb in H. simpl in H.
   destruct n; try discriminate H. apply Nat.ltb_lt. apply Nat.leb_le in H. unfold lt. inversion H.
   +apply le_n.
   +subst. apply le_n_S. assumption.
Qed.

Lemma nth_option_gt : forall {X : Type} (xs xs' : list X) (x : X) (n : nat),
    List.length xs <? n = false ->
    List.length xs =? n = false ->
    nth_option n (xs ++ [x] ++ xs') = nth_option n (xs ++ xs').
Proof.
  intros X xs xs' x n Hlt Heq.
  generalize dependent n; induction xs; intros.
  -destruct n; try solve [inversion Heq]; try solve [inversion Hlt].
  -simpl. destruct n.
   +reflexivity.
   +simpl. apply IHxs.
    *simpl in Hlt. assumption.
    *assumption.
Qed.

Ltac listTypeDeriv_tac argts ls := generalize dependent argts; induction ls; intros; destruct argts; try solve [inversion Ht_args]; try apply ListTypeDeriv_Nil.

Lemma subst_typing_cong : forall (sk : skeleton) (t t' : TypeName) (ctx_left ctx_right : list TypeName) (e e' : expr),
    (sk / [] |- e' : t') ->
    (sk / ctx_left ++ [t'] ++ ctx_right |- e : t) ->
    sk / ctx_left ++ ctx_right |- (substitute' (List.length ctx_left) e' e) : t.
Proof.
  intros sk t t' ctx_left ctx_right e e' He' He.
  generalize dependent t. generalize dependent ctx_left. generalize dependent ctx_right.
  induction e using expr_strong_ind; intros;
    let rec genfun_tac :=  subst; simpl;
                             match goal with
                             | [ _: _ // _ ||- _ :: ?argts  |- _ ] =>
                               (apply T_GlobalGenFunCall with (argts := argts) ||
                                                              apply T_LocalGenFunCall with (argts := argts))
                                 end;
                             try assumption;
                             clear Hin He;
                             listTypeDeriv_tac argts ls;
                             apply ListTypeDeriv_Cons;
                             [> inversion H; apply H2; inversion Ht_args; assumption
                             | inversion H; inversion Ht_args; subst; apply IHls; try assumption
                             ]
    in
    let rec consfun_tac := subst; simpl;
                             match goal with
                             | [ _: _ // _ ||- _ :: ?argts  |- _ ] =>
                               (apply T_GlobalConsFunCall with (argts := argts) ||
                                                               apply T_LocalConsFunCall with (argts := argts))
                             end;
                             try assumption;
                             [> apply IHe; assumption
                             | clear Hin He;
                               listTypeDeriv_tac argts ls;
                               apply ListTypeDeriv_Cons;
                               [> inversion H; apply H2; inversion Ht_args; assumption
                               | inversion H; inversion Ht_args; subst; apply IHls; try assumption
                               ]
                             ]
    in
  inversion He as [ sk' ctx' v' t''
                          | sk' ctx' args sn' cargs tn' HIn Ht_args tn_eq
                          | sk' ctx' args ex sn' dargs rtype Hin Ht_ex Ht_args
                          | sk' ctx' args n' argts rtype Hin Ht_args
                          | sk' ctx' args ex qn argts rtype Hin Ht_ex Ht_args (* E_ConsFunCallG *)
                          | sk' ctx' args ex qn argts rtype Hin Ht_ex Ht_args (* E_ConsFunCallL *)
                          | sk' ctx' args qn argts Hin Ht_args (* E_GenFunCallG *)
                          | sk' ctx' args qn argts Hin Ht_args (* E_GenFunCallL *)
                          | sk' ctx' qn ex  b_exs b_ts bs cs tn' ctorlist Ht_ex bs_comb Ht_bs HlookupConstr Hexhaustive Ht_cs
                          | sk' ctx' qn dtors b_exs b_ts bs cs bs_comb Ht_bs HlookupDestr Hexhaustive Ht_cs
                          | sk' ctx' e1' e2' t1 t2
                  ]; unfold substitute; [> | | | | consfun_tac | consfun_tac |  try genfun_tac | try genfun_tac | | | ].
  (* E_Var *)
  -subst. simpl. destruct (List.length ctx_left =? v) eqn:Elen.
   +apply beq_nat_true in Elen. rewrite <- Elen in H. rewrite nth_option_eq in H.
    inversion H. apply weaken_typederiv with (ctxBase := []). assumption.
   +destruct (List.length ctx_left <? v) eqn:Elenle.
    *destruct v. simpl.
     --induction ctx_left; try solve [inversion Elen].
       simpl. inversion Elenle.
     --rewrite  nth_option_lt in H; try assumption.
       apply T_Var; try assumption.
    *rewrite nth_option_gt in H; try assumption.
     apply T_Var; try assumption.
  (* E_Constr *)
  -simpl. apply T_Constr with (cargs := cargs); try assumption.
   subst. clear HIn He.
   listTypeDeriv_tac cargs ls.
   apply ListTypeDeriv_Cons.
   +inversion H. apply H2. inversion Ht_args. assumption.
   +inversion H. inversion Ht_args. subst. apply IHls; try assumption.
  (* E_DestrCall *)
  -subst. simpl. apply T_DestrCall with (dargs := dargs); try assumption.
   +apply IHe. assumption.
   +clear Hin He IHe.
   listTypeDeriv_tac dargs ls.
   apply ListTypeDeriv_Cons.
    *inversion H. apply H2. inversion Ht_args. assumption.
    *inversion H. inversion Ht_args. subst. apply IHls; try assumption.
  (* E_FunCall *)
  -subst. simpl. apply T_FunCall with (argts := argts); try assumption.
   clear Hin He.
   listTypeDeriv_tac argts ls.
   apply ListTypeDeriv_Cons.
   +inversion H. apply H2. inversion Ht_args. assumption.
   +inversion H. inversion Ht_args; subst. apply IHls; try assumption.
  (* E_Match *)
  -subst. simpl. rewrite map_combine_in_fst.
   apply T_Match with (bindings_exprs := map (substitute' (List.length ctx_left) e') b_exs)
                      (bindings_types := b_ts)
                      (ctorlist := ctorlist); try assumption; try reflexivity.
   +apply IHe. assumption.
   +clear - H0 Ht_bs. generalize dependent b_ts; induction b_exs; intros; destruct b_ts; try solve [inversion Ht_bs].
    *simpl. apply ListTypeDeriv_Nil.
    *inversion H0. apply ListTypeDeriv_Cons.
     --apply H2. inversion Ht_bs. assumption.
     --apply IHb_exs; try assumption. inversion Ht_bs. assumption.
  (* E_CoMatch *)
  -subst. simpl. rewrite map_combine_in_fst.
   apply T_CoMatch with (bindings_exprs := map (substitute' (List.length ctx_left) e') b_exs)
                        (bindings_types := b_ts)
                        (dtorlist := dtors); try assumption; try reflexivity.
   clear - H0 Ht_bs. generalize dependent b_ts; induction b_exs; intros; destruct b_ts; try solve [inversion Ht_bs].
   +apply ListTypeDeriv_Nil.
   +inversion H0. apply ListTypeDeriv_Cons; try assumption.
    *apply H2. inversion Ht_bs. assumption.
    *apply IHb_exs; try assumption.
     inversion Ht_bs. assumption.
  (* E_Let *)
  -subst; simpl. apply T_Let with (t1 := t1).
   +apply IHe1; try assumption.
   +assert (E : List.length ctx_left + 1 = List.length (t1 :: ctx_left)).
    simpl. rewrite <- plus_n_Sm. rewrite <- plus_n_O. reflexivity.
    rewrite E. apply IHe2 with (ctx_left := t1 :: ctx_left). assumption.
Qed.

Lemma subst_typing : forall (sk : skeleton) (t t' : TypeName) (ctx : list TypeName) (e e' : expr),
    (sk / [] |- e' : t') ->
    (sk / t' :: ctx |- e : t) ->
    sk / ctx |- (substitute e' e) : t.
Proof.
  intros. apply subst_typing_cong with (ctx_left := []) (t' := t'); try assumption.
Qed.

Lemma multisubst_typing : forall (sk : skeleton) (argts : list TypeName) (args : list expr) (e : expr) (t : TypeName),
    sk // [] ||- args :: argts ->
    (sk / argts |- e : t) ->
    sk / [] |- (multi_subst args e) : t.
Proof.
  intros sk argts args e t Hargs He.
  generalize dependent e.
  generalize dependent argts. induction args; intros; destruct argts; try solve [inversion Hargs]; try assumption.
  simpl. apply IHargs with (argts := argts).
  -inversion Hargs. assumption.
  -apply subst_typing with (t' := t0); try assumption.
   inversion Hargs. assumption.
Qed.

Lemma listTypeDeriv'_lemma : forall (prog : skeleton)(args : list expr)(argts : list TypeName)(ctxs: list ctxt),
    prog /// ctxs |||- args ::: argts ->
    length argts =? length args  = true.
Proof.
   intros prog args. induction args; intro argts; induction argts; intros ctxs H; try reflexivity; try inversion H; subst.
  simpl. eapply IHargs. eassumption.
Qed.

Lemma listTypeDeriv'_lemma_ctx: forall (prog : skeleton)(args : list expr)(argts : list TypeName)(ctxs: list ctxt),
    prog /// ctxs |||- args ::: argts ->
    length ctxs =? length args  = true.
Proof.
  intros prog args argts ctxs H.
  gen_induction (argts, ctxs) args; destruct ctxs; try solve [inversion H]; auto.
  simpl. inversion_clear H. IH_auto_tac.
Qed.

Fact index_list_typechecks : forall (s : skeleton) (l r : list TypeName) (n : nat),
    length r = n ->
    s // r ++ l ||- map fst (index_list n l) :: l.
Proof.
  intros s l r n H.
  gen_induction (r, n) l.
  - simpl. apply ListTypeDeriv_Nil.
  - simpl. apply ListTypeDeriv_Cons.
    + apply T_Var.
      gen_induction n r; destruct n; try solve [inversion H]; try reflexivity.
      simpl. apply IHr. inversion H; reflexivity.
    + specialize (IHl (S n) (r ++ [a])).
      simpl in IHl.
      assert ((r ++ [a]) ++ l = r ++ a :: l);
        [> clear; induction r; auto; simpl; f_equal; auto |].
      rewrite <- H0. IH_tac. rewrite app_length. simpl.
      rewrite Nat.add_1_r. f_equal. assumption.
Qed.

