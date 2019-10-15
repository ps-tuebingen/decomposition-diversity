(* Standard library imports *)
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Import ListNotations.
(* Project related imports *)
Require Import LiftComatch.
Require Import DefuncI.
Require Import DefuncII.
Require Import BodyTypeDefs.
Require Import ProgramDef.
Require Import Typechecker.
Require Import UtilsTypechecker.
Require Import AST.
Require Import Names.
Require Import GenericLemmas.
Require Import OptionMonad.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import Subterm.

(**************************************************************************************************)
(** Switching indices (necessary to preserve typechecking as currently defined)                   *)
(**************************************************************************************************)

Fact skipn_all_app : forall {A} (l l': list A), skipn (length l) (l++l') = l'.
Proof with auto. induction l... Qed.

Definition switch_indices_ctx (ctx : ctxt) (n : nat) : ctxt :=
  (skipn (length ctx - n) ctx) ++ (firstn (length ctx - n) ctx).

Fixpoint switch_indices_helper (e : expr) (p : skeleton) (m : nat) (n : nat) (b : nat) {struct e} : expr.
destruct e.
- destruct (v <? b); intros.
  + exact (E_Var v).
  + destruct (v <? b + n); intros.
    * exact (E_Var (v + m)).
    * exact (E_Var (v - n)).
- exact (E_Constr s (map (fun e => switch_indices_helper e p m n b) l)).
- exact (E_DestrCall s (switch_indices_helper e p m n b)
           (map (fun e => switch_indices_helper e p m n b) l)).
- exact (E_FunCall n0 (map (fun e => switch_indices_helper e p m n b) l)).
- exact (E_GenFunCall s (map (fun e => switch_indices_helper e p m n b) l)).
- exact (E_ConsFunCall s (switch_indices_helper e p m n b)
           (map (fun e => switch_indices_helper e p m n b) l)).
- exact (E_Match q (switch_indices_helper e p m n b)
           (map (fun x => (switch_indices_helper (fst x) p m n b, snd x)) l)
           l0 t).
- exact (E_CoMatch q
           (map (fun x => (switch_indices_helper (fst x) p m n b, snd x)) l)
           l0).
- exact (E_Let (switch_indices_helper e1 p m n b)
           (switch_indices_helper e2 p m n (b + 1))).
Defined.

Lemma app_nth_option1 : forall {A} (l l' : list A) n,
  n < length l -> nth_option n (l++l') = nth_option n l.
Proof with auto.
intros. generalize dependent l'. generalize dependent n.
induction l; intros; [inversion H |]. destruct n... simpl in *. apply IHl. omega.
Qed.

Lemma app_nth_option2 : forall {A} (l l' : list A) n,
  n >= length l -> nth_option n (l++l') = nth_option (n-length l) l'.
Proof with auto.
intros. generalize dependent l'. generalize dependent n.
induction l; intros; [rewrite Nat.sub_0_r |]...
simpl in *. destruct n; try omega. simpl. apply IHl. omega.
Qed.

Lemma skipn_length : forall {A} (l : list A) n,
  n < length l ->
  length (skipn (length l - n) l) = n.
Proof with auto.
intros. generalize dependent l. induction n; intros.
- clear. rewrite Nat.sub_0_r. induction l...
- induction l; intros; [inversion H|].
  simpl. case_eq (length l - n); intros.
  + simpl in H. omega.
  + simpl. case_eq (S n <? length l); intros.
    * rewrite Nat.ltb_lt in H1. apply IHl in H1.
      replace n0 with (length l - S n)... omega.
    * rewrite Nat.ltb_ge in H1. simpl in H.
      assert (S n = length l); try omega.
      specialize IHn with (l:=l).
      rewrite <- H2 in IHn. assert (n < S n); try omega.
      apply IHn in H3. replace (S n - n) with 1 in H3; try omega.
      destruct l; try discriminate. simpl in H3. rewrite <- H3 in H0.
      assert (n0 = 0); try omega. rewrite H4...
Qed.

Lemma nth_option_firstn : forall {A} n m (l : list A),
  m < n ->
  nth_option m (firstn n l) = nth_option m l.
Proof with auto.
intros. generalize dependent m. generalize l.
induction n; intros; [inversion H |].
destruct l0... simpl. destruct m...
simpl. apply IHn. omega.
Qed.


Lemma switch_indices_correct_aux : forall p t ctx bctx e m n b,
  n + m = length ctx ->
  b = length bctx ->
  p / bctx ++ (switch_indices_ctx ctx n) |- e : t ->
  p / bctx ++ ctx |- (switch_indices_helper e p m n b) : t.
Proof with auto.
intros. generalize dependent t. generalize dependent bctx. generalize dependent b.
induction e using expr_strong_ind; intros.
- simpl. case_eq (v <? b); intros.
  + inversion H1; subst. apply T_Var. rewrite Nat.ltb_lt in H2.
    rewrite app_nth_option1 in *...
  + case_eq (v <? b + n); intros.
    * inversion H1; subst. apply T_Var.
      rewrite Nat.ltb_ge in H2. rewrite Nat.ltb_lt in H3.
      unfold switch_indices_ctx in H7.
      rewrite app_nth_option2 in *; try omega.
      rewrite <- (firstn_skipn (length ctx - n) ctx).
      replace (v + m - length bctx) with ((v - length bctx) + m); try omega.
      case_eq (length ctx); intros.
      -- rewrite H0 in *. simpl in *. replace m with 0; omega.
      -- rewrite app_nth_option2.
         2: { rewrite firstn_length. rewrite H0. rewrite Nat.min_l; try omega. }
         destruct m.
         ++ rewrite Nat.add_0_r in *. rewrite H7. rewrite H. rewrite H0.
            rewrite Nat.sub_diag. rewrite firstn_O. rewrite app_nil_r.
            simpl. rewrite Nat.sub_0_r...
         ++ rewrite app_nth_option1 in H7.
            2: { rewrite skipn_length; omega. }
            rewrite firstn_length. rewrite H0. rewrite Nat.min_l; try omega.
            rewrite H7. rewrite <- H. replace (n + S m - n) with (S m); try omega.
            rewrite <- H0. rewrite <- H. replace (n + S m - n) with (S m); try omega.
            replace (v - length bctx + S m - S m) with (v - length bctx); try omega...
    * inversion H1; subst. rewrite Nat.ltb_ge in H3. rewrite Nat.ltb_ge in H2.
      apply T_Var. rewrite H7. rewrite app_nth_option2...
      unfold switch_indices_ctx. rewrite <- H. replace (n + m - n) with m; try omega.
      rewrite (app_nth_option2 bctx); try omega.
      replace (v - n - length bctx) with (v - length bctx - n); try omega.
      assert (n <= v - length bctx); try omega. rewrite app_nth_option2.
      2: {
       destruct m; [simpl; omega |].
       replace (S m) with (length ctx - n); try omega.
       rewrite skipn_length; try omega...
      }
      replace m with (length ctx - n); try omega.
      assert (length (switch_indices_ctx ctx n) = length ctx) as Aux.
      { clear. unfold switch_indices_ctx. rewrite app_length.
        case_eq (n <? length ctx); intros.
        - rewrite Nat.ltb_lt in H. rewrite skipn_length...
          rewrite firstn_length. rewrite Nat.min_l; omega.
        - rewrite Nat.ltb_ge in H. replace (length ctx - n) with 0; try omega.
          simpl. rewrite Nat.add_0_r...
      }
      destruct m.
      -- rewrite app_nth_option2 in H7...
         rewrite <- (app_nil_r (switch_indices_ctx _ _)) in H7.
         rewrite app_nth_option2 in H7.
         2: { rewrite Aux... rewrite <- H. rewrite Nat.add_0_r... }
         destruct (v - length bctx - length (switch_indices_ctx ctx n)); discriminate.
      -- rewrite skipn_length; try omega. apply nth_option_firstn.
         assert (n = length ctx - S m); try omega. subst.
         rewrite app_nth_option2 in H7...
         case_eq (v - length bctx <? length ctx); intros.
         ++ rewrite Nat.ltb_lt in H4. omega.
         ++ rewrite Nat.ltb_ge in H4.
            rewrite <- (app_nil_r (switch_indices_ctx _ _)) in H7.
            rewrite app_nth_option2 in H7; try omega.
            destruct (v - length bctx -
                length (switch_indices_ctx ctx (length ctx - S m)));
              discriminate.
- inversion H2; subst. apply T_Constr with (cargs:=cargs)...
  clear - H0 H8. generalize dependent cargs.
  induction ls; intros; inversion H8; subst; try apply ListTypeDeriv_Nil.
  inversion H0; subst. apply ListTypeDeriv_Cons...
- inversion H2; subst. apply T_DestrCall with (dargs:=dargs)...
  clear - H0 H11. generalize dependent dargs.
  induction ls; intros; inversion H11; subst; try apply ListTypeDeriv_Nil.
  inversion H0; subst. apply ListTypeDeriv_Cons...
- inversion H2; subst. apply T_FunCall with (argts:=argts)...
  clear - H0 H9. generalize dependent argts.
  induction ls; intros; inversion H9; subst; try apply ListTypeDeriv_Nil.
  inversion H0; subst. apply ListTypeDeriv_Cons...
- inversion H2; subst.
  + apply T_GlobalConsFunCall with (argts:=argts)...
    clear - H0 H11. generalize dependent argts.
    induction ls; intros; inversion H11; subst; try apply ListTypeDeriv_Nil.
    inversion H0; subst. apply ListTypeDeriv_Cons...
  + apply T_LocalConsFunCall with (argts:=argts)...
    clear - H0 H11. generalize dependent argts.
    induction ls; intros; inversion H11; subst; try apply ListTypeDeriv_Nil.
    inversion H0; subst. apply ListTypeDeriv_Cons...
- inversion H2; subst.
  + apply T_GlobalGenFunCall with (argts:=argts)...
    clear - H0 H9. generalize dependent argts.
    induction ls; intros; inversion H9; subst; try apply ListTypeDeriv_Nil.
    inversion H0; subst. apply ListTypeDeriv_Cons...
  + apply T_LocalGenFunCall with (argts:=argts)...
    clear - H0 H9. generalize dependent argts.
    induction ls; intros; inversion H9; subst; try apply ListTypeDeriv_Nil.
    inversion H0; subst. apply ListTypeDeriv_Cons...
- inversion H3; subst. apply T_Match with
    (bindings_types:=bindings_types)
    (bindings_exprs:=map (fun e => switch_indices_helper e p m n (length bctx))
                         bindings_exprs)
    (ctorlist:=ctorlist)...
  + rewrite <- map_fst_f_combine...
  + pose proof H14 as H14'.
    apply listTypeDeriv_lemma in H14'. rewrite Nat.eqb_eq in H14'.
    clear - H1 H14' H14. generalize dependent bindings_types.
    induction bindings_exprs; intros; destruct bindings_types; try discriminate.
    * apply ListTypeDeriv_Nil.
    * inversion H14; subst. simpl. apply ListTypeDeriv_Cons.
      -- simpl in H1. inversion H1; subst. apply H2...
      -- apply IHbindings_exprs... rewrite Forall_forall. intros.
         rewrite Forall_forall in H1. apply H1... simpl. right...
- inversion H3; subst. apply T_CoMatch with
    (bindings_types:=bindings_types)
    (bindings_exprs:=map (fun e => switch_indices_helper e p m n (length bctx))
                         bindings_exprs)
    (dtorlist:=dtorlist)...
  + rewrite <- map_fst_f_combine...
  + pose proof H8 as H8'.
    apply listTypeDeriv_lemma in H8'. rewrite Nat.eqb_eq in H8'.
    clear - H1 H8' H8. generalize dependent bindings_types.
    induction bindings_exprs; intros; destruct bindings_types; try discriminate.
    * apply ListTypeDeriv_Nil.
    * inversion H8; subst. simpl. apply ListTypeDeriv_Cons.
      -- simpl in H1. inversion H1; subst. apply H2...
      -- apply IHbindings_exprs... rewrite Forall_forall. intros.
         rewrite Forall_forall in H1. apply H1... simpl. right...
- inversion H1; subst. apply T_Let with (t1:=t1)...
  rewrite app_comm_cons. apply IHe2... simpl. omega.
Qed.

Lemma switch_indices_correct : forall p t ctx e m n,
  n + m = length ctx ->
  p / (switch_indices_ctx ctx n) |- e : t ->
  p / ctx |- (switch_indices_helper e p m n 0) : t.
Proof with auto.
intros. rewrite <- (app_nil_l ctx). apply switch_indices_correct_aux...
Qed.

Definition switch_indices (e : expr) (p : skeleton) (sn : ScopedName) (n : nat) :
  { e' : expr
  | forall t sig ctx,
      lookup_gfun_sig_scoped p sn = Some sig ->
      n + length (snd sig) = length ctx ->
      p / (switch_indices_ctx ctx n) |- e : t -> p / ctx |- e' : t }.
case_eq (lookup_gfun_sig_scoped p sn); intros.
- set (x := switch_indices_helper e p (length (snd g)) n 0).
  apply exist with (x:=x). intros. apply switch_indices_correct; auto.
  inversion H0; subst. auto.
- eapply exist. intros. discriminate.
Unshelve. eauto.
Defined.

Definition switch_indices_b (e : expr) (p : skeleton) (sn : ScopedName) (n : nat) (b : nat) :
  { e' : expr
  | forall t sig ctx bctx,
      lookup_gfun_sig_scoped p sn = Some sig ->
      n + length (snd sig) = length ctx ->
      b = length bctx ->
      p / bctx ++ (switch_indices_ctx ctx n) |- e : t -> p / bctx ++ ctx |- e' : t }.
case_eq (lookup_gfun_sig_scoped p sn); intros.
- set (x := switch_indices_helper e p (length (snd g)) n b).
  apply exist with (x:=x). intros. apply switch_indices_correct_aux; auto.
  inversion H0; subst. auto.
- eapply exist. intros. discriminate.
Unshelve. eauto.
Defined.

Lemma switch_indices_switch_indices_b : forall e p sn n,
  proj1_sig (switch_indices e p sn n) = proj1_sig (switch_indices_b e p sn n 0).
Proof with auto.
intros. unfold switch_indices. unfold switch_indices_b.
destruct (lookup_gfun_sig_scoped p sn)...
Qed.

Definition switch_indices_cfun (e : expr) (p : skeleton) (sn : ScopedName) (n : nat) :
  { e' : expr
  | forall t sig ctx,
      lookup_cfun_sig_scoped p sn = Some sig ->
      n + length (snd (fst sig)) = length ctx ->
      p / (switch_indices_ctx ctx n) |- e : t -> p / ctx |- e' : t }.
case_eq (lookup_cfun_sig_scoped p sn); intros.
- set (x := switch_indices_helper e p (length (snd (fst c))) n 0).
  apply exist with (x:=x). intros. apply switch_indices_correct; auto.
  inversion H0; subst. auto.
- eapply exist. intros. discriminate.
Unshelve. eauto.
Defined.

Definition switch_indices_b_cfun (e : expr) (p : skeleton) (sn : ScopedName) (n : nat) (b : nat) :
  { e' : expr
  | forall t sig ctx bctx,
      lookup_cfun_sig_scoped p sn = Some sig ->
      n + length (snd (fst sig)) = length ctx ->
      b = length bctx ->
      p / bctx ++ (switch_indices_ctx ctx n) |- e : t -> p / bctx ++ ctx |- e' : t }.
case_eq (lookup_cfun_sig_scoped p sn); intros.
- set (x := switch_indices_helper e p (length (snd (fst c))) n b).
  apply exist with (x:=x). intros. apply switch_indices_correct_aux; auto.
  inversion H0; subst. auto.
- eapply exist. intros. discriminate.
Unshelve. eauto.
Defined.

Lemma switch_indices_switch_indices_b_cfun : forall e p sn n,
  proj1_sig (switch_indices_cfun e p sn n) = proj1_sig (switch_indices_b_cfun e p sn n 0).
Proof with auto.
intros. unfold switch_indices_cfun. unfold switch_indices_b_cfun.
destruct (lookup_cfun_sig_scoped p sn)...
Qed.

