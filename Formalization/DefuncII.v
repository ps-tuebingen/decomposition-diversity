(* Standard library imports *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.
Import ListNotations.
(* Project related imports *)
Require Import GenericLemmas.
Require Import Names.
Require Import AST.
Require Import UtilsProgram.
Require Import UtilsSkeleton.
Require Import Skeleton.
Require Import Typechecker.
Require Import DefuncI.
Require Import LiftComatch.
Require Import Subterm.
(*Require Import FunInd.*)

(**************************************************************************************************)
(** * Defunctionalization Part II:                                                                *)
(**                                                                                               *)
(** In the second part of the algorithm we compute the new function bodies.                       *)
(**************************************************************************************************)

Fixpoint defunctionalize_expr (tn : TypeName) (e : expr) : expr :=
  match e with
  | E_Var n => E_Var n
  | E_Constr sn es => E_Constr sn (map (defunctionalize_expr tn) es)
  | E_DestrCall sn e es =>
      if eq_TypeName tn (fst (unscope sn))
      then E_ConsFunCall sn (defunctionalize_expr tn e) (map (defunctionalize_expr tn) es)
      else E_DestrCall sn (defunctionalize_expr tn e) (map (defunctionalize_expr tn) es)
  | E_FunCall n es => E_FunCall n (map (defunctionalize_expr tn) es)
  | E_GenFunCall sn es =>
      if eq_TypeName tn (fst (unscope sn))
      then E_Constr sn (map (defunctionalize_expr tn) es)
      else E_GenFunCall sn (map (defunctionalize_expr tn) es)
  | E_ConsFunCall sn e es => E_ConsFunCall sn (defunctionalize_expr tn e) (map (defunctionalize_expr tn) es)
  | E_Match qn e bs cases t =>
      E_Match qn (defunctionalize_expr tn e)
              (map (fun x => (defunctionalize_expr tn (fst x), snd x)) bs)
              (map (fun x => (fst x, defunctionalize_expr tn (snd x))) cases) t
  | E_CoMatch qn bs cocases =>
      (* Without lift/inline, we would have a case distinction... *)
      (*
      if eq_TypeName tn (fst qn)
      (* ...but this case may actually never occur (and will not, thanks to comatch lifting) *)
      then E_Constr (local qn) (map (fun x => defunctionalize_expr tn (fst x)) bs)
      else *)
      E_CoMatch qn (map (fun x => (defunctionalize_expr tn (fst x), snd x)) bs)
                   (map (fun x => (fst x, defunctionalize_expr tn (snd x))) cocases)
  | E_Let e1 e2 => E_Let (defunctionalize_expr tn e1) (defunctionalize_expr tn e2)
  end.


Lemma filter_compose : forall {A} (l : list A) f g,
  filter f (filter g l) = filter (fun x => andb (f x) (g x)) l.
Proof with auto.
intros. induction l... simpl. case_eq (g a); intros.
- case_eq (f a); intros.
  + simpl. rewrite H0. f_equal...
  + simpl. rewrite H0...
- case_eq (f a); intros...
Qed.


Lemma defunctionalize_expr_preserves_typing : forall p tn e ctx t,
  (forall e' n bs cocases, subterm e' e -> e' <> E_CoMatch (tn,n) bs cocases) ->
  (program_skeleton p) / ctx |- e : t ->
  (defunctionalize_to_skeleton p tn) / ctx |- (defunctionalize_expr tn e) : t.
Proof with try apply in_eq; try apply in_cons; eauto.
intros. generalize dependent ctx. generalize dependent t. generalize H. clear H.
induction e using expr_strong_ind; intros.
- inversion H0; subst. apply T_Var...
- inversion H1; subst. simpl. apply T_Constr with (cargs:=cargs)...
  + simpl. apply in_or_app. right...
  + clear - H H0 H7.
    assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
    { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_Constr... }
    clear H0. induction H7; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
    * inversion H; subst. apply H4... intros. apply H1 with (x:=e)...
    * apply IHListTypeDeriv; try inversion H... intros. apply H1 with (x:=x0)...
- simpl. case_eq (eq_TypeName tn (fst (unscope n))); intros.
  + inversion H1; subst. destruct n.
    * apply T_LocalConsFunCall with (argts:=dargs).
      -- simpl. unfold new_cfunsigs_l. apply in_or_app. left.
         rewrite in_map_iff. unfold cfunsigs_mapfun. exists (local q, dargs, t).
         split... rewrite filter_In. split...
      -- apply IHe... intros. unfold not in *. intros. eapply H0...
         eapply Sub_Trans... apply Sub_DestrCall_e0...
      -- assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
         { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_DestrCall_es... }
         clear - H H11 H3. induction H11; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
         ++ inversion H; subst. apply H4... intros. apply H3 with (x:=e)...
         ++ apply IHListTypeDeriv; try inversion H... intros. apply H3 with (x:=x0)...
    * apply T_GlobalConsFunCall with (argts:=dargs).
      -- simpl. unfold new_cfunsigs_g. apply in_or_app. left.
         rewrite in_map_iff. unfold cfunsigs_mapfun. exists (global q, dargs, t).
         split... rewrite filter_In. split...
      -- apply IHe... intros. unfold not in *. intros. eapply H0...
         eapply Sub_Trans... apply Sub_DestrCall_e0...
      -- assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
         { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_DestrCall_es... }
         clear - H H11 H3. induction H11; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
         ++ inversion H; subst. apply H4... intros. apply H3 with (x:=e)...
         ++ apply IHListTypeDeriv; try inversion H... intros. apply H3 with (x:=x0)...
  + inversion H1; subst. apply T_DestrCall with (dargs:=dargs).
    * simpl. unfold new_dtors. rewrite filter_In. split... rewrite H2...
    * apply IHe... intros. unfold not in *. intros. eapply H0...
      eapply Sub_Trans... apply Sub_DestrCall_e0...
    * assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
      { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_DestrCall_es... }
      clear - H H11 H3. induction H11; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
      ++ inversion H; subst. apply H4... intros. apply H3 with (x:=e)...
      ++ apply IHListTypeDeriv; try inversion H... intros. apply H3 with (x:=x0)...
- inversion H1; subst. simpl. apply T_FunCall with (argts:=argts)...
  clear - H H0 H8.
  assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
  { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_FunCall... }
  clear H0. induction H8; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
  * inversion H; subst. apply H4... intros. apply H1 with (x:=e)...
  * apply IHListTypeDeriv; try inversion H... intros. apply H1 with (x:=x0)...
- inversion H1; subst.
  + simpl. apply T_GlobalConsFunCall with (argts:=argts).
    * simpl. unfold new_cfunsigs_g. apply in_or_app...
    * apply IHe... intros. unfold not in *. intros. eapply H0...
      eapply Sub_Trans... apply Sub_ConsFunCall_e0...
    * assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
      { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_ConsFunCall_es... }
      clear - H H10 H2. induction H10; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
      -- inversion H; subst. apply H4... intros. apply H2 with (x:=e)...
      -- apply IHListTypeDeriv; try inversion H... intros. apply H2 with (x:=x0)...
  + simpl. apply T_LocalConsFunCall with (argts:=argts).
    * simpl. unfold new_cfunsigs_g. apply in_or_app...
    * apply IHe... intros. unfold not in *. intros. eapply H0...
      eapply Sub_Trans... apply Sub_ConsFunCall_e0...
    * assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
      { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_ConsFunCall_es... }
      clear - H H10 H2. induction H10; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
      -- inversion H; subst. apply H4... intros. apply H2 with (x:=e)...
      -- apply IHListTypeDeriv; try inversion H... intros. apply H2 with (x:=x0)...
- simpl. case_eq (eq_TypeName tn (fst (unscope sn))); intros.
  + inversion H1; subst.
    * apply T_Constr with (cargs:=argts)...
      -- simpl. unfold computeNewDatatype. apply in_or_app. left. apply in_or_app. left.
         rewrite in_map_iff. exists (qn, argts). split... rewrite filter_In. split...
         simpl in *. rewrite eq_TypeName_symm...
      -- assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
         { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_GenFunCall... }
         clear - H H9 H3. induction H9; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
         ++ inversion H; subst. apply H4... intros. apply H3 with (x:=e)...
         ++ apply IHListTypeDeriv; try inversion H... intros. apply H3 with (x:=x0)...
    * apply T_Constr with (cargs:=argts)...
      -- simpl. unfold computeNewDatatype. apply in_or_app. left. apply in_or_app. right.
         rewrite in_map_iff. exists (qn, argts). split... rewrite filter_In. split...
         simpl in *. rewrite eq_TypeName_symm...
      -- assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
         { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_GenFunCall... }
         clear - H H9 H3. induction H9; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
         ++ inversion H; subst. apply H4... intros. apply H3 with (x:=e)...
         ++ apply IHListTypeDeriv; try inversion H... intros. apply H3 with (x:=x0)...
  + inversion H1; subst.
    * apply T_GlobalGenFunCall with (argts:=argts).
      -- simpl. unfold new_gfunsigs_g. rewrite filter_In. split... simpl in *. rewrite H2...
      -- assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
         { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_GenFunCall... }
         clear - H H9 H3. induction H9; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
         ++ inversion H; subst. apply H4... intros. apply H3 with (x:=e)...
         ++ apply IHListTypeDeriv; try inversion H... intros. apply H3 with (x:=x0)...
    * apply T_LocalGenFunCall with (argts:=argts).
      -- simpl. unfold new_gfunsigs_l. rewrite filter_In. split... simpl in *. rewrite H2...
      -- assert (forall x y n bs cocases, In x ls -> subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
         { clear - H0. intros. apply H0. eapply Sub_Trans... apply Sub_GenFunCall... }
         clear - H H9 H3. induction H9; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
         ++ inversion H; subst. apply H4... intros. apply H3 with (x:=e)...
         ++ apply IHListTypeDeriv; try inversion H... intros. apply H3 with (x:=x0)...
- simpl. inversion H2; subst.
  apply T_Match with (bindings_exprs := map (defunctionalize_expr tn) bindings_exprs)
    (bindings_types := bindings_types) (ctorlist := ctorlist).
  + apply IHe... intros. unfold not in *. apply H1. eapply Sub_Trans... apply Sub_Match_e0.
  + rewrite map_fst_f_combine...
  + assert (forall x y n bs cocases,
      In x (map fst (combine bindings_exprs bindings_types)) ->
      subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
    { clear - H1. intros. apply H1. eapply Sub_Trans... apply Sub_Match_bs... }
    clear - H0 H13 H3. induction H13; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
    * inversion H0; subst. apply H4... intros. unfold not in *. eapply H3...
    * apply IHListTypeDeriv; try inversion H0... intros. apply H3 with (x:=x0)...
  + unfold lookup_ctors. unfold lookup_ctors in *.
    remember (filter (eq_TypeName (fst n)) (skeleton_dts (defunctionalize_to_skeleton p tn))) as fl.
    simpl. clear - H14 Heqfl.
    destruct (filter (eq_TypeName (fst n)) (skeleton_dts (program_skeleton p))) eqn:E; try discriminate.
    inversion H14. subst ctorlist. clear H14. pose proof (in_eq t l). rewrite <- E in H.
    rewrite filter_In in H. destruct H.
    assert (exists t l, fl = t :: l) as flEq.
    { case_eq (eq_TypeName (fst n) tn); intros.
      - simpl in Heqfl. rewrite H1 in Heqfl. exists tn. eexists...
      - simpl in Heqfl. rewrite H1 in Heqfl. rewrite E in Heqfl. exists t. exists l...
    }
    destruct flEq as [t' [l' flEq]]. rewrite flEq. clear t' l' flEq.
    unfold computeNewDatatype.
    rewrite filter_app. rewrite filter_app. f_equal. rewrite <- app_nil_l. f_equal.
    case_eq (eq_TypeName t tn); intros.
    * rewrite eq_TypeName_eq in H1. subst.
      pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
      unfold dts_cdts_disjoint in H1.
      pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as H2.
      unfold gfun_sigs_in_cdts in H2.
      pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as H2'.
      unfold gfun_sigs_in_cdts in H2'.
      case_eq ((filter (fun x => eq_TypeName (fst (fst x)) tn)
        (skeleton_gfun_sigs_l (program_skeleton p)))); intros;
      case_eq ((filter (fun x => eq_TypeName (fst (fst x)) tn)
        (skeleton_gfun_sigs_g (program_skeleton p)))); intros; auto; exfalso.
      -- pose proof (in_eq p0 l0). rewrite <- H4 in H5. rewrite filter_In in H5.
         destruct H5. rewrite eq_TypeName_eq in H6. subst.
         rewrite Forall_forall in H2'. pose proof (H2' _ H5). unfold not in H1.
         apply H1 with (t:=fst (fst p0))...
      -- pose proof (in_eq p0 l0). rewrite <- H3 in H5. rewrite filter_In in H5.
         destruct H5. rewrite eq_TypeName_eq in H6. subst.
         rewrite Forall_forall in H2. pose proof (H2 _ H5). unfold not in H1.
         apply H1 with (t:=fst (fst p0))...
      -- pose proof (in_eq p0 l0). rewrite <- H3 in H5. rewrite filter_In in H5.
         destruct H5. rewrite eq_TypeName_eq in H6. subst.
         rewrite Forall_forall in H2. pose proof (H2 _ H5). unfold not in H1.
         apply H1 with (t:=fst (fst p0))...
    * rewrite <- app_nil_l. f_equal;
      match goal with |- ?l = [] => case_eq l; intros; auto;
        exfalso; pose proof (in_eq p0 l0); rewrite <- H2 in H3; rewrite filter_In in H3;
        destruct H3; rewrite in_map_iff in H3; do 2 (destruct H3); rewrite filter_In in H5;
        destruct H5; destruct p0; inversion H3; subst; simpl in *;
        rewrite eq_TypeName_eq in H0; rewrite H0 in H4;
        rewrite eq_TypeName_eq in H6; rewrite eq_TypeName_eq in H4; subst;
        unfold QName in *; rewrite H4 in H1; rewrite eq_TypeName_refl in H1; discriminate
      end.
  + rewrite Forall_forall in *. intros. rewrite <- map_fst_f_combine in H3.
    rewrite in_map_iff in H3. do 2 (destruct H3). pose proof (H15 _ H4).
    destruct x. destruct p0. destruct p1. destruct x0. destruct p0. destruct p1. subst.
    inversion H3...
  + assert (forall x, In x ls -> In x ls)...
    generalize H3. generalize H16.
    generalize (map (fun ctor => snd ctor ++ bindings_types) ctorlist).
    generalize ls at - 4. clear - H H1. induction ls0; intros.
    * inversion H16. subst. apply ListTypeDeriv'_Nil.
    * inversion H16. subst. simpl. apply ListTypeDeriv'_Cons.
      -- rewrite Forall_forall in H. destruct a. simpl. apply H...
         ++ rewrite in_map_iff. exists (s,e0). split... apply H3...
         ++ intros. apply H1. apply Sub_Trans with (e2:=e0)... apply Sub_Match_cases.
            rewrite in_map_iff. exists (s,e0). split... apply H3...
      -- apply IHls0... intros. apply H3...
- simpl. case_eq (eq_TypeName tn (fst n)); intros.
  + exfalso. unfold not in H1. rewrite eq_TypeName_eq in H3. subst. destruct n.
    eapply H1; try eapply Sub_Refl...
  + simpl. inversion H2. subst.
    apply T_CoMatch with (bindings_exprs := map (defunctionalize_expr tn) bindings_exprs)
    (bindings_types := bindings_types) (dtorlist := dtorlist).
    * rewrite map_fst_f_combine...
    * assert (forall x y n bs cocases,
      In x (map fst (combine bindings_exprs bindings_types)) ->
      subterm y x -> y <> E_CoMatch (tn,n) bs cocases).
      { clear - H1. intros. apply H1. eapply Sub_Trans... apply Sub_CoMatch_bs... }
      clear - H0 H8 H4. induction H8; try apply ListTypeDeriv_Nil. simpl. apply ListTypeDeriv_Cons.
      -- inversion H0; subst. apply H3... intros. unfold not in *. eapply H4...
      -- apply IHListTypeDeriv; try inversion H0... intros. apply H4 with (x:=x0)...
    * unfold lookup_dtors. rewrite <- H11. f_equal. simpl. unfold new_cdts.
      unfold lookup_dtors. unfold new_dtors.
      generalize (skeleton_cdts (program_skeleton p)).
      generalize (skeleton_dtors (program_skeleton p)). intros c c0.
      repeat (rewrite filter_compose).
      rewrite filter_ext with (g:=eq_TypeName (fst n)).
      2 : { clear - H3. intros. case_eq (eq_TypeName (fst n) a); intros...
            rewrite eq_TypeName_eq in H. subst. rewrite H3... }
      rewrite filter_ext with
        (g:=(fun x : ScopedName * list TypeName * TypeName =>
          let (y, _) := x in let (n0, _) := y in eq_TypeName (fst (unscope n0)) (fst n)))...
      clear - H3. intros. destruct a. destruct p.
      case_eq (eq_TypeName (fst (unscope s)) (fst n)); intros...
      rewrite eq_TypeName_eq in H. rewrite H. rewrite H3...
    * rewrite Forall_forall in *. intros. rewrite <- map_fst_f_combine in H4.
      rewrite in_map_iff in H4. do 2 (destruct H4). pose proof (H13 _ H5).
      destruct x. destruct p0. destruct p1. destruct x0. destruct p0. destruct p1.
      destruct p2. destruct p0. subst. inversion H4...
    * assert (forall x, In x ls -> In x ls)...
      generalize H4. generalize H14.
      generalize (map (fun dtor => snd (fst dtor) ++ bindings_types) dtorlist).
      generalize (map snd dtorlist).
      generalize ls at - 3. clear - H H1. induction ls0; intros.
      -- inversion H14. subst. apply ListTypeDeriv'_Nil.
      -- inversion H14. subst. simpl. apply ListTypeDeriv'_Cons.
         ++ rewrite Forall_forall in H. destruct a. simpl. apply H...
            ** rewrite in_map_iff. exists (s,e). split... apply H4...
            ** intros. apply H1. apply Sub_Trans with (e2:=e)... apply Sub_CoMatch_cocases.
               rewrite in_map_iff. exists (s,e). split... apply H4...
         ++ apply IHls0... intros. apply H4...
- inversion H0. subst. simpl. apply T_Let with (t1:=t1).
  + apply IHe1... intros. apply H. apply Sub_Trans with (e2:=e1)... apply Sub_Let_e1...
  + apply IHe2... intros. apply H. apply Sub_Trans with (e2:=e2)... apply Sub_Let_e2...
Qed.

