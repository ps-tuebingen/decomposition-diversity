(* Standard library imports *)
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Import ListNotations.
(* Project related imports *)
Require Import LiftComatch.
Require Import RefuncI.
Require Import RefuncII.
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
Require Import SwitchIndices.
Require Import UtilsNamesUnique.

(**************************************************************************************************)
(** * Refunctionalization Part III:                                                               *)
(**                                                                                               *)
(** Puts together the new program skeleton and the new function bodies.                           *)
(**************************************************************************************************)

Definition no_matches (tn : TypeName) (e  : expr) : Prop :=
  forall e' n e0 bs cases t, subterm e' e -> e' <> E_Match (tn,n) e0 bs cases t.

Lemma switch_indices_no_match : forall tn e p sn n,
  no_matches tn e ->
  no_matches tn (proj1_sig (switch_indices_cfun e p sn n)).
Proof with auto.
intros. rewrite switch_indices_switch_indices_b_cfun. unfold switch_indices_b_cfun.
destruct (lookup_cfun_sig_scoped p sn)... generalize 0.
induction e using expr_strong_ind; intros; cbn.
- destruct n0; try rewrite Nat.add_0_l; [destruct n; try rewrite Nat.sub_0_r|]...
  + destruct (v <=? n); unfold no_matches; intros;
      inversion H0; try inversion H2; unfold not; intros; discriminate.
  + destruct (v <=? n); destruct (v <=? n0)...
    * destruct (S n0 + n) eqn:Seq; try omega. destruct (v <=? n1).
      -- unfold no_matches. intros.
         inversion H0; try inversion H2; unfold not; intros; discriminate.
      -- unfold no_matches. intros.
         inversion H0; try inversion H2; unfold not; intros; discriminate.
    * destruct (S n0 + n) eqn:Seq; try omega. destruct (v <=? n1).
      -- unfold no_matches. intros.
         inversion H0; try inversion H2; unfold not; intros; discriminate.
      -- unfold no_matches. intros.
         inversion H0; try inversion H2; unfold not; intros; discriminate.
- simpl in *. unfold no_matches. intros. induction ls.
  + inversion H1; try inversion H3... unfold not. intros. discriminate.
  + inversion H1.
    * unfold not. intros. discriminate.
    * inversion H3; subst. destruct H8.
      -- subst. inversion H0; subst. unfold no_matches in H6.
         apply H6 with (n0:=n1)... clear - H. unfold no_matches in H.
         intros. apply H. apply Sub_Trans with (e2:=a)...
         apply Sub_Constr. apply in_eq.
      -- inversion H0; subst. apply IHls...
         ++ clear - H. unfold no_matches in *. intros. inversion H0.
            ** unfold not. intros. discriminate.
            ** inversion H2; subst. apply H. apply Sub_Trans with (e2:=e2)...
               apply Sub_Constr. right...
         ++ apply Sub_Trans with (e2:=e2)... apply Sub_Constr...
- simpl in *. unfold no_matches. intros. inversion H1; subst.
  + unfold not. intros. discriminate.
  + inversion H3; subst.
    * unfold no_matches in IHe. apply IHe with (n0:=n1)...
      intros. unfold no_matches in H. apply H.
      apply Sub_Trans with (e2:=e)... apply Sub_DestrCall_e0.
    * clear H1 H3. induction ls; inversion H6.
      -- subst. inversion H0; subst. unfold no_matches in H4.
         apply H4 with (n0:=n1)... intros. unfold no_matches in H.
         apply H. apply Sub_Trans with (e2:=a)... apply Sub_DestrCall_es. left...
      -- inversion H0; subst. apply IHls...
         clear - H. unfold no_matches in H. unfold no_matches.
         intros. inversion H0; subst.
         ++ unfold not. intros. discriminate.
         ++ apply H. apply Sub_Trans with (e2:=e2)...
            inversion H2; subst.
            ** apply Sub_DestrCall_e0.
            ** apply Sub_DestrCall_es. right...
- simpl in *. unfold no_matches. intros. induction ls.
  + inversion H1; try inversion H3... unfold not. intros. discriminate.
  + inversion H1.
    * unfold not. intros. discriminate.
    * inversion H3; subst. destruct H8.
      -- subst. inversion H0; subst. unfold no_matches in H6.
         apply H6 with (n0:=n1)... clear - H. unfold no_matches in H.
         intros. apply H. apply Sub_Trans with (e2:=a)...
         apply Sub_FunCall. apply in_eq.
      -- inversion H0; subst. apply IHls...
         ++ clear - H. unfold no_matches in *. intros. inversion H0.
            ** unfold not. intros. discriminate.
            ** inversion H2; subst. apply H. apply Sub_Trans with (e2:=e2)...
               apply Sub_FunCall. right...
         ++ apply Sub_Trans with (e2:=e2)... apply Sub_FunCall...
- simpl in *. unfold no_matches. intros. inversion H1; subst.
  + unfold not. intros. discriminate.
  + inversion H3; subst.
    * unfold no_matches in IHe. apply IHe with (n0:=n0)...
      intros. unfold no_matches in H. apply H.
      apply Sub_Trans with (e2:=e)... apply Sub_ConsFunCall_e0.
    * clear H1 H3. induction ls; inversion H6.
      -- subst. inversion H0; subst. unfold no_matches in H4.
         apply H4 with (n0:=n0)... intros. unfold no_matches in H.
         apply H. apply Sub_Trans with (e2:=a)... apply Sub_ConsFunCall_es. left...
      -- inversion H0; subst. apply IHls...
         clear - H. unfold no_matches in H. unfold no_matches.
         intros. inversion H0; subst.
         ++ unfold not. intros. discriminate.
         ++ apply H. apply Sub_Trans with (e2:=e2)...
            inversion H2; subst.
            ** apply Sub_ConsFunCall_e0.
            ** apply Sub_ConsFunCall_es. right...
- simpl in *. unfold no_matches. intros. induction ls.
  + inversion H1; try inversion H3... unfold not. intros. discriminate.
  + inversion H1.
    * unfold not. intros. discriminate.
    * inversion H3; subst. destruct H8.
      -- subst. inversion H0; subst. unfold no_matches in H6.
         apply H6 with (n0:=n0)... clear - H. unfold no_matches in H.
         intros. apply H. apply Sub_Trans with (e2:=a)...
         apply Sub_GenFunCall. apply in_eq.
      -- inversion H0; subst. apply IHls...
         ++ clear - H. unfold no_matches in *. intros. inversion H0.
            ** unfold not. intros. discriminate.
            ** inversion H2; subst. apply H. apply Sub_Trans with (e2:=e2)...
               apply Sub_GenFunCall. right...
         ++ apply Sub_Trans with (e2:=e2)... apply Sub_GenFunCall...
- case_eq (eq_TypeName tn (fst n0)); intros.
  + exfalso. clear - H H2. unfold no_matches in H. unfold not in H.
    eapply H with (n:=snd n0); try apply Sub_Refl. f_equal.
    rewrite eq_TypeName_eq in H2. subst. destruct n0...
  + simpl in *. unfold no_matches. intros. inversion H3; subst.
    * unfold not. intros. inversion H4; subst.
      rewrite eq_TypeName_refl in H2. discriminate.
    * inversion H5; subst.
      -- unfold no_matches in IHe. apply IHe with (n0:=n1)... clear - H.
         unfold no_matches in H. intros. apply H. apply Sub_Trans with (e2:=e)...
         apply Sub_Match_e0.
      -- induction es; try inversion H8.
         ++ subst. inversion H1; subst. destruct a. simpl in *.
            unfold no_matches in H9. apply H9 with (n0:=n1)... intros.
            clear - H H6. unfold no_matches in H. apply H.
            apply Sub_Trans with (e2:=e1)... apply Sub_Match_bs. left...
         ++ inversion H1; subst. apply IHes...
            ** clear - H H2. unfold no_matches in *. intros.
               inversion H0; subst.
               --- unfold not. intros. inversion H1; subst.
                   rewrite eq_TypeName_refl in H2. discriminate.
               --- apply H. inversion H3; subst.
                   +++ apply Sub_Trans with (e2:=e)... apply Sub_Match_e0...
                   +++ apply Sub_Trans with (e2:=e2)... apply Sub_Match_bs... right...
                   +++ apply Sub_Trans with (e2:=e2)... apply Sub_Match_cases...
            ** apply Sub_Trans with (e2:=e2)... apply Sub_Match_bs...
            ** apply Sub_Match_bs...
      -- unfold no_matches in H. apply H.
         apply Sub_Trans with (e2:=e2)... apply Sub_Match_cases...
- simpl in *. unfold no_matches. intros. inversion H2; subst.
  + unfold not. intros. discriminate.
  + inversion H4; subst.
    * induction es; try inversion H7.
      -- subst. inversion H1; subst. destruct a. simpl in *.
         unfold no_matches in H8. apply H8 with (n0:=n1)... intros.
         clear - H H5. unfold no_matches in H. apply H.
         apply Sub_Trans with (e2:=e)... apply Sub_CoMatch_bs. left...
      -- inversion H1; subst. apply IHes...
         ++ clear - H. unfold no_matches in *. intros.
            inversion H0; subst.
            ** unfold not. intros. discriminate.
            ** apply H. inversion H2; subst.
               --- apply Sub_Trans with (e2:=e2)... apply Sub_CoMatch_bs... right...
               --- apply Sub_Trans with (e2:=e2)... apply Sub_CoMatch_cocases...
         ++ apply Sub_Trans with (e2:=e2)... apply Sub_CoMatch_bs...
         ++ apply Sub_CoMatch_bs...
    * clear - H H3 H7. unfold no_matches in H. apply H.
      apply Sub_Trans with (e2:=e2)... apply Sub_CoMatch_cocases...
- simpl in *. unfold no_matches. intros. inversion H0; subst.
  + unfold not. intros. discriminate.
  + inversion H2; subst.
    * unfold no_matches in IHe1. apply IHe1 with (n0:=n0)... intros.
      unfold no_matches in H. apply H. apply Sub_Trans with (e2:=e1)...
      apply Sub_Let_e1.
    * unfold no_matches in IHe2. apply IHe2 with (n0:=n0+1)... intros.
      unfold no_matches in H. apply H. apply Sub_Trans with (e2:=e2)...
      apply Sub_Let_e2.
Qed.




Definition new_fun_bods (p : program) (tn : TypeName) : fun_bods :=
  map (fun x => (fst x, refunctionalize_expr tn (snd x))) (program_fun_bods p).

Lemma new_has_all_funbods : forall p tn,
  has_all_fun_bods (skeleton_fun_sigs (refunctionalize_to_skeleton p tn)) (new_fun_bods p tn).
Proof with eauto.
intros. unfold has_all_fun_bods. unfold new_fun_bods. rewrite map_map.
pose proof (program_has_all_fun_bods p) as H...
Qed.

Lemma new_funbods_typecheck : forall p tn,
  Forall (no_matches tn) (map snd (program_fun_bods p)) ->
  fun_bods_typecheck (refunctionalize_to_skeleton p tn) (new_fun_bods p tn).
Proof with auto.
intros. unfold fun_bods_typecheck.
pose proof (program_fun_bods_typecheck p).
unfold fun_bods_typecheck in H0.
rewrite Forall_forall in *. intros.
unfold new_fun_bods in H1. rewrite in_map_iff in H1. do 2 (destruct H1).
pose proof (H0 _ H2). do 4 (destruct H3). exists x1. exists x2. exists x3. split.
- inversion H1; subst. simpl in *. rewrite <- H3. unfold lookup_fun_sig...
- destruct x. simpl. inversion H1; subst. apply refunctionalize_expr_preserves_typing...
  unfold no_matches in H. intros. apply H with (x:=snd x0)... apply in_map...
Qed.


Definition new_cfun_bods_g (p : program) (tn : TypeName) : cfun_bods :=
  filter (fun x => match x with (n',_) => negb (eq_TypeName tn (fst n')) end)
         (map (fun x => (fst x, map (fun y => (fst y, refunctionalize_expr tn (snd y))) (snd x)))
              (program_cfun_bods_g p)).

Definition new_has_all_cfunbods_g (p : program) (tn : TypeName) :
  has_all_cfun_bods (skeleton_cfun_sigs_g (refunctionalize_to_skeleton p tn))
    (new_cfun_bods_g p tn).
Proof with eauto.
unfold has_all_cfun_bods. unfold new_cfun_bods_g. simpl. unfold new_cfunsigs_g.
rewrite <- filter_map. rewrite map_map. simpl.
pose proof (program_has_all_cfun_bods_g p) as H. unfold has_all_cfun_bods in H.
erewrite filter_ext; [erewrite filter_ext with (l:=program_cfun_bods_g p)|].
- repeat (rewrite filter_map). rewrite H...
- intros. simpl. change (negb (eq_TypeName tn (fst (fst a)))) with
    ((fun x => (negb (eq_TypeName tn (fst x)))) (fst a))...
- intros. simpl. destruct a. destruct p0...
Qed.

Fact prod_assoc : forall {A B C} (a a2 : A) (b b2 : B) (c c2 : C),
  (a, b, c) = (a2, b2, c2) <-> (a, (b, c)) = (a2, (b2, c2)).
Proof with auto. intros. split; intros; inversion H; subst... Qed.

Corollary new_cfunbods_g_typecheck: forall p tn,
  Forall (no_matches tn) (map snd (flat_map snd (program_cfun_bods_g p))) ->
  cfun_bods_g_typecheck (refunctionalize_to_skeleton p tn) (new_cfun_bods_g p tn).
Proof with eauto.
intros. unfold cfun_bods_g_typecheck. rewrite Forall_forall. intros.
unfold new_cfun_bods_g in H0.
pose proof (program_cfun_bods_typecheck_g p). unfold cfun_bods_g_typecheck in H1.
rewrite Forall_forall in H1. rewrite filter_In in H0. destruct H0.
rewrite in_map_iff in H0. destruct H0 as [x0' [H0Eq H0]]. pose proof H0 as H0'.
apply H1 in H0. do 4 destruct H0. exists x0. exists x1. exists x2. split.
- unfold lookup_cfun_sig_g. unfold lookup_cfun_sig_x. simpl.
  unfold new_cfunsigs_g. unfold lookup_cfun_sig_g in H0. unfold lookup_cfun_sig_x in H0.
  apply find_some in H0. destruct H0. simpl in H4. rewrite eq_QName_eq in H4. subst.
  unfold QName in *. destruct x0'. simpl in H2. change p0 with (fst (fst (p0, x1, x2))) in H2. simpl in H0.
  pose proof (conj H0 H2). change (negb (eq_TypeName tn (fst (fst (fst (p0, x1, x2))))))
    with ((fun y => negb (eq_TypeName tn (fst (fst (fst y))))) (p0, x1, x2)) in H4.
  rewrite <- filter_In in H4. simpl. match goal with [|- ?lhs = _] => case_eq lhs; intros end.
  + apply find_some in H5. destruct H5. rewrite eq_QName_eq in H6. subst.
    match goal with [_ : In (fst (fst p1), x1, x2) (_ ?f _) |- _] => rewrite filter_ext with (g:=f) in H5 end.
    2: { intros. destruct a. destruct p0... }
    pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
    unfold cfun_sigs_names_unique in Uniq. destruct p1. destruct p0. simpl in *. f_equal. apply prod_assoc. f_equal.
    clear - H4 H5 Uniq. generalize dependent (skeleton_cfun_sigs_g (program_skeleton p)).
    induction c; intros; [inversion H4|]. simpl in *. unfold cfun_sig in *. unfold QName in *.
    case_eq (negb (eq_TypeName tn (fst (fst (fst a))))); intros; rewrite H in *.
    * destruct H4; destruct H5.
      -- destruct a. inversion H0. inversion H1. subst. inversion H5. subst...
      -- rewrite filter_In in H1. destruct H1. subst. apply in_map with (f:=fst) in H1.
         apply (in_map fst) in H1. rewrite map_map in H1.
         simpl in *. inversion Uniq. subst. exfalso...
      -- rewrite filter_In in H0. destruct H0. subst. apply in_map with (f:=fst) in H0.
         apply (in_map fst) in H0. rewrite map_map in H0.
         simpl in *. inversion Uniq. subst. exfalso...
      -- inversion Uniq. subst. apply IHc...
    * inversion Uniq. subst. apply IHc...
  + exfalso. apply find_none with (x:=(p0,x1,x2)) in H5.
    * simpl in *. rewrite eq_QName_refl in H5. discriminate.
    * erewrite filter_ext... intros. destruct a. destruct p1...
- destruct x. inversion H0Eq. subst. simpl.
  rename H2 into Flt. clear - H H3 H0' Flt. inversion H3; subst.
  apply T_Match with (ctorlist:=ctorlist)(bindings_exprs:=bindings_exprs)
    (bindings_types:=bindings_types)...
  + clear - H6. inversion H6; subst. apply T_Var...
  + apply listTypeDeriv_lemma in H11. rewrite Nat.eqb_eq in H11.
    clear - H11 H9.
    replace (fst (fst x0') :: x1) with ([fst (fst x0')] ++ x1)...
    rewrite <- (map_fst_combine bindings_exprs bindings_types)... rewrite <- H9.
    rewrite <- (map_snd_combine bindings_exprs bindings_types)... rewrite <- H9.
    replace (map snd (index_list 1 x1)) with x1; try apply index_list_typechecks...
    clear. generalize 0. induction x1; intros... simpl. f_equal...
  + clear - H12 Flt. unfold lookup_ctors in *.
    case_eq (filter (eq_TypeName (fst (fst x0'))) (skeleton_dts (refunctionalize_to_skeleton p tn))); intros.
    * exfalso. case_eq (filter (eq_TypeName (fst (fst x0'))) (skeleton_dts (program_skeleton p))); intros.
      -- rewrite H0 in *. discriminate.
      -- rewrite H0 in *. inversion H12; subst. cbn in H. unfold new_dts in H.
         rewrite filter_filter in H. rewrite H0 in H. clear H12. cbn in *.
         case_eq (negb (eq_TypeName tn t)); intros.
         ++ rewrite H1 in H. discriminate.
         ++ clear H. pose proof (in_eq t l). rewrite <- H0 in H. rewrite filter_In in H. destruct H.
            rewrite negb_true_iff in Flt. rewrite negb_false_iff in H1. rewrite eq_TypeName_eq in *. subst.
            rewrite eq_TypeName_refl in Flt. discriminate.
    * cbn in H. unfold new_dts in H. rewrite filter_filter in H.
      case_eq (filter (eq_TypeName (fst (fst x0'))) (skeleton_dts (program_skeleton p))); intros.
      -- rewrite H0 in H. simpl in H. discriminate.
      -- rewrite H0 in H12. inversion H12; subst. f_equal. cbn. unfold new_ctors. rewrite filter_compose.
         erewrite filter_ext... intros. destruct a.
         case_eq (eq_TypeName (fst (unscope s)) (fst (fst x0'))); intros...
         rewrite eq_TypeName_eq in *. rewrite H1. rewrite Flt...
  + rewrite Forall_forall in H13. rewrite Forall_forall. intros. destruct x. destruct p0.
    destruct p1. assert (exists x0, In (s, x0, (s0, l)) (combine (snd x0') ctorlist)).
    { rewrite <- map_combine_in_fst in H0. rewrite in_map_iff in H0. do 2 destruct H0.
      destruct x. destruct p0. simpl in *. inversion H0; subst. exists e0...
    }
    destruct H1. apply H13 in H1...
  + apply (in_map snd) in H0'. rewrite in_map_iff in H0'.
    rewrite <- (app_nil_l (snd x0')) in H0'. clear - H14 H0' H. rewrite map_map. simpl.
    generalize dependent bindings_types. generalize dependent (snd x0'). generalize (@nil (ScopedName*expr)). clear - H.
    induction ctorlist; intros; pose proof H14 as H14'; apply listTypeDeriv'_lemma_ctx in H14;
      rewrite Nat.eqb_eq in H14; simpl in H14; destruct l0; try discriminate; try apply ListTypeDeriv'_Nil.
    inversion H14'; subst. simpl. apply ListTypeDeriv'_Cons...
    * apply refunctionalize_expr_preserves_typing... intros.
      destruct H0'. destruct H1. clear - H H1 H2 H0.
      rewrite Forall_forall in H. unfold no_matches in H.
      inversion H0; subst.
      -- eapply H... apply in_map. destruct x. simpl in *. subst.
         rewrite in_flat_map. eexists. split... simpl. clear. induction l; [apply in_eq|apply in_cons]...
      -- apply H with (x:=snd p0)... apply in_map. destruct x. simpl in *. subst.
         rewrite in_flat_map. eexists. split... simpl. clear. induction l; [apply in_eq|apply in_cons]...
    * intros. apply IHctorlist with (l:=l++[p0])... destruct H0'. destruct H0. exists x.
      rewrite <- app_assoc. split...
Qed.



Definition new_cfun_bods_l (p : program) (tn : TypeName) : cfun_bods :=
  filter (fun x => match x with (n',_) => negb (eq_TypeName tn (fst n')) end)
         (map (fun x => (fst x, map (fun y => (fst y, refunctionalize_expr tn (snd y))) (snd x)))
              (program_cfun_bods_l p)).

Definition new_has_all_cfunbods_l (p : program) (tn : TypeName) :
  has_all_cfun_bods (skeleton_cfun_sigs_l (refunctionalize_to_skeleton p tn))
    (new_cfun_bods_l p tn).
Proof with eauto.
unfold has_all_cfun_bods. unfold new_cfun_bods_l. simpl. unfold new_cfunsigs_l.
rewrite <- filter_map. rewrite map_map. simpl.
pose proof (program_has_all_cfun_bods_l p) as H. unfold has_all_cfun_bods in H.
erewrite filter_ext; [erewrite filter_ext with (l:=program_cfun_bods_l p)|].
- repeat (rewrite filter_map). rewrite H...
- intros. simpl. change (negb (eq_TypeName tn (fst (fst a)))) with
    ((fun x => (negb (eq_TypeName tn (fst x)))) (fst a))...
- intros. simpl. destruct a. destruct p0...
Qed.

Corollary new_cfunbods_l_typecheck: forall p tn,
  Forall (no_matches tn) (map snd (flat_map snd (program_cfun_bods_l p))) ->
  cfun_bods_l_typecheck (refunctionalize_to_skeleton p tn) (new_cfun_bods_l p tn).
Proof with eauto.
intros. unfold cfun_bods_l_typecheck. rewrite Forall_forall. intros.
unfold new_cfun_bods_l in H0.
pose proof (program_cfun_bods_typecheck_l p). unfold cfun_bods_l_typecheck in H1.
rewrite Forall_forall in H1. rewrite filter_In in H0. destruct H0.
rewrite in_map_iff in H0. destruct H0 as [x0' [H0Eq H0]]. pose proof H0 as H0'.
apply H1 in H0. do 4 destruct H0. exists x0. exists x1. exists x2. split.
- unfold lookup_cfun_sig_l. unfold lookup_cfun_sig_x. simpl.
  unfold new_cfunsigs_l. unfold lookup_cfun_sig_l in H0. unfold lookup_cfun_sig_x in H0.
  apply find_some in H0. destruct H0. simpl in H4. rewrite eq_QName_eq in H4. subst.
  unfold QName in *. destruct x0'. simpl in H2. change p0 with (fst (fst (p0, x1, x2))) in H2. simpl in H0.
  pose proof (conj H0 H2). change (negb (eq_TypeName tn (fst (fst (fst (p0, x1, x2))))))
    with ((fun y => negb (eq_TypeName tn (fst (fst (fst y))))) (p0, x1, x2)) in H4.
  rewrite <- filter_In in H4. simpl. match goal with [|- ?lhs = _] => case_eq lhs; intros end.
  + apply find_some in H5. destruct H5. rewrite eq_QName_eq in H6. subst.
    match goal with [_ : In (fst (fst p1), x1, x2) (_ ?f _) |- _] => rewrite filter_ext with (g:=f) in H5 end.
    2: { intros. destruct a. destruct p0... }
    pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
    unfold cfun_sigs_names_unique in Uniq. destruct p1. destruct p0. simpl in *. f_equal. apply prod_assoc. f_equal.
    clear - H4 H5 Uniq. generalize dependent (skeleton_cfun_sigs_l (program_skeleton p)).
    induction c; intros; [inversion H4|]. simpl in *. unfold cfun_sig in *. unfold QName in *.
    case_eq (negb (eq_TypeName tn (fst (fst (fst a))))); intros; rewrite H in *.
    * destruct H4; destruct H5.
      -- destruct a. inversion H0. inversion H1. subst. inversion H5. subst...
      -- rewrite filter_In in H1. destruct H1. subst. apply in_map with (f:=fst) in H1.
         apply (in_map fst) in H1. rewrite map_map in H1.
         simpl in *. inversion Uniq. subst. exfalso...
      -- rewrite filter_In in H0. destruct H0. subst. apply in_map with (f:=fst) in H0.
         apply (in_map fst) in H0. rewrite map_map in H0.
         simpl in *. inversion Uniq. subst. exfalso...
      -- inversion Uniq. subst. apply IHc...
    * inversion Uniq. subst. apply IHc...
  + exfalso. apply find_none with (x:=(p0,x1,x2)) in H5.
    * simpl in *. rewrite eq_QName_refl in H5. discriminate.
    * erewrite filter_ext... intros. destruct a. destruct p1...
- destruct x. inversion H0Eq. subst. simpl.
  rename H2 into Flt. clear - H H3 H0' Flt. inversion H3; subst.
  apply T_Match with (ctorlist:=ctorlist)(bindings_exprs:=bindings_exprs)
    (bindings_types:=bindings_types)...
  + clear - H6. inversion H6; subst. apply T_Var...
  + apply listTypeDeriv_lemma in H11. rewrite Nat.eqb_eq in H11.
    clear - H11 H9.
    replace (fst (fst x0') :: x1) with ([fst (fst x0')] ++ x1)...
    rewrite <- (map_fst_combine bindings_exprs bindings_types)... rewrite <- H9.
    rewrite <- (map_snd_combine bindings_exprs bindings_types)... rewrite <- H9.
    replace (map snd (index_list 1 x1)) with x1; try apply index_list_typechecks...
    clear. generalize 0. induction x1; intros... simpl. f_equal...
  + clear - H12 Flt. unfold lookup_ctors in *.
    case_eq (filter (eq_TypeName (fst (fst x0'))) (skeleton_dts (refunctionalize_to_skeleton p tn))); intros.
    * exfalso. case_eq (filter (eq_TypeName (fst (fst x0'))) (skeleton_dts (program_skeleton p))); intros.
      -- rewrite H0 in *. discriminate.
      -- rewrite H0 in *. inversion H12; subst. cbn in H. unfold new_dts in H.
         rewrite filter_filter in H. rewrite H0 in H. clear H12. cbn in *.
         case_eq (negb (eq_TypeName tn t)); intros.
         ++ rewrite H1 in H. discriminate.
         ++ clear H. pose proof (in_eq t l). rewrite <- H0 in H. rewrite filter_In in H. destruct H.
            rewrite negb_true_iff in Flt. rewrite negb_false_iff in H1. rewrite eq_TypeName_eq in *. subst.
            rewrite eq_TypeName_refl in Flt. discriminate.
    * cbn in H. unfold new_dts in H. rewrite filter_filter in H.
      case_eq (filter (eq_TypeName (fst (fst x0'))) (skeleton_dts (program_skeleton p))); intros.
      -- rewrite H0 in H. simpl in H. discriminate.
      -- rewrite H0 in H12. inversion H12; subst. f_equal. cbn. unfold new_ctors. rewrite filter_compose.
         erewrite filter_ext... intros. destruct a.
         case_eq (eq_TypeName (fst (unscope s)) (fst (fst x0'))); intros...
         rewrite eq_TypeName_eq in *. rewrite H1. rewrite Flt...
  + rewrite Forall_forall in H13. rewrite Forall_forall. intros. destruct x. destruct p0.
    destruct p1. assert (exists x0, In (s, x0, (s0, l)) (combine (snd x0') ctorlist)).
    { rewrite <- map_combine_in_fst in H0. rewrite in_map_iff in H0. do 2 destruct H0.
      destruct x. destruct p0. simpl in *. inversion H0; subst. exists e0...
    }
    destruct H1. apply H13 in H1...
  + apply (in_map snd) in H0'. rewrite in_map_iff in H0'.
    rewrite <- (app_nil_l (snd x0')) in H0'. clear - H14 H0' H. rewrite map_map. simpl.
    generalize dependent bindings_types. generalize dependent (snd x0'). generalize (@nil (ScopedName*expr)). clear - H.
    induction ctorlist; intros; pose proof H14 as H14'; apply listTypeDeriv'_lemma_ctx in H14;
      rewrite Nat.eqb_eq in H14; simpl in H14; destruct l0; try discriminate; try apply ListTypeDeriv'_Nil.
    inversion H14'; subst. simpl. apply ListTypeDeriv'_Cons...
    * apply refunctionalize_expr_preserves_typing... intros.
      destruct H0'. destruct H1. clear - H H1 H2 H0.
      rewrite Forall_forall in H. unfold no_matches in H.
      inversion H0; subst.
      -- eapply H... apply in_map. destruct x. simpl in *. subst.
         rewrite in_flat_map. eexists. split... simpl. clear. induction l; [apply in_eq|apply in_cons]...
      -- apply H with (x:=snd p0)... apply in_map. destruct x. simpl in *. subst.
         rewrite in_flat_map. eexists. split... simpl. clear. induction l; [apply in_eq|apply in_cons]...
    * intros. apply IHctorlist with (l:=l++[p0])... destruct H0'. destruct H0. exists x.
      rewrite <- app_assoc. split...
Qed.


(**************************************************************************************************)
(** Computing the new gfunbods                                                                    *)
(**************************************************************************************************)

(* Part 1: Global gfuns *)

Definition gfunbods_mapfun (x : ScopedName * expr) :=
  match x with (x1,x2) => (unscope x1, x2) end.

Definition gfunbods_filterfun_g (q : QName) (x : QName * (ScopedName * expr)) :=
  match x with
  | ((tn, _), (global q', _)) => andb (eq_TypeName tn (fst q)) (eq_QName q q')
  | _ => false
  end.

Definition switch_indices_aux (p : skeleton )(sn : ScopedName) (n : nat) (tn : TypeName) (e : expr) :=
  refunctionalize_expr tn (proj1_sig (switch_indices_cfun e p sn n)).

Definition globalize_aux {B} := map (fun x : QName * B => (global (fst x), snd x)).
Definition localize_aux {B} := map (fun x : QName * B => (local (fst x), snd x)).

Definition new_gfun_bods_g (p : program) (tn : TypeName) : gfun_bods :=
   (map (fun ctor => (unscope (fst ctor),
         (map (fun x =>
               (fst x,
                switch_indices_aux (program_skeleton p) (fst x) (length (snd ctor)) tn (snd (snd x))))
              (globalize_aux
               (filter (gfunbods_filterfun_g (unscope (fst ctor)))
                       (flat_map (fun x => (map (fun y => (fst x, y)) (snd x)))
                                 (program_cfun_bods_g p))))) ++
         (map (fun x =>
               (fst x,
                switch_indices_aux (program_skeleton p) (fst x) (length (snd ctor)) tn (snd (snd x))))
              (localize_aux
               (filter (gfunbods_filterfun_g (unscope (fst ctor)))
                       (flat_map (fun x => (map (fun y => (fst x, y)) (snd x)))
                                 (program_cfun_bods_l p)))))))
        (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p)))) ++
   (map (fun x => (fst x, map (fun y => (fst y, refunctionalize_expr tn (snd y))) (snd x)))
        (program_gfun_bods_g p)).

Definition new_has_all_gfunbods_g (p : program) (tn : TypeName) :
  has_all_gfun_bods (skeleton_gfun_sigs_g (refunctionalize_to_skeleton p tn))
    (new_gfun_bods_g p tn).
Proof with eauto.
intros. unfold has_all_gfun_bods. unfold new_gfun_bods_g. rewrite map_app.
repeat (rewrite map_map). simpl. unfold new_gfunsigs_g. rewrite map_app.
repeat (rewrite map_map). f_equal.
- unfold gfunsigs_mapfun. apply map_ext. intros. destruct a...
- apply (program_has_all_gfun_bods_g p).
Qed.

(* Part 2: Local gfuns *)

Definition gfunbods_filterfun_l (q : QName) (x : QName * (ScopedName * expr)) :=
  match x with
  | ((tn, _), (local q', _)) => andb (eq_TypeName tn (fst q)) (eq_QName q q')
  | _ => false
  end.

Definition new_gfun_bods_l (p : program) (tn : TypeName) : gfun_bods :=
   (map (fun ctor => (unscope (fst ctor),
         (map (fun x =>
               (fst x,
                switch_indices_aux (program_skeleton p) (fst x) (length (snd ctor)) tn (snd (snd x))))
              (globalize_aux
               (filter (gfunbods_filterfun_l (unscope (fst ctor)))
                       (flat_map (fun x => (map (fun y => (fst x, y)) (snd x)))
                                 (program_cfun_bods_g p))))) ++
         (map (fun x =>
               (fst x,
                switch_indices_aux (program_skeleton p) (fst x) (length (snd ctor)) tn (snd (snd x))))
              (localize_aux
               (filter (gfunbods_filterfun_l (unscope (fst ctor)))
                       (flat_map (fun x => (map (fun y => (fst x, y)) (snd x)))
                                 (program_cfun_bods_l p)))))))
        (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p)))) ++
   (map (fun x => (fst x, map (fun y => (fst y, refunctionalize_expr tn (snd y))) (snd x)))
        (program_gfun_bods_l p)).

Definition new_has_all_gfunbods_l (p : program) (tn : TypeName) :
  has_all_gfun_bods (skeleton_gfun_sigs_l (refunctionalize_to_skeleton p tn))
    (new_gfun_bods_l p tn).
Proof with eauto.
intros. unfold has_all_gfun_bods. unfold new_gfun_bods_l. rewrite map_app.
repeat (rewrite map_map). simpl. unfold new_gfunsigs_l. rewrite map_app.
repeat (rewrite map_map). f_equal.
- unfold gfunsigs_mapfun. apply map_ext. intros. destruct a...
- apply (program_has_all_gfun_bods_l p).
Qed.



(**************************************************************************************************)
(** Typechecking the new gfunbods                                                                 *)
(**************************************************************************************************)


(**************************************************************************************************)
(** Part 0: Some generic lemmas and auxiliary definitions                                         *)
(**************************************************************************************************)

Fact index_list_typechecks' : forall (s : skeleton) (l : list TypeName) (x : TypeName),
  s // (x::l) ||- map fst (index_list 1 l) :: l.
Proof.
intros. rewrite <- (app_nil_l l) at 1. change 1 with (length (A:=TypeName) [x]).
generalize (nil (A:=TypeName)).
induction l; intros; try apply ListTypeDeriv_Nil. simpl.
apply ListTypeDeriv_Cons.
- apply T_Var. induction l0; auto.
- specialize IHl with (l0 ++ [a]). rewrite <- app_assoc in IHl. simpl in IHl.
  rewrite app_length in IHl. simpl in IHl.
  replace (S (length l0)) with (length l0 + 1); omega + auto.
Qed.

Fact app_unique_2 : forall {A} (l1 l2 : list A),
  Unique.unique (l1++l2) ->
  Unique.unique l2.
Proof with auto.
intros. generalize dependent l2. induction l1; intros...
apply IHl1. inversion H...
Qed.

Lemma ListTypeDeriv'_split : forall p cs0 c cs0' es0 e es0' ts0 t ts0',
  length cs0 = length es0 ->
  length es0 = length ts0 ->
  p /// (cs0 ++ c :: cs0') |||- (es0 ++ e :: es0') ::: (ts0 ++ t :: ts0') ->
  p / c |- e : t.
Proof with eauto.
intros. generalize dependent es0. generalize dependent ts0. induction cs0; intros.
- destruct es0; try discriminate. destruct ts0; try discriminate.
  inversion H1; subst...
- destruct es0; try discriminate. destruct ts0; try discriminate.
  inversion H1; subst. eapply IHcs0...
Qed.

Lemma firstn_nth : forall {A} n (l : list A) d,
  length (firstn (S n) l) = S n ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof with auto.
intros. generalize dependent l. induction n; intros.
- rewrite firstn_O. simpl. destruct l; try discriminate...
- destruct l; try (rewrite firstn_nil in H; discriminate).
  simpl. f_equal. destruct l; try discriminate.
  rewrite <- IHn...
Qed.

Definition from_some_default {A} (d : A) (a : option A): A :=
  match a with
  | Some a' => a'
  | None => d
  end.

Fact skipn_map : forall {A B} n (l: list A) (f : A -> B),
  skipn n (map f l) = map f (skipn n l).
Proof with auto.
intros. generalize dependent n. induction l; intros; [induction n|]...
simpl. destruct n... simpl...
Qed.

Fact skipn_In : forall {A} (x : A) n l, In x (skipn n l) -> In x l.
Proof with eauto.
intros. generalize dependent n. induction l; try destruct n...
intros. right...
Qed.

Lemma sigs_bods_g_length : forall p (x0 : ScopedName * list TypeName),
  length
    (filter
      (fun x1 : TypeName * Name * list TypeName * TypeName =>
       eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
      (skeleton_cfun_sigs_g (program_skeleton p))) =
  length
    (filter
      (fun x1 : TypeName * Name * list (ScopedName * expr) =>
       eq_TypeName (fst (unscope (fst x0))) (fst (fst x1)))
      (program_cfun_bods_g p)).
Proof with eauto.
intros. rewrite <- map_length with (f:=fun x => fst (fst x)). erewrite filter_ext.
- rewrite filter_map. rewrite (program_has_all_cfun_bods_g p).
  rewrite <- map_length with (f:=@fst _ (list (ScopedName * expr))).
  erewrite filter_ext with (l:=program_cfun_bods_g p).
  + rewrite filter_map...
  + intros. simpl.
    change (eq_TypeName ?y (fst (fst a)))
    with ((fun x => eq_TypeName y (fst x)) (fst a))...
- intros...
Qed.

Lemma sigs_bods_l_length : forall p (x0 : ScopedName * list TypeName),
  length
    (filter
      (fun x1 : TypeName * Name * list TypeName * TypeName =>
       eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
      (skeleton_cfun_sigs_l (program_skeleton p))) =
  length
    (filter
      (fun x1 : TypeName * Name * list (ScopedName * expr) =>
       eq_TypeName (fst (unscope (fst x0))) (fst (fst x1)))
      (program_cfun_bods_l p)).
Proof with eauto.
intros. rewrite <- map_length with (f:=fun x => fst (fst x)). erewrite filter_ext.
- rewrite filter_map. rewrite (program_has_all_cfun_bods_l p).
  rewrite <- map_length with (f:=@fst _ (list (ScopedName * expr))).
  erewrite filter_ext with (l:=program_cfun_bods_l p).
  + rewrite filter_map...
  + intros. simpl.
    change (eq_TypeName ?y (fst (fst a)))
    with ((fun x => eq_TypeName y (fst x)) (fst a))...
- intros...
Qed.

Fact filter_length_lt : forall {A} (l : list A) f,
  length (filter f l) <= length l.
Proof with auto. intros. induction l... cbn. destruct (f a)... cbn. omega. Qed.


(**************************************************************************************************)
(** Part 1: Typechecking global gfunbods                                                          *)
(**************************************************************************************************)

Lemma gfun_sig_lookup : forall x0 p tn l q,
  In x0 (skeleton_ctors (program_skeleton p)) ->
  fst x0 = global q ->
  eq_TypeName tn (fst (unscope (fst x0))) = true ->
  lookup_gfun_sig_x
    ((map gfunsigs_mapfun
          (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))))
     ++ l) (unscope (fst x0)) =
    Some (unscope (fst x0), snd x0).
Proof with auto.
intros.
apply in_split in H. do 2 (destruct H). rewrite H.
assert (exists l', skeleton_ctors (program_skeleton p) = l'++x++x0::x1).
{ exists []... }
clear H. rename H2 into H.
induction x.
- simpl. destruct x0. simpl in H0. subst. simpl in *. rewrite H1.
  simpl. rewrite eq_QName_refl...
- simpl. case_eq (gfunsigs_filterfun_g tn a); intros.
  + simpl.
    case_eq (eq_QName (unscope (fst x0)) (fst (gfunsigs_mapfun a)));
     intros.
    * pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)).
      unfold dts_ctor_names_unique in H4. destruct H.
      unfold gfunsigs_filterfun_g in H2. destruct a.
      destruct s; try discriminate. clear - H H0 H3 H4. rewrite H in H4.
      simpl in *. clear H. exfalso. induction x2.
      -- inversion H4. apply H2. clear - H0 H3. induction x.
         ++ rewrite eq_QName_eq in H3. subst. simpl. left. rewrite H0...
         ++ simpl. right. apply IHx.
      -- apply IHx2. inversion H4...
    * apply IHx. destruct H. exists (x2 ++ [a]). rewrite <- app_assoc...
  + apply IHx. destruct H. exists (x2 ++ [a]). rewrite <- app_assoc...
Qed.

Lemma filter_gfunbods_filterfun_g_unique :
forall p (a : QName) (a' : cfun_bod_named) q x0,
  is_global (fst x0) ->
  q = unscope (fst x0) ->
  In x0 (skeleton_ctors (program_skeleton p)) ->
  eq_TypeName (fst (unscope (fst x0))) (fst a) = true ->
  a = fst a' ->
  (exists l' l, l' ++ a' :: l = program_cfun_bods_g p) ->
  map fst
      (filter (gfunbods_filterfun_g q)
              (map (fun y : ScopedName * expr => (a, y)) (snd a')))
  = [a].
Proof with eauto.
intros p a a' q x0 Glob qEq x0In eqTyp eqA H.
assert (length (filter (gfunbods_filterfun_g q) (map (fun y => (a, y)) (snd a'))) = 1).
{ pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
  unfold cfun_sigs_names_unique in Uniq.
  case_eq (filter (gfunbods_filterfun_g q) (map (fun y => (a, y)) (snd a'))); intros.
  - exfalso. pose proof (program_cfun_bods_typecheck_g p) as Typ.
    unfold cfun_bods_g_typecheck in Typ.
    rewrite Forall_forall in Typ.
    assert (In a' (program_cfun_bods_g p)).
    { destruct H as [l1 [l2 H]]. rewrite <- H. clear.
      induction l1; try apply in_eq. right...
    }
    apply Typ in H1. destruct H1 as [qn [args [t [H1_1 H1_2]]]].
    inversion H1_2. subst.
    apply (f_equal (map (fun x => (fst x, fst (snd x))))) in H0.
    set (q:=unscope (fst x0)) in *. unfold QName in H0.
    rewrite filter_ext with (g:=fun y => (fun x => match x with
    | ((tn, _), global q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
    | _ => false
    end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    2: { intros. destruct a. simpl. destruct p0. destruct p1... }
    change
      (fun y : TypeName * Name * (ScopedName * expr) =>
        let (tn, _) := fst y in
        match fst (snd y) with
        | local _ => false
        | global q' => eq_TypeName tn (fst q) && eq_QName q q'
        end)
    with
      (fun y : TypeName * Name * (ScopedName * expr) => (fun x => match x with
        | ((tn, _), global q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
        | _ => false
        end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    rewrite filter_map in H0. rewrite map_map in H0. simpl in H0.
    match goal with [H0 : filter ?t ?t2 = _ |- _] => set (flt := filter t t2) in * end.
    assert (In (fst a', fst x0) flt); [|rewrite H0 in H1]...
    unfold flt. rewrite filter_In. split.
    + rewrite <- map_map. rewrite in_map_iff. exists (fst x0). split...
      assert (map fst (snd a') = map fst ctorlist) as CtorlistEq.
      { clear - H13 H14. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H14) as Len. clear H14.
        rewrite map_length in Len.
        unfold cfun_bod in *. generalize dependent ctorlist.
        generalize (@snd _ (list (prod ScopedName expr)) a'). induction l; intros.
        - destruct ctorlist; try discriminate...
        - destruct ctorlist; try discriminate. simpl. f_equal.
          + inversion H13. subst. destruct a. destruct p0...
          + apply IHl... inversion H13...
      }
      unfold QName in *. rewrite CtorlistEq.
      rewrite in_map_iff. exists x0. split...
      unfold lookup_ctors in H12.
      case_eq (filter (eq_TypeName (fst (fst a')))
         (skeleton_dts (program_skeleton p))); intros.
      * unfold cfun_bod in *. unfold QName in *. rewrite H1 in H12. discriminate.
      * unfold cfun_bod in *. unfold QName in *. rewrite H1 in H12. inversion H12.
        rewrite filter_In. split...
        destruct x0...
    + destruct a'. simpl. destruct q0. case_eq (fst x0); intros.
      * inversion Glob. rewrite H1 in H3. discriminate.
      * unfold q. rewrite H1. simpl. rewrite eq_QName_refl.
        simpl in eqTyp. rewrite eq_TypeName_eq in eqTyp. subst.
        unfold q. rewrite H1. simpl. rewrite eq_TypeName_refl...
  - clear eqTyp eqA. case_eq l; intros... exfalso. rewrite H1 in H0.
    pose proof (program_cfun_bods_typecheck_g p) as Typ.
    unfold cfun_bods_g_typecheck in Typ.
    rewrite Forall_forall in Typ.
    assert (In a' (program_cfun_bods_g p)).
    { destruct H as [l1 [l2 H]]. rewrite <- H. clear.
      induction l1; try apply in_eq. right...
    }
    apply Typ in H2. clear - H0 H2. destruct H2 as [qn [args [t [H2_1 H2_2]]]].
    inversion H2_2. subst.
    pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as Len.
    clear - H0 H11 H12 Len.
    unfold QName in H0.
    apply (f_equal (map (fun x => (fst x, fst (snd x))))) in H0.
    rewrite filter_ext with (g:=fun y => (fun x => match x with
    | ((tn, _), global q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
    | _ => false
    end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    2: { intros. destruct a0. simpl. destruct p3... }
    change
      (fun y : TypeName * Name * (ScopedName * expr) =>
        let (tn, _) := fst y in
        match fst (snd y) with
        | local _ => false
        | global q' => eq_TypeName tn (fst q) && eq_QName q q'
        end)
    with
      (fun y : TypeName * Name * (ScopedName * expr) => (fun x => match x with
        | ((tn, _), global q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
        | _ => false
        end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    rewrite filter_map in H0.
    rewrite map_map in H0. simpl in H0.
    assert (Unique.unique (map (fun x : ScopedName * expr => (a, fst x)) (snd a'))) as Uniq.
    { clear - H11 H12 Len. generalize H12. clear H12.
      assert (exists l, lookup_ctors (program_skeleton p) (fst (fst a')) = Some (l ++ ctorlist)).
      { exists []... }
      clear H11. generalize dependent ctorlist.
      change (list (ScopedName * expr)) with cfun_bod. generalize (snd a').
      induction c; intros.
      - apply Unique.Unique_nil.
      - simpl. apply Unique.Unique_cons.
        + clear - H H12 Len. destruct H as [l H].
          unfold lookup_ctors in H.
          destruct (filter (eq_TypeName (fst (fst a')))
            (skeleton_dts (program_skeleton p))); try discriminate.
          inversion H. clear H.
          pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
          unfold dts_ctor_names_unique in Uniq.
          apply (f_equal (map fst)) in H1.
          rewrite filter_ext with (g:=(fun y : ScopedName * list TypeName =>
             (fun x => eq_TypeName (fst (unscope x)) (fst (fst a')))
              (fst y))) in H1.
          2: { intros. destruct a1... }
          change (fun y => eq_TypeName (fst (unscope (fst y))) (fst (fst a')))
          with (fun y : ScopedName * list TypeName =>
                (fun x => eq_TypeName (fst (unscope x)) (fst (fst a')))
                (fst y)) in H1.
          rewrite filter_map in H1.
          pose proof (Unique.filter_unique _
            (fun x : ScopedName => eq_TypeName (fst (unscope x)) (fst (fst a'))) _ Uniq).
          rewrite H1 in H. clear - H12 H Len. rewrite map_app in H. apply app_unique_2 in H.
          inversion H; subst.
          * destruct ctorlist; simpl in H1; try discriminate.
          * destruct ctorlist; simpl in H0; try discriminate.
            inversion H0. subst. clear - H12 H1 Len. unfold not. intros. apply H1.
            inversion H12. subst. destruct a0. destruct p. subst. simpl in *.
            rewrite in_map_iff in H. destruct H as [x [H_1 H_2]].
            apply (in_map fst) in H_2. inversion H_1; subst.
            replace (map fst ctorlist) with (map fst c)...
            clear - H4 Len. generalize dependent ctorlist. induction c; intros.
            -- destruct ctorlist; try discriminate...
            -- destruct ctorlist; try discriminate. inversion H4. subst.
               destruct a. destruct p. simpl. f_equal...
        + destruct ctorlist.
          * apply IHc with (ctorlist:=[]); try inversion Len...
          * apply IHc with (ctorlist:=ctorlist); try inversion H12...
            destruct H as [l0 H]. exists (l0++[p0]). rewrite <- app_assoc...
    }
    eapply Unique.filter_unique in Uniq.
    unfold QName in *. rewrite H0 in Uniq.
    set (ml:=map (fun x : TypeName * Name * (ScopedName * expr) => (fst x, fst (snd x))) l0).
    pose proof (in_eq (fst p0, fst (snd p0)) ((fst p1, fst (snd p1)) :: ml)).
    pose proof (in_cons (fst p0, fst (snd p0)) _ _ (in_eq (fst p1, fst (snd p1)) ml)).
    unfold ml in *. pose proof H as Aux1. pose proof H1 as Aux2.
    rewrite <- H0 in Aux1. rewrite <- H0 in Aux2.
    rewrite filter_In in Aux1. rewrite filter_In in Aux2.
    inversion Uniq. subst. apply H4.
    assert (fst p0 = fst p1) as Eq1.
    { clear - Aux1 Aux2. destruct Aux1 as [Aux1 _]. destruct Aux2 as [Aux2 _].
      rewrite in_map_iff in Aux1. rewrite in_map_iff in Aux2.
      destruct Aux1 as [tmp1 [Aux1 _]]. destruct Aux2 as [tmp2 [Aux2 _]].
      inversion Aux1. inversion Aux2. subst...
    }
    assert (fst (snd p0) = fst (snd p1)) as Eq2.
    { destruct Aux1 as [_ Aux1]. destruct Aux2 as [_ Aux2]. clear - Aux1 Aux2.
      case_eq (fst (snd p0)); intros; rewrite H in Aux1; destruct (fst p0).
      - discriminate.
      - case_eq (fst (snd p1)); intros; rewrite H0 in Aux2; destruct (fst p1).
        + discriminate.
        + rewrite andb_true_iff in Aux1. destruct Aux1 as [_ Aux1].
          rewrite andb_true_iff in Aux2. destruct Aux2 as [_ Aux2].
          rewrite eq_QName_eq in Aux1. rewrite eq_QName_eq in Aux2. subst...
    }
    rewrite Eq1. rewrite Eq2. apply in_eq.
}
case_eq (filter (gfunbods_filterfun_g q) (map (fun y => (a, y)) (snd a'))); intros.
- apply (f_equal (length (A:=_))) in H1. rewrite H0 in H1. simpl in H1. discriminate.
- destruct l.
  + destruct p0. simpl. inversion H1. pose proof (in_eq (q0,p0) []).
    rewrite <- H3 in H2. rewrite filter_In in H2. destruct H2. rewrite in_map_iff in H2.
    destruct H2. inversion H2. inversion H5...
  + apply (f_equal (length (A:=_))) in H1. rewrite H0 in H1. simpl in H1. discriminate.
Qed.

Lemma filter_gfunbods_filterfun_g_unique_l :
forall p (a : QName) (a' : cfun_bod_named) q x0,
  is_global (fst x0) ->
  q = unscope (fst x0) ->
  In x0 (skeleton_ctors (program_skeleton p)) ->
  eq_TypeName (fst (unscope (fst x0))) (fst a) = true ->
  a = fst a' ->
  (exists l' l, l' ++ a' :: l = program_cfun_bods_l p) ->
  map fst
      (filter (gfunbods_filterfun_g q)
              (map (fun y : ScopedName * expr => (a, y)) (snd a')))
  = [a].
Proof with eauto.
intros p a a' q x0 Glob qEq x0In eqTyp eqA H.
assert (length (filter (gfunbods_filterfun_g q) (map (fun y => (a, y)) (snd a'))) = 1).
{ pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
  unfold cfun_sigs_names_unique in Uniq.
  case_eq (filter (gfunbods_filterfun_g q) (map (fun y => (a, y)) (snd a'))); intros.
  - exfalso. pose proof (program_cfun_bods_typecheck_l p) as Typ.
    unfold cfun_bods_l_typecheck in Typ.
    rewrite Forall_forall in Typ.
    assert (In a' (program_cfun_bods_l p)).
    { destruct H as [l1 [l2 H]]. rewrite <- H. clear.
      induction l1; try apply in_eq. right...
    }
    apply Typ in H1. destruct H1 as [qn [args [t [H1_1 H1_2]]]].
    inversion H1_2. subst.
    apply (f_equal (map (fun x => (fst x, fst (snd x))))) in H0.
    set (q:=unscope (fst x0)) in *. unfold QName in H0.
    rewrite filter_ext with (g:=fun y => (fun x => match x with
    | ((tn, _), global q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
    | _ => false
    end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    2: { intros. destruct a. simpl. destruct p0. destruct p1... }
    change
      (fun y : TypeName * Name * (ScopedName * expr) =>
        let (tn, _) := fst y in
        match fst (snd y) with
        | local _ => false
        | global q' => eq_TypeName tn (fst q) && eq_QName q q'
        end)
    with
      (fun y : TypeName * Name * (ScopedName * expr) => (fun x => match x with
        | ((tn, _), global q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
        | _ => false
        end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    rewrite filter_map in H0. rewrite map_map in H0. simpl in H0.
    match goal with [H0 : filter ?t ?t2 = _ |- _] => set (flt := filter t t2) in * end.
    assert (In (fst a', fst x0) flt); [|rewrite H0 in H1]...
    unfold flt. rewrite filter_In. split.
    + rewrite <- map_map. rewrite in_map_iff. exists (fst x0). split...
      assert (map fst (snd a') = map fst ctorlist) as CtorlistEq.
      { clear - H13 H14. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H14) as Len. clear H14.
        rewrite map_length in Len.
        unfold cfun_bod in *. generalize dependent ctorlist.
        generalize (@snd _ (list (prod ScopedName expr)) a'). induction l; intros.
        - destruct ctorlist; try discriminate...
        - destruct ctorlist; try discriminate. simpl. f_equal.
          + inversion H13. subst. destruct a. destruct p0...
          + apply IHl... inversion H13...
      }
      unfold QName in *. rewrite CtorlistEq.
      rewrite in_map_iff. exists x0. split...
      unfold lookup_ctors in H12.
      case_eq (filter (eq_TypeName (fst (fst a')))
         (skeleton_dts (program_skeleton p))); intros.
      * unfold cfun_bod in *. unfold QName in *. rewrite H1 in H12. discriminate.
      * unfold cfun_bod in *. unfold QName in *. rewrite H1 in H12. inversion H12.
        rewrite filter_In. split...
        destruct x0...
    + destruct a'. simpl. destruct q0. case_eq (fst x0); intros.
      * inversion Glob. rewrite H1 in H3. discriminate.
      * unfold q. rewrite H1. simpl. rewrite eq_QName_refl.
        simpl in eqTyp. rewrite eq_TypeName_eq in eqTyp. subst.
        unfold q. rewrite H1. simpl. rewrite eq_TypeName_refl...
  - clear eqTyp eqA. case_eq l; intros... exfalso. rewrite H1 in H0.
    pose proof (program_cfun_bods_typecheck_l p) as Typ.
    unfold cfun_bods_l_typecheck in Typ.
    rewrite Forall_forall in Typ.
    assert (In a' (program_cfun_bods_l p)).
    { destruct H as [l1 [l2 H]]. rewrite <- H. clear.
      induction l1; try apply in_eq. right...
    }
    apply Typ in H2. clear - H0 H2. destruct H2 as [qn [args [t [H2_1 H2_2]]]].
    inversion H2_2. subst.
    pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as Len.
    clear - H0 H11 H12 Len.
    unfold QName in H0.
    apply (f_equal (map (fun x => (fst x, fst (snd x))))) in H0.
    rewrite filter_ext with (g:=fun y => (fun x => match x with
    | ((tn, _), global q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
    | _ => false
    end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    2: { intros. destruct a0. simpl. destruct p3... }
    change
      (fun y : TypeName * Name * (ScopedName * expr) =>
        let (tn, _) := fst y in
        match fst (snd y) with
        | local _ => false
        | global q' => eq_TypeName tn (fst q) && eq_QName q q'
        end)
    with
      (fun y : TypeName * Name * (ScopedName * expr) => (fun x => match x with
        | ((tn, _), global q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
        | _ => false
        end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    rewrite filter_map in H0.
    rewrite map_map in H0. simpl in H0.
    assert (Unique.unique (map (fun x : ScopedName * expr => (a, fst x)) (snd a'))) as Uniq.
    { clear - H11 H12 Len. generalize H12. clear H12.
      assert (exists l, lookup_ctors (program_skeleton p) (fst (fst a')) = Some (l ++ ctorlist)).
      { exists []... }
      clear H11. generalize dependent ctorlist.
      change (list (ScopedName * expr)) with cfun_bod. generalize (snd a').
      induction c; intros.
      - apply Unique.Unique_nil.
      - simpl. apply Unique.Unique_cons.
        + clear - H H12 Len. destruct H as [l H].
          unfold lookup_ctors in H.
          destruct (filter (eq_TypeName (fst (fst a')))
            (skeleton_dts (program_skeleton p))); try discriminate.
          inversion H. clear H.
          pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
          unfold dts_ctor_names_unique in Uniq.
          apply (f_equal (map fst)) in H1.
          rewrite filter_ext with (g:=(fun y : ScopedName * list TypeName =>
             (fun x => eq_TypeName (fst (unscope x)) (fst (fst a')))
              (fst y))) in H1.
          2: { intros. destruct a1... }
          change (fun y => eq_TypeName (fst (unscope (fst y))) (fst (fst a')))
          with (fun y : ScopedName * list TypeName =>
                (fun x => eq_TypeName (fst (unscope x)) (fst (fst a')))
                (fst y)) in H1.
          rewrite filter_map in H1.
          pose proof (Unique.filter_unique _
            (fun x : ScopedName => eq_TypeName (fst (unscope x)) (fst (fst a'))) _ Uniq).
          rewrite H1 in H. clear - H12 H Len. rewrite map_app in H. apply app_unique_2 in H.
          inversion H; subst.
          * destruct ctorlist; simpl in H1; try discriminate.
          * destruct ctorlist; simpl in H0; try discriminate.
            inversion H0. subst. clear - H12 H1 Len. unfold not. intros. apply H1.
            inversion H12. subst. destruct a0. destruct p. subst. simpl in *.
            rewrite in_map_iff in H. destruct H as [x [H_1 H_2]].
            apply (in_map fst) in H_2. inversion H_1; subst.
            replace (map fst ctorlist) with (map fst c)...
            clear - H4 Len. generalize dependent ctorlist. induction c; intros.
            -- destruct ctorlist; try discriminate...
            -- destruct ctorlist; try discriminate. inversion H4. subst.
               destruct a. destruct p. simpl. f_equal...
        + destruct ctorlist.
          * apply IHc with (ctorlist:=[]); try inversion Len...
          * apply IHc with (ctorlist:=ctorlist); try inversion H12...
            destruct H as [l0 H]. exists (l0++[p0]). rewrite <- app_assoc...
    }
    eapply Unique.filter_unique in Uniq.
    unfold QName in *. rewrite H0 in Uniq.
    set (ml:=map (fun x : TypeName * Name * (ScopedName * expr) => (fst x, fst (snd x))) l0).
    pose proof (in_eq (fst p0, fst (snd p0)) ((fst p1, fst (snd p1)) :: ml)).
    pose proof (in_cons (fst p0, fst (snd p0)) _ _ (in_eq (fst p1, fst (snd p1)) ml)).
    unfold ml in *. pose proof H as Aux1. pose proof H1 as Aux2.
    rewrite <- H0 in Aux1. rewrite <- H0 in Aux2.
    rewrite filter_In in Aux1. rewrite filter_In in Aux2.
    inversion Uniq. subst. apply H4.
    assert (fst p0 = fst p1) as Eq1.
    { clear - Aux1 Aux2. destruct Aux1 as [Aux1 _]. destruct Aux2 as [Aux2 _].
      rewrite in_map_iff in Aux1. rewrite in_map_iff in Aux2.
      destruct Aux1 as [tmp1 [Aux1 _]]. destruct Aux2 as [tmp2 [Aux2 _]].
      inversion Aux1. inversion Aux2. subst...
    }
    assert (fst (snd p0) = fst (snd p1)) as Eq2.
    { destruct Aux1 as [_ Aux1]. destruct Aux2 as [_ Aux2]. clear - Aux1 Aux2.
      case_eq (fst (snd p0)); intros; rewrite H in Aux1; destruct (fst p0).
      - discriminate.
      - case_eq (fst (snd p1)); intros; rewrite H0 in Aux2; destruct (fst p1).
        + discriminate.
        + rewrite andb_true_iff in Aux1. destruct Aux1 as [_ Aux1].
          rewrite andb_true_iff in Aux2. destruct Aux2 as [_ Aux2].
          rewrite eq_QName_eq in Aux1. rewrite eq_QName_eq in Aux2. subst...
    }
    rewrite Eq1. rewrite Eq2. apply in_eq.
}
case_eq (filter (gfunbods_filterfun_g q) (map (fun y => (a, y)) (snd a'))); intros.
- apply (f_equal (length (A:=_))) in H1. rewrite H0 in H1. simpl in H1. discriminate.
- destruct l.
  + destruct p0. simpl. inversion H1. pose proof (in_eq (q0,p0) []).
    rewrite <- H3 in H2. rewrite filter_In in H2. destruct H2. rewrite in_map_iff in H2.
    destruct H2. inversion H2. inversion H5...
  + apply (f_equal (length (A:=_))) in H1. rewrite H0 in H1. simpl in H1. discriminate.
Qed.

Lemma cfunbods_g_cfunsigs : forall p (x0 : ScopedName * list TypeName),
  In x0 (skeleton_ctors (program_skeleton p)) ->
  is_global (fst x0) ->
  map (fun x : QName * (ScopedName * expr) => global (fst x))
      (filter (gfunbods_filterfun_g (unscope (fst x0)))
              (flat_map
                 (fun x : QName * list (ScopedName * expr) =>
                  map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                 (program_cfun_bods_g p)))
= map (fun x : QName * list TypeName * TypeName => global (fst (fst x)))
      (filter (fun x1 : TypeName * Name * list TypeName * TypeName =>
               eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
              (skeleton_cfun_sigs_g (program_skeleton p))).
Proof with auto.
intros p x0 x0In Glob. pose proof (program_has_all_cfun_bods_g p) as H.
unfold has_all_cfun_bods in H.
rewrite <- map_map with (f:=fst).
change (fun x : QName * list TypeName * TypeName => global (fst (fst x)))
  with (fun y : QName * list TypeName * TypeName => (fun x => global (fst x)) (fst y)).
repeat (rewrite <- map_map with (f:=fst)). f_equal.
remember (program_cfun_bods_g p) as l.
remember (skeleton_cfun_sigs_g (program_skeleton p)) as l2.
assert (exists l' l2', length l' = length l2' /\
  l' ++ l = program_cfun_bods_g p /\
  l2' ++ l2 = skeleton_cfun_sigs_g (program_skeleton p)).
{ exists []. exists []... }
rewrite Heql in H. rewrite Heql2 in H.
clear Heql. clear Heql2. generalize dependent l2.
induction l.
- induction l2... intros H0.
  destruct H0 as [l' [l2' [Len [H1 H2]]]].
  apply (f_equal (length (A:=_))) in H. repeat (rewrite map_length in H).
  rewrite app_nil_r in H1. rewrite <- H1 in H. rewrite <- H2 in H.
  unfold cfun_bod_named in *. rewrite Len in H. rewrite app_length in H.
  simpl in H. omega.
- induction l2. intros H0.
  + destruct H0 as [l' [l2' [Len [H1 H2]]]].
    apply (f_equal (length (A:=_))) in H. repeat (rewrite map_length in H).
    rewrite app_nil_r in H2. rewrite <- H1 in H. rewrite <- H2 in H.
    unfold cfun_sig in *. rewrite <- Len in H. rewrite app_length in H.
    simpl in H. omega.
  + simpl. rewrite filter_app. rewrite map_app.
    case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst a0)))); intros.
    * unfold QName in *. rewrite H0. simpl.
      match goal with
        [ |- ?t = fst (fst a0) :: ?t2] => change (fst (fst a0) :: t2) with ([fst (fst a0)] ++ t2)
      end.
      rewrite IHl with (l2:=l2).
      2: {
        destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]]. exists (l'++[a]). exists (l2'++[a0]).
        repeat (rewrite app_length). split...
        repeat (rewrite <- app_assoc). simpl. split...
      }
      unfold QName in *. f_equal.
      assert (fst (fst a0) = fst a).
      { destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]].
        apply (f_equal (map fst)) in H1_1. apply (f_equal (map (fun x => fst (fst x)))) in H1_2.
        unfold QName in *. rewrite H in H1_2. rewrite <- H1_1 in H1_2.
        clear - H1_2 Len. generalize dependent l2'. induction l'; intros.
        - destruct l2'; try discriminate. simpl in H1_2. inversion H1_2. rewrite H0...
        - destruct l2'; try discriminate. apply IHl' with (l2':=l2')...
          simpl in H1_2. inversion H1_2... }
      unfold cfun_bod in *. unfold QName in *. rewrite <- H2.
      assert (exists l' l, l' ++ a :: l = program_cfun_bods_g p).
      { destruct H1. destruct H1. destruct H1. destruct H1. destruct H3.
        exists x. exists l...
      }
      apply filter_gfunbods_filterfun_g_unique with (p:=p) (x0:=x0)...
    * unfold QName in *. rewrite H0.
      assert (filter (gfunbods_filterfun_g (unscope (fst x0)))
        (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = nil).
      { clear - H0 H H1. unfold gfunbods_filterfun_g. induction (snd a)...
        simpl. destruct a. simpl. destruct q. destruct a1. destruct s...
        destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]].
        assert (t = fst (fst (fst a0))).
        { clear IHc.
          apply (f_equal (map fst)) in H1_1. apply (f_equal (map (fun x => fst (fst x)))) in H1_2.
          unfold QName in *. rewrite H in H1_2. rewrite <- H1_1 in H1_2.
          clear - H1_2 Len. generalize dependent l2'. induction l'; intros.
          - destruct l2'; try discriminate. simpl in H1_2. inversion H1_2. rewrite H0...
          - destruct l2'; try discriminate. apply IHl' with (l2':=l2')...
            simpl in H1_2. inversion H1_2...
        }
        subst. rewrite eq_TypeName_symm in H0. unfold QName in *. rewrite H0. simpl...
      }
      unfold QName in *. unfold cfun_bod in *. rewrite H2. simpl.
      apply IHl.
      destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]]. exists (l'++[a]). exists (l2'++[a0]).
      repeat (rewrite app_length). split...
      repeat (rewrite <- app_assoc). simpl. split...
Qed.

Lemma cfunbods_l_cfunsigs : forall p (x0 : ScopedName * list TypeName),
  In x0 (skeleton_ctors (program_skeleton p)) ->
  is_global (fst x0) ->
  map (fun x : QName * (ScopedName * expr) => local (fst x))
      (filter (gfunbods_filterfun_g (unscope (fst x0)))
              (flat_map
                 (fun x : QName * list (ScopedName * expr) =>
                  map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                 (program_cfun_bods_l p)))
= map (fun x : QName * list TypeName * TypeName => local (fst (fst x)))
      (filter (fun x1 : TypeName * Name * list TypeName * TypeName =>
               eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
              (skeleton_cfun_sigs_l (program_skeleton p))).
Proof with auto.
intros p x0 x0In Glob. pose proof (program_has_all_cfun_bods_l p) as H.
unfold has_all_cfun_bods in H.
rewrite <- map_map with (f:=fst).
change (fun x : QName * list TypeName * TypeName => local (fst (fst x)))
  with (fun y : QName * list TypeName * TypeName => (fun x => local (fst x)) (fst y)).
repeat (rewrite <- map_map with (f:=fst)). f_equal.
remember (program_cfun_bods_l p) as l.
remember (skeleton_cfun_sigs_l (program_skeleton p)) as l2.
assert (exists l' l2', length l' = length l2' /\
  l' ++ l = program_cfun_bods_l p /\
  l2' ++ l2 = skeleton_cfun_sigs_l (program_skeleton p)).
{ exists []. exists []... }
rewrite Heql in H. rewrite Heql2 in H.
clear Heql. clear Heql2. generalize dependent l2.
induction l.
- induction l2... intros H0.
  destruct H0 as [l' [l2' [Len [H1 H2]]]].
  apply (f_equal (length (A:=_))) in H. repeat (rewrite map_length in H).
  rewrite app_nil_r in H1. rewrite <- H1 in H. rewrite <- H2 in H.
  unfold cfun_bod_named in *. rewrite Len in H. rewrite app_length in H.
  simpl in H. omega.
- induction l2. intros H0.
  + destruct H0 as [l' [l2' [Len [H1 H2]]]].
    apply (f_equal (length (A:=_))) in H. repeat (rewrite map_length in H).
    rewrite app_nil_r in H2. rewrite <- H1 in H. rewrite <- H2 in H.
    unfold cfun_sig in *. rewrite <- Len in H. rewrite app_length in H.
    simpl in H. omega.
  + simpl. rewrite filter_app. rewrite map_app.
    case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst a0)))); intros.
    * unfold QName in *. rewrite H0. simpl.
      match goal with
        [ |- ?t = fst (fst a0) :: ?t2] => change (fst (fst a0) :: t2) with ([fst (fst a0)] ++ t2)
      end.
      rewrite IHl with (l2:=l2).
      2: {
        destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]]. exists (l'++[a]). exists (l2'++[a0]).
        repeat (rewrite app_length). split...
        repeat (rewrite <- app_assoc). simpl. split...
      }
      unfold QName in *. f_equal.
      assert (fst (fst a0) = fst a).
      { destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]].
        apply (f_equal (map fst)) in H1_1. apply (f_equal (map (fun x => fst (fst x)))) in H1_2.
        unfold QName in *. rewrite H in H1_2. rewrite <- H1_1 in H1_2.
        clear - H1_2 Len. generalize dependent l2'. induction l'; intros.
        - destruct l2'; try discriminate. simpl in H1_2. inversion H1_2. rewrite H0...
        - destruct l2'; try discriminate. apply IHl' with (l2':=l2')...
          simpl in H1_2. inversion H1_2... }
      unfold cfun_bod in *. unfold QName in *. rewrite <- H2.
      assert (exists l' l, l' ++ a :: l = program_cfun_bods_l p).
      { destruct H1. destruct H1. destruct H1. destruct H1. destruct H3.
        exists x. exists l...
      }
      apply filter_gfunbods_filterfun_g_unique_l with (p:=p) (x0:=x0)...
    * unfold QName in *. rewrite H0.
      assert (filter (gfunbods_filterfun_g (unscope (fst x0)))
        (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = nil).
      { clear - H0 H H1. unfold gfunbods_filterfun_g. induction (snd a)...
        simpl. destruct a. simpl. destruct q. destruct a1. destruct s...
        destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]].
        assert (t = fst (fst (fst a0))).
        { clear IHc.
          apply (f_equal (map fst)) in H1_1. apply (f_equal (map (fun x => fst (fst x)))) in H1_2.
          unfold QName in *. rewrite H in H1_2. rewrite <- H1_1 in H1_2.
          clear - H1_2 Len. generalize dependent l2'. induction l'; intros.
          - destruct l2'; try discriminate. simpl in H1_2. inversion H1_2. rewrite H0...
          - destruct l2'; try discriminate. apply IHl' with (l2':=l2')...
            simpl in H1_2. inversion H1_2...
        }
        subst. rewrite eq_TypeName_symm in H0. unfold QName in *. rewrite H0. simpl...
      }
      unfold QName in *. unfold cfun_bod in *. rewrite H2. simpl.
      apply IHl.
      destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]]. exists (l'++[a]). exists (l2'++[a0]).
      repeat (rewrite app_length). split...
      repeat (rewrite <- app_assoc). simpl. split...
Qed.

Definition map_alternative_for_filter q d (x : cfun_bod_named) :=
  (fst x, from_some_default d
           (find (fun y =>
                  match fst y with
                  | global q' => eq_QName q q'
                  | _ => false
                  end) (snd x))).

Lemma cfun_bods_g_map_filter : forall p x0 (d : ScopedName * expr),
  In x0 (skeleton_ctors (program_skeleton p)) ->
  is_global (fst x0) ->
  filter (gfunbods_filterfun_g (unscope (fst x0)))
          (flat_map
            (fun x : QName * list (ScopedName * expr) =>
             map (fun y : ScopedName * expr => (fst x, y)) (snd x))
            (program_cfun_bods_g p)) =
  map (map_alternative_for_filter (unscope (fst x0)) d)
      (filter (fun x => eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
              (program_cfun_bods_g p)).
Proof with eauto.
intros. unfold map_alternative_for_filter.
assert (exists l', l' ++ program_cfun_bods_g p = program_cfun_bods_g p).
{ exists []... }
generalize H1. clear H1. generalize (program_cfun_bods_g p) at - 2.
induction c; intros... simpl.
case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst a))); intros.
- unfold QName in *. rewrite H2. simpl. rewrite filter_app.
  rewrite <- (app_nil_l (map _ (filter _ _))). rewrite app_comm_cons. f_equal.
  + rewrite combine_fst_snd. rewrite (combine_fst_snd (filter _ _)). f_equal.
    * destruct H1. eapply filter_gfunbods_filterfun_g_unique...
    * assert (exists a',
        filter (gfunbods_filterfun_g (unscope (fst x0)))
          (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = [a']).
      { case_eq (filter (gfunbods_filterfun_g (unscope (fst x0)))
         (map (fun y : ScopedName * expr => (fst a, y)) (snd a))); intros.
        - apply (f_equal (map fst)) in H3. destruct H1.
          erewrite filter_gfunbods_filterfun_g_unique in H3...
          simpl in H3. discriminate.
        - apply (f_equal (map fst)) in H3. destruct H1.
          erewrite filter_gfunbods_filterfun_g_unique in H3...
          destruct l; try discriminate. exists p0...
      }
      simpl. unfold cfun_bod in *. unfold QName in *. destruct H3. rewrite H3.
      generalize H3. clear.
      generalize ((@snd (prod TypeName Name) (list (prod ScopedName expr)) a)).
      induction l; intros; try discriminate. simpl. destruct a0. simpl.
      destruct s.
      -- simpl in IHl. apply IHl. simpl in H3. destruct a. simpl in H3.
         destruct q0...
      -- simpl in H3. case_eq (eq_QName (unscope (fst x0)) q); intros.
         ++ rewrite H in H3. destruct a. destruct q0. simpl in *.
            case_eq (eq_TypeName t (fst (unscope (fst x0)))); intros.
            ** rewrite H0 in H3. simpl in *. inversion H3...
            ** rewrite H0 in H3. simpl in H3.
               pose proof (in_eq x []). rewrite <- H3 in H1.
               rewrite filter_In in H1. destruct H1.
               unfold gfunbods_filterfun_g in H2. destruct x. destruct p.
               destruct p0. destruct s; try discriminate.
               rewrite in_map_iff in H1. do 2 (destruct H1). inversion H1.
               subst. rewrite andb_true_iff in H2. rewrite (proj1 H2) in H0.
               discriminate.
         ++ rewrite H in H3. destruct a. destruct q0. simpl in H3.
            rewrite andb_false_r in H3.
            pose proof (in_eq x []). rewrite <- H3 in H0.
            rewrite filter_In in H0. destruct H0.
            unfold gfunbods_filterfun_g in H1. destruct x. destruct p.
            destruct p0. destruct s; try discriminate.
            rewrite in_map_iff in H0. do 2 (destruct H0). inversion H0.
            subst. apply IHl...
  + apply IHc. destruct H1. exists (x++[a]). rewrite <- app_assoc...
- unfold QName in *. rewrite H2. rewrite filter_app.
  assert (filter (gfunbods_filterfun_g (unscope (fst x0)))
    (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = []).
  { clear - H2. induction (snd a)... simpl. destruct a. simpl.
    destruct q. destruct a0. destruct s... simpl in H2.
    rewrite eq_TypeName_symm in H2. rewrite H2... }
  unfold QName in *. unfold cfun_bod in *. rewrite H3. apply IHc.
  destruct H1. exists (x++[a]). rewrite <- app_assoc...
Qed.

Lemma cfun_bods_l_map_filter : forall p x0 (d : ScopedName * expr),
  In x0 (skeleton_ctors (program_skeleton p)) ->
  is_global (fst x0) ->
  filter (gfunbods_filterfun_g (unscope (fst x0)))
          (flat_map
            (fun x : QName * list (ScopedName * expr) =>
             map (fun y : ScopedName * expr => (fst x, y)) (snd x))
            (program_cfun_bods_l p)) =
  map (map_alternative_for_filter (unscope (fst x0)) d)
      (filter (fun x => eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
              (program_cfun_bods_l p)).
Proof with eauto.
intros. unfold map_alternative_for_filter.
assert (exists l', l' ++ program_cfun_bods_l p = program_cfun_bods_l p).
{ exists []... }
generalize H1. clear H1. generalize (program_cfun_bods_l p) at - 2.
induction c; intros... simpl.
case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst a))); intros.
- unfold QName in *. rewrite H2. simpl. rewrite filter_app.
  rewrite <- (app_nil_l (map _ (filter _ _))). rewrite app_comm_cons. f_equal.
  + rewrite combine_fst_snd. rewrite (combine_fst_snd (filter _ _)). f_equal.
    * destruct H1. eapply filter_gfunbods_filterfun_g_unique_l...
    * assert (exists a',
        filter (gfunbods_filterfun_g (unscope (fst x0)))
          (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = [a']).
      { case_eq (filter (gfunbods_filterfun_g (unscope (fst x0)))
         (map (fun y : ScopedName * expr => (fst a, y)) (snd a))); intros.
        - apply (f_equal (map fst)) in H3. destruct H1.
          erewrite filter_gfunbods_filterfun_g_unique_l in H3...
          simpl in H3. discriminate.
        - apply (f_equal (map fst)) in H3. destruct H1.
          erewrite filter_gfunbods_filterfun_g_unique_l in H3...
          destruct l; try discriminate. exists p0...
      }
      simpl. unfold cfun_bod in *. unfold QName in *. destruct H3. rewrite H3.
      generalize H3. clear.
      generalize ((@snd (prod TypeName Name) (list (prod ScopedName expr)) a)).
      induction l; intros; try discriminate. simpl. destruct a0. simpl.
      destruct s.
      -- simpl in IHl. apply IHl. simpl in H3. destruct a. simpl in H3.
         destruct q0...
      -- simpl in H3. case_eq (eq_QName (unscope (fst x0)) q); intros.
         ++ rewrite H in H3. destruct a. destruct q0. simpl in *.
            case_eq (eq_TypeName t (fst (unscope (fst x0)))); intros.
            ** rewrite H0 in H3. simpl in *. inversion H3...
            ** rewrite H0 in H3. simpl in H3.
               pose proof (in_eq x []). rewrite <- H3 in H1.
               rewrite filter_In in H1. destruct H1.
               unfold gfunbods_filterfun_g in H2. destruct x. destruct p.
               destruct p0. destruct s; try discriminate.
               rewrite in_map_iff in H1. do 2 (destruct H1). inversion H1.
               subst. rewrite andb_true_iff in H2. rewrite (proj1 H2) in H0.
               discriminate.
         ++ rewrite H in H3. destruct a. destruct q0. simpl in H3.
            rewrite andb_false_r in H3.
            pose proof (in_eq x []). rewrite <- H3 in H0.
            rewrite filter_In in H0. destruct H0.
            unfold gfunbods_filterfun_g in H1. destruct x. destruct p.
            destruct p0. destruct s; try discriminate.
            rewrite in_map_iff in H0. do 2 (destruct H0). inversion H0.
            subst. apply IHl...
  + apply IHc. destruct H1. exists (x++[a]). rewrite <- app_assoc...
- unfold QName in *. rewrite H2. rewrite filter_app.
  assert (filter (gfunbods_filterfun_g (unscope (fst x0)))
    (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = []).
  { clear - H2. induction (snd a)... simpl. destruct a. simpl.
    destruct q. destruct a0. destruct s... simpl in H2.
    rewrite eq_TypeName_symm in H2. rewrite H2... }
  unfold QName in *. unfold cfun_bod in *. rewrite H3. apply IHc.
  destruct H1. exists (x++[a]). rewrite <- app_assoc...
Qed.

Lemma lookup_cfun_nth : forall p tn sig n m1 d' d_a
  (x0 : ScopedName * list TypeName) (d_l0 :  QName * list TypeName * TypeName),
In x0 (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))) ->
m1 = globalize_aux
        (filter (gfunbods_filterfun_g (unscope (fst x0)))
           (flat_map
              (fun x : QName * list (ScopedName * expr) =>
               map (fun y : ScopedName * expr => (fst x, y)) (snd x))
              (program_cfun_bods_g p))) ->
n < length (filter (fun x : TypeName * Name * list (ScopedName * expr) =>
                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                    (program_cfun_bods_g p)) ->
lookup_cfun_sig_scoped (program_skeleton p)
  (fst (nth n m1
            (global (fst (map_alternative_for_filter (unscope (fst x0)) d' d_a)),
             snd (map_alternative_for_filter (unscope (fst x0)) d' d_a)))) = Some sig ->
nth n
  (filter
     (fun x1 : TypeName * Name * list TypeName * TypeName =>
      eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
     (skeleton_cfun_sigs_g (program_skeleton p) ++
      skeleton_cfun_sigs_l (program_skeleton p))) d_l0 = sig.
Proof with auto.
intros p tn sig n m1 d' d_a x0 d_l0 x0In H H0 H1. subst m1. unfold map_alternative_for_filter in H1. simpl in H1.
unfold globalize_aux in H1. rewrite <- map_nth in H1. simpl in H1.
rewrite map_map in H1. simpl in H1. unfold lookup_cfun_sig_scoped in H1.
rewrite <- map_map in H1. rewrite map_nth in H1. unfold lookup_cfun_sig_g in H1.
unfold lookup_cfun_sig_x in H1. rewrite filter_app.
pose proof (program_has_all_cfun_bods_g p) as Zip.
unfold has_all_cfun_bods in Zip.
assert (n < length
 (filter (fun x1 : TypeName * Name * list TypeName * TypeName =>
          eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
 (skeleton_cfun_sigs_g (program_skeleton p)))) as Len.
{ rewrite <- map_length with (f:=fun x : TypeName * Name * list TypeName * TypeName => fst (fst (fst x))).
  erewrite filter_ext.
  - rewrite filter_map. rewrite <- map_map. rewrite <- filter_map. rewrite map_length.
    unfold gfun_bod_named in *. unfold gfun_bod in *. unfold QName in *. rewrite Zip.
    rewrite <- filter_map. rewrite map_length. apply H0.
  - intros...
}
rewrite app_nth1... apply find_some in H1. destruct H1.
rewrite filter_In in x0In. destruct x0In.
unfold gfunsigs_filterfun_g in H3. destruct x0. destruct s; try discriminate.
pose proof (cfunbods_g_cfunsigs p (global q, l) H2 (Is_global_global _)) as Aux.
simpl in *. rewrite <- map_map in Aux.
change (fun x : QName * list TypeName * TypeName => global (fst (fst x)))
  with (fun y : QName * list TypeName * TypeName => (fun x => global (fst x)) (fst y)) in Aux.
rewrite <- (map_map fst) in Aux. rewrite <- (map_map fst) in Aux.
assert (forall l l', map global l = map global l' -> l = l') as Aux2.
{ clear. induction l; intros.
  - destruct l'... inversion H.
  - destruct l'; inversion H. f_equal...
}
apply Aux2 in Aux. rewrite Aux in H1. evar (d_ts : list TypeName). evar (d_t : TypeName).
replace (fst d_a) with ((fun x => fst (fst x)) (fst d_a, d_ts, d_t)) in H1...
rewrite map_map in H1.
change (fst (fst (fst d_a, d_ts, d_t))) with ((fun x => fst (fst x)) (fst d_a, d_ts, d_t)) in H1.
rewrite map_nth in H1. rewrite nth_indep with (d':=d_l0) in H1...
clear - H H1 Len. pose proof (nth_In _ d_l0 Len).
assert (In sig (filter (fun x : TypeName * Name * list TypeName * TypeName =>
                        eq_TypeName (fst q) (fst (fst (fst x))))
                       (skeleton_cfun_sigs_g (program_skeleton p)))) as sigIn.
{ clear - H H1 H0. rewrite filter_In. split...
  rewrite eq_QName_eq in H1. unfold QName in *. rewrite <- H1.
  rewrite filter_In in H0. destruct H0...
}
clear Len. pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
unfold gfun_sigs_names_unique in Uniq.
set (flt:=fun x1 : TypeName * Name => eq_TypeName (fst q) (fst x1)).
apply Unique.filter_unique with (f:=flt) in Uniq. rewrite <- filter_map in Uniq.
rewrite eq_QName_eq in H1.
generalize sigIn H1 H H0 Uniq. clear. generalize (skeleton_cfun_sigs_g (program_skeleton p)).
intros. unfold flt in *. unfold QName in *.
set (flt':=fun x1 : TypeName * Name * list TypeName * TypeName => eq_TypeName (fst q) (fst (fst (fst x1)))) in *.
unfold cfun_sig in *. unfold QName in *. generalize dependent (filter flt' c). clear.
intros. generalize dependent (nth n l d_l0). intros. generalize dependent p.
induction l; intros; [inversion sigIn |].
simpl in Uniq. inversion Uniq; subst. destruct H0.
- destruct sigIn; subst... exfalso. apply H3. apply in_map with (f:=fun x => fst (fst x)) in H0. rewrite H1...
- destruct sigIn; subst... exfalso. apply H3. apply in_map with (f:=fun x => fst (fst x)) in H. rewrite <- H1...
Unshelve. all:eauto.
Qed.

Lemma lookup_cfun_nth_l : forall p tn sig n m1 d' d_a
  (x0 : ScopedName * list TypeName) (d_l0 :  QName * list TypeName * TypeName),
In x0 (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))) ->
m1 = localize_aux
        (filter (gfunbods_filterfun_g (unscope (fst x0)))
           (flat_map
              (fun x : QName * list (ScopedName * expr) =>
               map (fun y : ScopedName * expr => (fst x, y)) (snd x))
              (program_cfun_bods_l p))) ->
n >= length (filter (fun x : TypeName * Name * list (ScopedName * expr) =>
                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                    (program_cfun_bods_g p)) ->
n - length (filter (gfunbods_filterfun_g (unscope (fst x0)))
                   (flat_map (fun x : QName * list (ScopedName * expr) =>
                      map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                          (program_cfun_bods_g p))) <
 length (filter (fun x : TypeName * Name * list (ScopedName * expr) =>
                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                    (program_cfun_bods_l p))  ->
lookup_cfun_sig_scoped (program_skeleton p)
  (fst (nth (n - length
                        (map
                           (fun x : QName * (ScopedName * expr) =>
                            switch_indices_aux (program_skeleton p)
                              (fst (global (fst x), snd x)) (length (snd x0)) tn
                              (snd (snd (global (fst x), snd x))))
                           (filter (gfunbods_filterfun_g (unscope (fst x0)))
                              (flat_map
                                 (fun x : QName * list (ScopedName * expr) =>
                                  map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                                 (program_cfun_bods_g p))))) m1
            (local (fst (map_alternative_for_filter (unscope (fst x0)) d' d_a)),
             snd (map_alternative_for_filter (unscope (fst x0)) d' d_a)))) = Some sig ->
nth n
  (filter
     (fun x1 : TypeName * Name * list TypeName * TypeName =>
      eq_TypeName (fst (unscope (fst  x0))) (fst (fst (fst x1))))
     (skeleton_cfun_sigs_g (program_skeleton p) ++
      skeleton_cfun_sigs_l (program_skeleton p))) d_l0 = sig.
Proof with auto.
intros p tn sig n m1 d' d_a x0 d_l0 x0In H H0 H0' H1. subst m1. unfold map_alternative_for_filter in H1. simpl in H1.
unfold localize_aux in H1. rewrite <- map_nth in H1. simpl in H1.
rewrite map_map in H1. simpl in H1. unfold lookup_cfun_sig_scoped in H1.
rewrite <- map_map in H1. rewrite map_nth in H1. unfold lookup_cfun_sig_l in H1.
unfold lookup_cfun_sig_x in H1. rewrite filter_app.
pose proof (program_has_all_cfun_bods_g p) as Zip.
unfold has_all_cfun_bods in Zip.
assert (n >= length
 (filter (fun x1 : TypeName * Name * list TypeName * TypeName =>
          eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
 (skeleton_cfun_sigs_g (program_skeleton p)))) as Len.
{ rewrite <- map_length with (f:=fun x : TypeName * Name * list TypeName * TypeName => fst (fst (fst x))).
  erewrite filter_ext.
  - rewrite filter_map. rewrite <- map_map. rewrite <- filter_map. rewrite map_length.
    unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite Zip.
    rewrite <- filter_map. rewrite map_length. apply H0.
  - intros...
}
rewrite app_nth2... apply find_some in H1. destruct H1.
rewrite filter_In in x0In. destruct x0In.
unfold gfunsigs_filterfun_g in H3. destruct x0. destruct s; try discriminate.
pose proof (cfunbods_l_cfunsigs p (global q, l) H2 (Is_global_global _)) as Aux.
simpl in *. rewrite <- map_map in Aux.
change (fun x : QName * list TypeName * TypeName => local (fst (fst x)))
  with (fun y : QName * list TypeName * TypeName => (fun x => local (fst x)) (fst y)) in Aux.
rewrite <- (map_map fst) in Aux. rewrite <- (map_map fst) in Aux.
assert (forall l l', map local l = map local l' -> l = l') as Aux2.
{ clear. induction l; intros.
  - destruct l'... inversion H.
  - destruct l'; inversion H. f_equal...
}
apply Aux2 in Aux. rewrite Aux in H1. evar (d_ts : list TypeName). evar (d_t :  TypeName).
replace (fst d_a) with (fst (fst (fst d_a, d_ts, d_t))) in H1...
repeat (rewrite map_nth in H1). clear Len.
assert (Len : n -
  length
    (map
       (fun x : QName * (ScopedName * expr) =>
        switch_indices_aux (program_skeleton p) (global (fst x)) (length l) tn (snd (snd x)))
       (filter (gfunbods_filterfun_g q)
         (flat_map
             (fun x : QName * list (ScopedName * expr) =>
              map (fun y : ScopedName * expr => (fst x, y)) (snd x))
             (program_cfun_bods_g p)))) <
  length
    (filter (fun x1 : TypeName * Name * list TypeName * TypeName => eq_TypeName (fst q) (fst (fst (fst x1))))
       (skeleton_cfun_sigs_l (program_skeleton p)))).
{ change q with (unscope (fst (global q, l))).
  erewrite cfun_bods_g_map_filter; try apply Is_global_global...
  repeat (rewrite map_length). rewrite <- sigs_bods_g_length.
  change q with (unscope (fst (global q, l))) in H0'.
  erewrite cfun_bods_g_map_filter in H0'; try apply Is_global_global...
  rewrite map_length in H0'.
  change q with (unscope (fst (global q, l))) in H0'.
  rewrite <- sigs_bods_g_length in H0'. rewrite <- sigs_bods_l_length in H0'...
}
rewrite nth_indep with (d':=d_l0) in H1...
clear - H H1 Len H2. pose proof (nth_In _ d_l0 Len).
assert (In sig (filter (fun x : TypeName * Name * list TypeName * TypeName =>
                        eq_TypeName (fst q) (fst (fst (fst x))))
                       (skeleton_cfun_sigs_l (program_skeleton p)))) as sigIn.
{ clear - H H1 H0. rewrite filter_In. split...
  rewrite eq_QName_eq in H1. unfold QName in *. rewrite <- H1.
  rewrite filter_In in H0. destruct H0...
}
clear Len. pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
unfold cfun_sigs_names_unique in Uniq.
set (flt:=fun x1 : TypeName * Name => eq_TypeName (fst q) (fst x1)).
apply Unique.filter_unique with (f:=flt) in Uniq. rewrite <- filter_map in Uniq.
rewrite eq_QName_eq in H1.
change q with (unscope (fst (global q, l))) in H1.
erewrite cfun_bods_g_map_filter in H1; try apply Is_global_global...  simpl in H1.
change q with (unscope (fst (global q, l))) in H0.
erewrite cfun_bods_g_map_filter in H0; try apply Is_global_global... simpl in H0.
repeat (rewrite map_length in H1). repeat (rewrite map_length in H0).
change q with (unscope (fst (global q, l))) in H1.
rewrite <- sigs_bods_g_length in H1. simpl in H1.
change q with (unscope (fst (global q, l))) in H0.
rewrite <- sigs_bods_g_length in H0. simpl in H0.
generalize sigIn H1 H H0 Uniq. clear. generalize (skeleton_cfun_sigs_l (program_skeleton p)).
intros. unfold flt in *. unfold QName in *.
set (flt':=fun x1 : TypeName * Name * list TypeName * TypeName => eq_TypeName (fst q) (fst (fst (fst x1)))) in *.
unfold cfun_sig in *. unfold QName in *. generalize dependent (filter flt' c). clear.
intros.
generalize dependent (nth (n - length (filter flt' (skeleton_cfun_sigs_g (program_skeleton p)))) l d_l0).
intros. generalize dependent p0.
induction l; intros; [inversion sigIn |].
simpl in Uniq. inversion Uniq; subst. destruct H0.
- destruct sigIn; subst... exfalso. apply H3. apply in_map with (f:=fun x => fst (fst x)) in H0. rewrite H1...
- destruct sigIn; subst... exfalso. apply H3. apply in_map with (f:=fun x => fst (fst x)) in H. rewrite <- H1...
Unshelve. all:eauto.
+ split; try exact (global q). exact (E_Var 0).
+ split; try exact (global q). exact (E_Var 0).
Qed.


Lemma new_gfunbods_g_typecheck_aux:
  forall (p : program) (tn : TypeName)
         (x0 : ScopedName * list TypeName),
    (forall x : expr,
              In x (map snd (flat_map snd (program_cfun_bods_g p))) ->
              no_matches tn x) ->
    (forall x : expr,
              In x (map snd (flat_map snd (program_cfun_bods_l p))) ->
              no_matches tn x) ->
    In x0
       (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))) ->
    forall (es : list expr) (ctxts : list (list TypeName)),
      es = map snd
        (map
           (fun x : ScopedName * (ScopedName * expr) =>
            (fst x,
            switch_indices_aux (program_skeleton p)
              (fst x) (length (snd x0)) tn
              (snd (snd x))))
           (globalize_aux
              (filter (gfunbods_filterfun_g (unscope (fst x0)))
                 (flat_map
                    (fun x : QName * list (ScopedName * expr) =>
                     map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                    (program_cfun_bods_g p)))) ++
         map
           (fun x : ScopedName * (ScopedName * expr) =>
            (fst x,
            switch_indices_aux (program_skeleton p)
              (fst x) (length (snd x0)) tn
              (snd (snd x))))
           (localize_aux
              (filter (gfunbods_filterfun_g (unscope (fst x0)))
                 (flat_map
                    (fun x : QName * list (ScopedName * expr) =>
                     map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                    (program_cfun_bods_l p))))) ->
      ctxts = map
           (fun dtor : ScopedName * list TypeName * TypeName =>
            snd (fst dtor) ++ snd x0)
           (map (fun x : QName * list TypeName * TypeName => (global (fst (fst x)), snd (fst x), snd x))
              (filter
                 (fun x1 : TypeName * Name * list TypeName * TypeName =>
                  eq_TypeName (fst (unscope (fst x0)))
                    (fst (fst (fst x1))))
                 (skeleton_cfun_sigs_g (program_skeleton p))) ++
            map (fun x : QName * list TypeName * TypeName => (local (fst (fst x)), snd (fst x), snd x))
              (filter
                 (fun x1 : TypeName * Name * list TypeName * TypeName =>
                  eq_TypeName (fst (unscope (fst x0)))
                    (fst (fst (fst x1))))
                 (skeleton_cfun_sigs_l (program_skeleton p)))) ->
      length ctxts = length es ->
      forall ts : list TypeName,
        ts = map snd
          (map
             (fun x : QName * list TypeName * TypeName =>
              (global (fst (fst x)), snd (fst x), snd x))
             (filter
                (fun x1 : TypeName * Name * list TypeName * TypeName =>
                 eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
                (skeleton_cfun_sigs_g (program_skeleton p))) ++
           map
             (fun x : QName * list TypeName * TypeName =>
              (local (fst (fst x)), snd (fst x), snd x))
             (filter
                (fun x1 : TypeName * Name * list TypeName * TypeName =>
                 eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
                (skeleton_cfun_sigs_l (program_skeleton p)))) ->
        length es = length ts ->
        (exists (l : list (list TypeName)) (l' : list expr)
                (l'' : list TypeName),
            length l = length l' /\
            length l' = length l'' /\
            l ++ ctxts = ctxts /\ l' ++ es = es /\ l'' ++ ts = ts) ->
        forall (a : expr) (es0 : list expr),
          (forall (ts0 : list TypeName) (ctxts0 : list (list TypeName)),
              (exists (l : list (list TypeName)) (l' : list expr)
                      (l'' : list TypeName),
                  length l = length l' /\
                  length l' = length l'' /\
                  l ++ ctxts0 = ctxts /\ l' ++ es0 = es /\ l'' ++ ts0 = ts) ->
              refunctionalize_to_skeleton p tn /// ctxts0 |||- es0 ::: ts0) ->
          forall (ts0 : list TypeName) (ctxts0 l : list (list TypeName))
                 (l' : list expr) (l'' : list TypeName),
            length l = length l' ->
            length l' = length l'' ->
            l ++ ctxts0 = ctxts ->
            l' ++ a :: es0 =
            map
              (fun x : ScopedName * (ScopedName * expr) =>
                 switch_indices_aux (program_skeleton p) (fst x)
                                    (length (snd x0)) tn (snd (snd x)))
              (globalize_aux
                 (filter (gfunbods_filterfun_g (unscope (fst x0)))
                         (flat_map
                            (fun x : QName * list (ScopedName * expr) =>
                               map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                            (program_cfun_bods_g p))) ++
                 localize_aux
                 (filter (gfunbods_filterfun_g (unscope (fst x0)))
                         (flat_map
                            (fun x : QName * list (ScopedName * expr) =>
                               map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                            (program_cfun_bods_l p)))) ->
            l'' ++ ts0 = ts ->
            forall (l0 : list TypeName) (l1 : list (list TypeName)),
              ctxts0 = l0 :: l1 ->
              forall (t : TypeName) (l2 : list TypeName),
                ts0 = t :: l2 ->
                refunctionalize_to_skeleton p tn / l0 |- a : t.
Proof with eauto.
  intros p tn x0 NoMatch_g NoMatch_l H6 es ctxts Heseq Hctxtseq Len1 ts Htseq Len2 H a es0 IHes0 ts0 ctxts0
    l l' l'' Len'1 Len'2 lEq l'Eq l''Eq l0 l1 H0 t l2 H1.
  set (Len:=length l' <?
                 length
                   (filter
                      (fun x : TypeName * Name * list (ScopedName * expr) =>
                         eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                      (program_cfun_bods_g p))).
                  match goal with [l'Eq : l' ++ a :: es0 = map _ (?m1' ++ ?m2') |- _] =>
                    set (m1 := m1') in *; set (m2:= m2') in * end.
                  evar (d_a : cfun_bod_named). evar (d' : (ScopedName * expr)%type).
                  set (fn := (fun y : ScopedName * (ScopedName * expr) =>
                    switch_indices_aux (program_skeleton p) (fst y) (length (snd x0)) tn (snd (snd y)))).
                  set (global_local:=if Len then global else local).
                  set (length_length:=if Len then length l' else
                    length l' - length (map
                     (fun x : QName * (ScopedName * expr) =>
                      switch_indices_aux (program_skeleton p)
                        (fst (global (fst x), snd x)) (length (snd x0)) tn
                        (snd (snd (global (fst x), snd x))))
                      (filter (gfunbods_filterfun_g (unscope (fst x0)))
                        (flat_map
                          (fun x : QName * list (ScopedName * expr) =>
                           map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                        (program_cfun_bods_g p))))).
                  set (m1_m2:=if Len then m1 else m2).
                  assert (aEq : a = nth length_length
                    (map (fun x => switch_indices_aux (program_skeleton p) (fst x) (length (snd x0))
                           tn (snd (snd x))) m1_m2)
                    (fn
                     ((fun x => (global_local (fst x), snd x))
                      (map_alternative_for_filter (unscope (fst x0)) d' d_a)))).
                  { evar (d'' : expr). apply (f_equal (fun x => nth (length l') x d'')) in l'Eq.
                    rewrite app_nth2 in l'Eq... rewrite Nat.sub_diag in l'Eq. simpl in l'Eq.
                    rewrite l'Eq. unfold fn. unfold d''. unfold d''.
                    case_eq Len; intros.
                    - unfold Len in *. unfold length_length.
                      unfold m1_m2. unfold m1. unfold globalize_aux. unfold localize_aux.
                      rewrite H2. rewrite map_app. rewrite map_map.
                      rewrite app_nth1... rewrite map_length. apply Nat.ltb_lt.
                      erewrite cfun_bods_g_map_filter; try rewrite map_length...
                      * rewrite filter_In in H6. destruct H6...
                      * rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                        destruct x0. destruct s; try discriminate.
                        apply Is_global_global.
                    - unfold Len in *. unfold length_length.
                      unfold m1_m2. unfold m1. unfold m2. unfold globalize_aux. unfold localize_aux.
                      rewrite H2. rewrite map_app. rewrite map_map.
                      rewrite app_nth2... rewrite map_length. apply Nat.ltb_ge.
                      erewrite cfun_bods_g_map_filter; try rewrite map_length...
                      * rewrite filter_In in H6. destruct H6...
                      * rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                        destruct x0. destruct s; try discriminate.
                        apply Is_global_global.
                  }
                  rewrite aEq. rewrite map_nth.
                  unfold switch_indices_aux.
                  match goal with [|- (_ / _ |- (refunctionalize_expr tn (proj1_sig ?s)) : _)] =>
                    set (switch' := s)
                  end.
                  destruct switch' as [switch Switch] eqn:switchEq. simpl.
                  apply refunctionalize_expr_preserves_typing.
                  +++ clear - switchEq.
                      replace switch with (proj1_sig switch').
                      2: { rewrite switchEq... }
                      match goal with
                      | [|- ?goal] => replace goal with (no_matches tn (proj1_sig switch'))
                      end...
                      apply switch_indices_no_match.
                      assert (forall x : expr,
                        In x ((map snd (flat_map snd (program_cfun_bods_g p ++ program_cfun_bods_l p)))) ->
                        no_matches tn x) as NoMatch.
                      { rewrite flat_map_concat_map. rewrite map_app. rewrite concat_app.
                        rewrite map_app. intros. repeat (rewrite <- flat_map_concat_map in H2).
                        apply in_app_or in H2. destruct H2; [apply NoMatch_g | apply NoMatch_l]...
                      }
                      apply NoMatch.
                      rewrite in_map_iff. eexists. apply and_comm.
                      rewrite in_flat_map. evar (d : (QName * list (ScopedName * expr))%type).
                      set (cfun_bods_g_l := program_cfun_bods_g p ++ program_cfun_bods_l p).
                      split.
                      *** exists (nth (length l') (filter
                           (fun x : TypeName * Name * cfun_bod =>
                            eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                           cfun_bods_g_l) d).
                          split.
                          ---- eapply proj1. rewrite <- filter_In. unfold length_length. unfold cfun_bods_g_l.
                               do 2 rewrite filter_app. case_eq Len; intros; unfold Len in *.
                               ++++ apply nth_In. rewrite Nat.ltb_lt in H2. rewrite app_length.
                                    unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. omega.
                               ++++ apply nth_In. apply (f_equal (@length _)) in Hctxtseq.
                                    rewrite map_length in Hctxtseq. rewrite app_length in Hctxtseq.
                                    repeat (rewrite map_length in Hctxtseq). rewrite <- app_length in Hctxtseq.
                                    apply (f_equal (@length _)) in lEq. rewrite Hctxtseq in lEq. rewrite H0 in lEq.
                                    rewrite <- Len'1. clear - lEq. rewrite app_length in lEq at 1. simpl in lEq.
                                    rewrite app_length in *.
                                    rewrite <- sigs_bods_g_length. rewrite <- sigs_bods_l_length.
                                    unfold QName in *. rewrite <- lEq. omega.
                          ---- shelve.
                      *** eauto. Unshelve. all:eauto. 3:{
                          unfold length_length in *. unfold m1_m2 in *.
                          unfold global_local in *. unfold cfun_bods_g_l in *.
                          case_eq Len; intros.
                          1:{
                          assert (Tmp2 : nth (length l')
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_g p ++ program_cfun_bods_l p)) d
                            = nth (length l')
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_g p)) d).
                          { rewrite filter_app. rewrite app_nth1... apply Nat.ltb_lt... }
                          rewrite Tmp2. unfold Len in *. clear Len. rename H2 into Len.
                          unfold m1. rewrite filter_In in H6. destruct H6.
                          unfold gfunsigs_filterfun_g in e. destruct x0. destruct s; try discriminate.
                          rewrite cfun_bods_g_map_filter with (d:=d'); try apply Is_global_global...
                          unfold globalize_aux. repeat (rewrite map_map). simpl.
                          match goal with [|- In (_ (_ _ (_ ?fn' _) ?dd')) _] =>
                            set (fn:=fn'); set (dd:=dd') end.
                          replace dd with (fn d_a)... rewrite map_nth.
                          unfold fn. simpl.
                          assert (forall {A} l f d (x : A), find f l = Some x ->
                            In (from_some_default d (find f l)) l).
                          { clear. intros. induction l; try discriminate.
                            simpl. destruct (f a) eqn:fEq; [left|]...
                            right. apply IHl. simpl in H. rewrite fEq in H...
                          }
                          rewrite Nat.ltb_lt in Len. rewrite nth_indep with (d':=d)...
                          match goal with [|- In (_ _ (_ ?f _)) ?l] => case_eq (find f l); intros end;
                           [apply H2 with (x:=p0)|]... exfalso.
                          pose proof (program_cfun_bods_typecheck_g p) as Typ.
                          unfold cfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
                          assert (In (nth (length l')
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst q) (fst (fst x)))
                              (program_cfun_bods_g p)) d) (program_cfun_bods_g p)).
                          { eapply proj1. rewrite <- filter_In. apply nth_In... }
                          apply Typ in H4. do 4 (destruct H4). inversion H5; subst.
                          apply listTypeDeriv'_lemma_ctx in H19. do 2 (rewrite map_length in H19).
                          rewrite Nat.eqb_eq in H19. clear - (**)Len(**) H3 H17 H18 H19. unfold lookup_ctors in H17.
                          match goal with
                          | _ : match ?dstr with _ => _ end = _ |- _ => destruct dstr
                          end; try discriminate. inversion H17; subst. clear H17.
                          rewrite Forall_forall in H18. evar (d_c : (ScopedName * list TypeName)%type).
                          pose proof (conj i e) as FilterAux.
                          change (eq_TypeName tn (fst q)) with
                           ((fun x => eq_TypeName tn (fst (unscope (fst x)))) (global q, l3))
                           in FilterAux.
                          rewrite <- filter_In in FilterAux.
                          apply In_nth with (d:=d_c) in FilterAux. destruct FilterAux as [n [nEq nthEq]].
                          evar (d_e : (ScopedName * expr)%type). set (nth_e := nth n
                            (snd (nth (length l')  (filter
                              (fun x0 : TypeName * Name * cfun_bod =>
                               eq_TypeName tn (fst (fst x0))) (program_cfun_bods_g p)) d)) d_e).
                          apply find_none with (x:=(global q, snd nth_e)) in H3;
                            [simpl in H3; rewrite eq_QName_refl in H3; discriminate|].
                          apply (f_equal fst) in nthEq. simpl in nthEq.
                          rewrite <- nthEq.
                          assert (fst (nth n (filter
                            (fun x : ScopedName * list TypeName =>
                             eq_TypeName tn (fst (unscope (fst x))))
                            (skeleton_ctors (program_skeleton p))) d_c) = fst nth_e).
                          { unfold nth_e. symmetry.
                            rewrite eq_TypeName_eq in e. subst tn.
                            match goal with [|- fst (_ _ ?lhs _) = fst (_ _ ?rhs _)] =>
                              specialize H18 with (x:=(nth n lhs d_e, nth n rhs d_c));
                              set (LenAux':=length lhs=length rhs)
                            end.
                            assert LenAux' as LenAux.
                            { unfold LenAux'. clear LenAux'. unfold QName in *. unfold cfun_bod in *.
                              rewrite <- H19. f_equal. apply filter_ext. intros. destruct a0.
                              match goal with [|- _ _ (_ (_ (_ _ ?fltrd' _))) = _] => set (fltrd:=fltrd') end.
                              assert (In (nth (length l') fltrd d) fltrd).
                              { apply nth_In. simpl in Len. unfold fltrd... }
                              unfold fltrd in H0. rewrite filter_In in H0. destruct H0.
                              symmetry. unfold fltrd. rewrite eq_TypeName_eq in H1. rewrite <- H1.
                              apply eq_TypeName_symm.
                            }
                            rewrite <- combine_nth in H18...
                            match goal with [_ : In ?x (combine ?l1 ?l2) -> _ |- _] =>
                              set (H' := In x (combine l1 l2)) end.
                            assert H'. { unfold H'. clear H'.
                            match goal with [|- In (_ _ (_ (_ (_ _ ?fltrd' _)) _) _) _] => set (fltrd:=fltrd') end.
                            assert (In (nth (length l') fltrd d) fltrd).
                            { apply nth_In. simpl in Len. unfold fltrd... }
                            erewrite filter_ext with (f:=fun x : ScopedName * list TypeName
                              => let (n0, _) := x in eq_TypeName _ _).
                            - apply nth_In. unfold fltrd in *.
                              rewrite combine_length. rewrite <- H19. erewrite filter_ext.
                              + rewrite Nat.min_id...
                              + intros. destruct a0. rewrite eq_TypeName_symm. f_equal.
                                rewrite filter_In in H0. destruct H0. symmetry. apply eq_TypeName_eq...
                            - intros. destruct a0. rewrite eq_TypeName_symm. f_equal.
                              unfold fltrd in *. rewrite filter_In in H0. destruct H0.
                              rewrite eq_TypeName_eq in H1... }
                            unfold H' in *. apply H18 in H0. rewrite combine_nth in H0...
                            match goal with [|- fst ?lhs' = fst ?rhs'] =>
                              set (lhs:=lhs') in *; set (rhs:=rhs') in * end.
                            destruct lhs. destruct rhs...
                          }
                          unfold ctor in *. rewrite H0. rewrite <- surjective_pairing.
                          unfold nth_e. rewrite eq_TypeName_eq in e. subst tn.
                          apply nth_In. rewrite <- H19. erewrite filter_ext; [apply nEq|].
                          intros. destruct a0. simpl. rewrite eq_TypeName_symm. f_equal.
                          match goal with [|- fst (fst (_ _ ?fltrd' _)) = _] => set (fltrd:=fltrd') end.
                          assert (In (nth (length l') fltrd d) fltrd).
                          { apply nth_In. simpl in Len. unfold fltrd... }
                          unfold fltrd in H1. rewrite filter_In in H1. destruct H1.
                          symmetry. unfold fltrd. apply eq_TypeName_eq...
                          }

                          1:{
                          set (lngth:=length l' -
                            length
                              (map
                                (fun x : QName * (ScopedName * expr) =>
                                 switch_indices_aux (program_skeleton p) (fst (global (fst x), snd x))
                                 (length (snd x0)) tn (snd (snd (global (fst x), snd x))))
                              (filter (gfunbods_filterfun_g (unscope (fst x0)))
                                (flat_map
                                  (fun x : QName * list (ScopedName * expr) =>
                                   map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                                (program_cfun_bods_g p))))).
                          assert (Tmp : lngth < length (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_l p))).
                          { unfold lngth in *. clear lngth. unfold Len in *. rewrite <- Len'1 in *.
                            erewrite cfun_bods_g_map_filter.
                            2:{ rewrite filter_In in H6. destruct H6... }
                            2:{ rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                                destruct x0. destruct s; try discriminate. apply Is_global_global. }
                            rewrite H0 in lEq. rewrite Hctxtseq in lEq. rewrite Nat.ltb_ge in H2.
                            apply (f_equal (@length _)) in lEq. rewrite map_length in *.
                            repeat (rewrite app_length in lEq). simpl in lEq.
                            repeat (rewrite map_length in lEq). rewrite map_length.
                            clear switch' switchEq Switch length_length m1_m2. clear - lEq H2.
                            erewrite filter_ext in lEq.
                            - rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                              erewrite filter_ext with (l0:=skeleton_cfun_sigs_l _) in lEq.
                              + rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                                rewrite (program_has_all_cfun_bods_g p) in lEq.
                                rewrite (program_has_all_cfun_bods_l p) in lEq.
                                repeat (rewrite <- filter_map in lEq). repeat (rewrite map_length in lEq).
                                erewrite filter_ext in lEq;
                                  [ erewrite filter_ext with (l0:=program_cfun_bods_l _) in lEq |].
                                * generalize lEq. clear lEq.
                                  do 2 instantiate (1:=fun x : TypeName * Name * cfun_bod =>
                                    eq_TypeName (fst (unscope (fst x0))) (fst (fst x))).
                                  intros. eapply plus_lt_reg_l. unfold cfun_bod_named in *. unfold cfun_bod in *.
                                  unfold QName in *. rewrite <- lEq. omega.
                                * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                                    with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                                * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                                    with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                              + eauto.
                            - eauto.
                          }
                          assert (Tmp2 : nth lngth
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_l p)) d
                            = nth (length l')
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_g p ++ program_cfun_bods_l p)) d).
                          { unfold lngth in *. rewrite filter_app. rewrite app_nth2.
                            - erewrite cfun_bods_g_map_filter.
                              + rewrite map_map. rewrite map_length...
                              + rewrite filter_In in H6. destruct H6...
                              + rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                                destruct x0. destruct s; try discriminate. apply Is_global_global.
                            - unfold Len in H2. apply Nat.ltb_ge...
                          }
                          rewrite <- Tmp2. unfold Len in *. clear Len. rename H2 into Len.
                          unfold m2. rewrite filter_In in H6. destruct H6.
                          unfold gfunsigs_filterfun_g in e. destruct x0. destruct s; try discriminate.
                          rewrite cfun_bods_l_map_filter with (d:=d'); try apply Is_global_global...
                          unfold localize_aux. repeat (rewrite map_map). simpl.
                          match goal with [|- In (_ (_ _ (_ ?fn' _) ?dd')) _] =>
                            set (fn:=fn'); set (dd:=dd') end.
                          replace dd with (fn d_a)... rewrite map_nth.
                          unfold fn. simpl.
                          assert (forall {A} l f d (x : A), find f l = Some x ->
                            In (from_some_default d (find f l)) l).
                          { clear. intros. induction l; try discriminate.
                            simpl. destruct (f a) eqn:fEq; [left|]...
                            right. apply IHl. simpl in H. rewrite fEq in H...
                          }
                          rewrite nth_indep with (d':=d)...
                          match goal with [|- In (_ _ (_ ?f _)) ?l] => case_eq (find f l); intros end;
                           [apply H2 with (x:=p0)|]... exfalso.
                          pose proof (program_cfun_bods_typecheck_l p) as Typ.
                          unfold cfun_bods_l_typecheck in Typ. rewrite Forall_forall in Typ.
                          assert (In (nth lngth
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst q) (fst (fst x)))
                              (program_cfun_bods_l p)) d) (program_cfun_bods_l p)).
                          { eapply proj1. rewrite <- filter_In. apply nth_In... }
                          apply Typ in H4. do 4 (destruct H4). inversion H5; subst.
                          apply listTypeDeriv'_lemma_ctx in H19. do 2 (rewrite map_length in H19).
                          rewrite Nat.eqb_eq in H19. clear - (**)Len(**) H3 H17 H18 H19 i e Tmp. unfold lookup_ctors in H17.
                          match goal with
                          | _ : match ?dstr with _ => _ end = _ |- _ => destruct dstr
                          end; try discriminate. inversion H17; subst. clear H17.
                          rewrite Forall_forall in H18. evar (d_c : (ScopedName * list TypeName)%type).
                          pose proof (conj i e) as FilterAux.
                          change (eq_TypeName tn (fst q)) with
                           ((fun x => eq_TypeName tn (fst (unscope (fst x)))) (global q, l3))
                           in FilterAux.
                          rewrite <- filter_In in FilterAux.
                          apply In_nth with (d:=d_c) in FilterAux. destruct FilterAux as [n [nEq nthEq]].
                          evar (d_e : (ScopedName * expr)%type). set (nth_e := nth n
                            (snd (nth lngth  (filter
                              (fun x0 : TypeName * Name * cfun_bod =>
                               eq_TypeName tn (fst (fst x0))) (program_cfun_bods_l p)) d)) d_e).
                          apply find_none with (x:=(global q, snd nth_e)) in H3;
                            [simpl in H3; rewrite eq_QName_refl in H3; discriminate|].
                          apply (f_equal fst) in nthEq. simpl in nthEq.
                          rewrite <- nthEq.
                          assert (fst (nth n (filter
                            (fun x : ScopedName * list TypeName =>
                             eq_TypeName tn (fst (unscope (fst x))))
                            (skeleton_ctors (program_skeleton p))) d_c) = fst nth_e).
                          { unfold nth_e. symmetry.
                            rewrite eq_TypeName_eq in e. subst tn.
                            match goal with [|- fst (_ _ ?lhs _) = fst (_ _ ?rhs _)] =>
                              specialize H18 with (x:=(nth n lhs d_e, nth n rhs d_c));
                              set (LenAux':=length lhs=length rhs)
                            end.
                            assert LenAux' as LenAux.
                            { unfold LenAux'. clear LenAux'. unfold QName in *. unfold cfun_bod in *.
                              rewrite <- H19. f_equal. apply filter_ext. intros. destruct a0.
                              match goal with [|- _ _ (_ (_ (_ _ ?fltrd' _))) = _] => set (fltrd:=fltrd') end.
                              assert (In (nth lngth fltrd d) fltrd).
                              { apply nth_In. unfold lngth. unfold fltrd... }
                              unfold fltrd in H0. rewrite filter_In in H0. destruct H0.
                              symmetry. unfold fltrd. rewrite eq_TypeName_eq in H1. rewrite <- H1.
                              apply eq_TypeName_symm.
                            }
                            rewrite <- combine_nth in H18...
                            match goal with [_ : In ?x (combine ?l1 ?l2) -> _ |- _] =>
                              set (H' := In x (combine l1 l2)) end.
                            assert H'. { unfold H'. clear H'.
                            match goal with [|- In (_ _ (_ (_ (_ _ ?fltrd' _)) _) _) _] => set (fltrd:=fltrd') end.
                            assert (In (nth lngth fltrd d) fltrd).
                            { apply nth_In. unfold lngth. unfold fltrd... }
                            erewrite filter_ext with (f:=fun x : ScopedName * list TypeName
                              => let (n0, _) := x in eq_TypeName _ _).
                            - apply nth_In. unfold fltrd in *.
                              rewrite combine_length. rewrite <- H19. erewrite filter_ext.
                              + rewrite Nat.min_id...
                              + intros. destruct a0. rewrite eq_TypeName_symm. f_equal.
                                rewrite filter_In in H0. destruct H0. symmetry. apply eq_TypeName_eq...
                            - intros. destruct a0. rewrite eq_TypeName_symm. f_equal.
                              unfold fltrd in *. rewrite filter_In in H0. destruct H0.
                              rewrite eq_TypeName_eq in H1... }
                            unfold H' in *. apply H18 in H0. rewrite combine_nth in H0...
                            match goal with [|- fst ?lhs' = fst ?rhs'] =>
                              set (lhs:=lhs') in *; set (rhs:=rhs') in * end.
                            destruct lhs. destruct rhs...
                          }
                          unfold ctor in *. rewrite H0. rewrite <- surjective_pairing.
                          unfold nth_e. rewrite eq_TypeName_eq in e. subst tn.
                          apply nth_In. rewrite <- H19. erewrite filter_ext; [apply nEq|].
                          intros. destruct a0. simpl. rewrite eq_TypeName_symm. f_equal.
                          match goal with [|- fst (fst (_ _ ?fltrd' _)) = _] => set (fltrd:=fltrd') end.
                          assert (In (nth lngth fltrd d) fltrd).
                          { apply nth_In. unfold lngth. unfold fltrd... }
                          unfold fltrd in H1. rewrite filter_In in H1. destruct H1.
                          symmetry. unfold fltrd. apply eq_TypeName_eq...
                          } } all:shelve.
                  +++ assert (exists sig, lookup_cfun_sig_scoped (program_skeleton p)
                        (fst (nth length_length m1_m2 (global_local (fst
                          (map_alternative_for_filter (unscope (fst x0)) d' d_a)),
                           snd (map_alternative_for_filter (unscope (fst x0)) d' d_a)))) =
                        Some sig) as SwitchAux1.
                      { unfold length_length. unfold m1_m2. unfold global_local.
                        case_eq Len; intros; unfold Len in *.
                        - unfold m1. rewrite <- map_nth. simpl.
                          unfold globalize_aux. rewrite map_map. simpl.
                          match goal with [|- exists _, _ _ ?nth' = _] => set (nthSn:=nth') end.
                          assert (In nthSn (map (fun x => global (fst x)) (program_cfun_bods_g p))).
                          { unfold nthSn. erewrite cfun_bods_g_map_filter.
                            2: { rewrite filter_In in H6. destruct H6... }
                            2: { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                                 destruct x0. destruct s; try discriminate. apply Is_global_global.
                            }
                          rewrite map_map. simpl. change (global (fst d_a))
                          with ((fun x => global (fst x)) d_a). rewrite map_nth.
                          match goal with [|- In (_ (_ ?y)) _] =>
                            change (global (fst y)) with ((fun x => global (fst x)) y) end.
                          apply in_map. eapply proj1. rewrite <- filter_In. apply nth_In.
                          apply Nat.ltb_lt...
                          }
                          rewrite <- map_map in H3. rewrite in_map_iff in H3. do 2 (destruct H3).
                          pose proof (program_has_all_cfun_bods_g p) as Zip.
                          unfold has_all_cfun_bods in Zip. rewrite <- Zip in H4.
                          unfold lookup_cfun_sig_scoped. rewrite <- H3. unfold lookup_cfun_sig_g.
                          unfold lookup_cfun_sig_x. case_eq (find (fun sig => eq_QName x (fst (fst sig)))
                            (skeleton_cfun_sigs_g (program_skeleton p))); intros...
                          rewrite in_map_iff in H4. do 2 (destruct H4).
                          apply find_none with (x:=x1) in H5... rewrite H4 in H5.
                          rewrite eq_QName_refl in H5. discriminate.
                        - unfold m2. rewrite <- map_nth. simpl.
                          unfold localize_aux. rewrite map_map. simpl.
                          match goal with [|- exists _, _ _ ?nth' = _] => set (nthSn:=nth') end.
                          assert (In nthSn (map (fun x => local (fst x)) (program_cfun_bods_l p))).
                          { unfold nthSn. erewrite cfun_bods_l_map_filter.
                            2: { rewrite filter_In in H6. destruct H6... }
                            2: { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                                 destruct x0. destruct s; try discriminate. apply Is_global_global.
                            }
                            rewrite map_map. simpl. change (local (fst d_a))
                            with ((fun x => local (fst x)) d_a). rewrite map_nth.
                            match goal with [|- In (_ (_ ?y)) _] =>
                              change (local (fst y)) with ((fun x => local (fst x)) y) end.
                            apply in_map. eapply proj1. rewrite <- filter_In. apply nth_In.
                            unfold Len in *. rewrite <- Len'1 in *.
                            erewrite cfun_bods_g_map_filter.
                            2:{ rewrite filter_In in H6. destruct H6... }
                            2:{ rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                                destruct x0. destruct s; try discriminate. apply Is_global_global. }
                            rewrite H0 in lEq. rewrite Hctxtseq in lEq. rewrite Nat.ltb_ge in H2.
                            apply (f_equal (@length _)) in lEq. rewrite map_length in *.
                            repeat (rewrite app_length in lEq). simpl in lEq.
                            repeat (rewrite map_length in lEq). rewrite map_length.
                            clear switch' switchEq Switch length_length aEq m1_m2. clear - lEq H2.
                            erewrite filter_ext in lEq.
                            - rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                              erewrite filter_ext with (l0:=skeleton_cfun_sigs_l _) in lEq.
                              + rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                                rewrite (program_has_all_cfun_bods_g p) in lEq.
                                rewrite (program_has_all_cfun_bods_l p) in lEq.
                                repeat (rewrite <- filter_map in lEq). repeat (rewrite map_length in lEq).
                                erewrite filter_ext in lEq;
                                  [ erewrite filter_ext with (l0:=program_cfun_bods_l _) in lEq |].
                                * generalize lEq. clear lEq.
                                  do 2 instantiate (1:=fun x : TypeName * Name * cfun_bod =>
                                    eq_TypeName (fst (unscope (fst x0))) (fst (fst x))).
                                  intros. eapply plus_lt_reg_l. unfold cfun_bod_named in *. unfold cfun_bod in *.
                                  unfold QName in *. rewrite <- lEq. omega.
                                * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                                    with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                                * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                                    with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                              + eauto.
                            - eauto.
                          }
                          rewrite <- map_map in H3. rewrite in_map_iff in H3. do 2 (destruct H3).
                          pose proof (program_has_all_cfun_bods_l p) as Zip.
                          unfold has_all_cfun_bods in Zip. rewrite <- Zip in H4.
                          unfold lookup_cfun_sig_scoped. rewrite <- H3. unfold lookup_cfun_sig_l.
                          unfold lookup_cfun_sig_x. case_eq (find (fun sig => eq_QName x (fst (fst sig)))
                            (skeleton_cfun_sigs_l (program_skeleton p))); intros...
                          rewrite in_map_iff in H4. do 2 (destruct H4).
                          apply find_none with (x:=x1) in H5... rewrite H4 in H5.
                          rewrite eq_QName_refl in H5. discriminate.
                      }

                      assert (Tmp : Len = false ->
                        length l' -
                            length
                              (map
                                (fun x : QName * (ScopedName * expr) =>
                                 switch_indices_aux (program_skeleton p)
                                  (fst (global (fst x), snd x)) (length (snd x0)) tn
                                  (snd (snd (global (fst x), snd x))))
                                (filter (gfunbods_filterfun_g (unscope (fst x0)))
                                   (flat_map
                                     (fun x : QName * list (ScopedName * expr) =>
                                      map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                                   (program_cfun_bods_g p)))) <
                          length (filter (fun x : TypeName * Name * cfun_bod =>
                            eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                            (program_cfun_bods_l p))).
                      { intros. unfold Len in *. rewrite <- Len'1 in *.
                        erewrite cfun_bods_g_map_filter.
                        2:{ rewrite filter_In in H6. destruct H6... }
                        2:{ rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                        destruct x0. destruct s; try discriminate. apply Is_global_global. }
                        rewrite H0 in lEq. rewrite Hctxtseq in lEq.
                        apply (f_equal (@length _)) in lEq. rewrite map_length in *.
                        repeat (rewrite app_length in lEq). simpl in lEq.
                        repeat (rewrite map_length in lEq). rewrite map_length.
                        clear switch' switchEq Switch length_length m1_m2 aEq SwitchAux1. clear - lEq H2.
                        erewrite filter_ext in lEq.
                        - rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                          erewrite filter_ext with (l0:=skeleton_cfun_sigs_l _) in lEq.
                          + rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                            rewrite (program_has_all_cfun_bods_g p) in lEq.
                            rewrite (program_has_all_cfun_bods_l p) in lEq.
                            repeat (rewrite <- filter_map in lEq). repeat (rewrite map_length in lEq).
                            erewrite filter_ext in lEq;
                              [ erewrite filter_ext with (l0:=program_cfun_bods_l _) in lEq |].
                            * generalize lEq. clear lEq.
                              do 2 instantiate (1:=fun x : TypeName * Name * cfun_bod =>
                              eq_TypeName (fst (unscope (fst x0))) (fst (fst x))).
                              intros. eapply plus_lt_reg_l. unfold cfun_bod_named in *. unfold cfun_bod in *.
                              unfold QName in *. rewrite <- lEq. rewrite Nat.ltb_ge in H2. omega.
                            * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                               with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                            * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                               with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                          + eauto.
                        - auto.
                      }

                      destruct SwitchAux1 as [sig SwitchAux1].
                      apply Switch with (sig:=sig)...
                      { evar (d_l0 : (QName * list TypeName * TypeName)%type).
                        replace l0 with (nth (length l') ctxts
                          ((fun x => snd x ++ snd x0) (fst d_l0))).
                        2:{ rewrite <- lEq. rewrite <- Len'1. rewrite app_nth2...
                            rewrite H0. rewrite Nat.sub_diag... }
                        replace sig with (nth (length l') (filter
                          (fun x1 : TypeName * Name * list TypeName * TypeName =>
                           eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
                          (skeleton_cfun_sigs_g (program_skeleton p) ++
                           skeleton_cfun_sigs_l (program_skeleton p))) d_l0).
                        2: { unfold length_length in *. unfold m1_m2 in *. unfold global_local in *.
                          case_eq Len; intros; unfold Len in *; rewrite H2 in *.
                          - rewrite Nat.ltb_lt in H2. eapply lookup_cfun_nth...
                          - rewrite Nat.ltb_ge in H2.
                            eapply lookup_cfun_nth_l... rewrite map_length in Tmp...
                        }
                        subst ctxts. rewrite map_app. repeat (rewrite map_map). simpl.
                        rewrite <- map_app. rewrite <- filter_app.
                        change (snd (fst d_l0) ++ snd x0)
                        with ((fun x => snd (fst x) ++ snd x0) d_l0). rewrite map_nth.
                        rewrite app_length. rewrite plus_comm...
                      }
                      clear switch switchEq Switch SwitchAux1 sig.
                      rewrite map_nth in aEq.
                      set (bods_gl := if Len then program_cfun_bods_g else program_cfun_bods_l).
                      assert (aEq' : a =
                        switch_indices_aux (program_skeleton p)
                          (global_local (fst (nth length_length
                            (filter
                              (fun x : TypeName * Name * cfun_bod =>
                               eq_TypeName (fst (unscope (fst x0)))
                              (fst (fst x))) (bods_gl p)) d_a)))
                          (length (snd x0)) tn
                          (snd
                            (from_some_default d'
                              (find
                                (fun y : ScopedName * expr =>
                                 match fst y with
                                 | local _ => false
                                 | global q' => eq_QName (unscope (fst x0)) q'
                                 end)
                          (snd (nth length_length
                            (filter
                              (fun x : TypeName * Name * cfun_bod =>
                               eq_TypeName (fst (unscope (fst x0)))
                            (fst (fst x))) (bods_gl p)) d_a)))))).
                      { unfold m1_m2 in *. unfold global_local in *. unfold length_length in *.
                        unfold bods_gl in *.
                        case_eq Len; intros; rewrite H2 in aEq; unfold m1 in *; unfold m2 in *.
                        - rewrite cfun_bods_g_map_filter with (d:=d') in aEq.
                          2: { rewrite filter_In in H6. destruct H6... }
                          2: { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                               destruct x0. destruct s; try discriminate. apply Is_global_global.
                          }
                          unfold globalize_aux in aEq. rewrite map_map in aEq.
                          change (global (fst (map_alternative_for_filter (unscope (fst x0))
                                              d' d_a)),
                                 snd  (map_alternative_for_filter (unscope (fst x0)) d' d_a))
                          with ((fun x => (global (fst (map_alternative_for_filter (unscope (fst x0))
                                                    d' x)),
                                      snd (map_alternative_for_filter (unscope (fst x0)) d' x))) d_a)
                          in aEq.
                          rewrite map_nth in aEq...
                        - rewrite cfun_bods_l_map_filter with (d:=d') in aEq.
                          2: { rewrite filter_In in H6. destruct H6... }
                          2: { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                               destruct x0. destruct s; try discriminate. apply Is_global_global.
                          }
                          unfold localize_aux in aEq. rewrite map_map in aEq.
                          change (local (fst (map_alternative_for_filter (unscope (fst x0))
                                              d' d_a)),
                                 snd  (map_alternative_for_filter (unscope (fst x0)) d' d_a))
                          with ((fun x => (local (fst (map_alternative_for_filter (unscope (fst x0))
                                                    d' x)),
                                      snd (map_alternative_for_filter (unscope (fst x0)) d' x))) d_a)
                          in aEq.
                          rewrite map_nth in aEq...
                      }
                      clear aEq. rename aEq' into aEq.
                      match goal with
                        [aEq : a = switch_indices_aux _ _ _ _ (snd (_ _ (_ _ (snd ?a'_0)))) |- _] =>
                         set (a':=a'_0) in * end.
                      assert (In a' (bods_gl p)) as Typ.
                      { unfold a'. eapply proj1. rewrite <- filter_In. apply nth_In.
                        unfold length_length. unfold bods_gl. case_eq Len; intros.
                        - apply Nat.ltb_lt...
                        - apply Tmp in H2...
                      }
                      pose proof (program_cfun_bods_typecheck_g p) as H3.
                      unfold cfun_bods_g_typecheck in H3. rewrite Forall_forall in H3.
                      pose proof (program_cfun_bods_typecheck_l p) as H3_l.
                      unfold cfun_bods_l_typecheck in H3_l. rewrite Forall_forall in H3_l.
                      assert (exists qn ctx t (ctorlist : list (ScopedName * list TypeName))
                        (bindings_exprs : list expr)
                        (bindings_types : list TypeName),
                        (if Len then lookup_cfun_sig_g else lookup_cfun_sig_l) (program_skeleton p) (fst a')
                          = Some (qn, ctx, t) /\
                        program_skeleton p //  (fst (fst a') :: ctx) ||- bindings_exprs :: bindings_types /\
                        index_list 1 ctx = combine bindings_exprs bindings_types /\
                        lookup_ctors (program_skeleton p) (fst (fst a')) = Some ctorlist /\
                        Forall
                         (fun x : ScopedName * expr * (ScopedName * list TypeName) =>
                          let (y, y0) := x in
                          let (sn, _) := y in
                          let (sn', _) := y0 in sn = sn')
                         (combine (snd a') ctorlist) /\
                        program_skeleton p ///
                          map (fun ctor : ScopedName * list TypeName =>
                               snd ctor ++ bindings_types) ctorlist |||-
                          map snd (snd a') ::: repeat t (length (snd a'))) as TypStuff.
                      { unfold bods_gl in Typ.
                        case_eq Len; intros; rewrite H2 in Typ.
                        - apply H3 in Typ. destruct Typ as [qn [args [t0 [SigLookup Typ]]]].
                          inversion Typ. subst qn0 t0 bindings cases prog.
                          do 6 eexists. repeat split; eauto.
                        - apply H3_l in Typ. destruct Typ as [qn [args [t0 [SigLookup Typ]]]].
                          inversion Typ. subst qn0 t0 bindings cases prog.
                          do 6 eexists. repeat split; eauto.
                      }
                      destruct TypStuff as [qn [ctx [t0 [ctorlist [bindings_exprs [bindings_types
                        [SigLookup [H4 [H5 [H7 [H8 H13]]]]]]]]]]].

                      match goal with [H13 : _ /// ?mctxt' |||- _ ::: _ |- _] =>
                          set (mctxt := mctxt') in * end.

                      pose proof H6 as H6'.
                      replace (filter (gfunsigs_filterfun_g tn)
                          (skeleton_ctors (program_skeleton p))) with
                        (filter (fun x => eq_TypeName tn (fst (unscope (fst x)))
                                  && match (fst x) with global _ => true | _ => false end)
                          (skeleton_ctors (program_skeleton p))) in H6.
                      2: { apply filter_ext. intros. unfold gfunsigs_filterfun_g.
                           destruct a0.
                           destruct s; simpl; try rewrite andb_false_r...
                           rewrite andb_true_r... }
                      rewrite <- filter_compose in H6. rewrite filter_filter in H6.
                      rewrite filter_In in H6. apply proj1 in H6.
                      apply in_split in H6. destruct H6 as [l_init [l_tail H6]].
                      unfold lookup_ctors in H7.
                      case_eq (filter (eq_TypeName (fst (fst a')))
                        (skeleton_dts (program_skeleton p))); intros;
                        unfold cfun_bod in *; rewrite H2 in H7; try discriminate.
                      inversion H7.
                      assert (fst (fst a') = tn) as tnEq.
                      { unfold a'. rewrite filter_In in H6'. destruct H6'.
                        unfold gfunsigs_filterfun_g in H11. destruct x0.
                        destruct s; try discriminate. rewrite eq_TypeName_eq in H11. subst tn.
                        simpl. unfold length_length in *. unfold bods_gl in *. case_eq Len; intros.
                        - unfold Len in H11. rewrite Nat.ltb_lt in H11.
                          pose proof (nth_In _ d_a H11).
                          rewrite filter_In in H12. destruct H12. simpl in H14.
                          unfold length_length in H14.
                          symmetry. apply eq_TypeName_eq...
                        - apply Tmp in H11. pose proof (nth_In _ d_a H11).
                          rewrite filter_In in H12. destruct H12. simpl in H14.
                          symmetry. apply eq_TypeName_eq...
                      }
                      match goal with [|- (_ / _ |- ?e' : _)] => set (e:=e') end.
                      assert (snda'Eq : exists es_0 es_0', length es_0 = length l_init /\
                        map snd (snd a') = es_0 ++ e :: es_0').
                      { exists (firstn (length l_init) (map snd (snd a'))).
                        exists (skipn (S (length l_init)) (map snd (snd a'))).
                        assert (length (firstn (S (length l_init)) (map snd (snd a'))) = S (length l_init))
                          as LenAux.
                        { rewrite firstn_length. apply Nat.min_l. subst ctorlist.
                          apply listTypeDeriv'_lemma_ctx in H13. rewrite beq_nat_true_iff in H13.
                          unfold cfun_bod. rewrite <- H13. unfold mctxt. rewrite map_length.
                          erewrite filter_ext.
                          - rewrite H6. rewrite app_length. simpl. omega.
                          - intros. destruct a0. rewrite <- tnEq. rewrite eq_TypeName_symm...
                        }
                        assert (x0Global : is_global (fst x0)).
                        { clear - H6'. rewrite filter_In in H6'. destruct H6'.
                          unfold gfunsigs_filterfun_g in H0. destruct x0. simpl.
                          destruct s; try discriminate. apply Is_global_global.
                        }
                        split.
                        - clear - LenAux. generalize dependent (map snd (snd a')).
                          generalize dependent (length l_init).
                          induction n; intros; try rewrite firstn_O...
                          simpl. destruct l3; try discriminate. simpl. rewrite IHn...
                        - rewrite <- firstn_skipn with (n:=S (length l_init)) at 1.
                          rewrite <- (app_nil_l (skipn _ _)) at 2. rewrite app_comm_cons.
                          rewrite app_assoc. f_equal.
                          rewrite firstn_nth with
                            (d:=snd (snd (map_alternative_for_filter (unscope (fst x0)) d' d_a)))...
                          f_equal. f_equal. unfold e. unfold a'.
                          unfold m1_m2. unfold m1. unfold m2.

                          change (snd (snd
                            (map_alternative_for_filter (unscope (fst x0)) d' d_a)))
                          with ((fun x => snd (snd x))
                            (map_alternative_for_filter (unscope (fst x0)) d' d_a)).
                          unfold global_local in *.
                          match goal with [|- _ = _ (_ (_ _ _ ((if Len then global else local) ?l, ?r)))] =>
                            replace ((if Len then global else local) l, r) with
                              (if Len then (global l, r) else (local l, r))
                          end.
                          2:{ destruct Len... }
                          match goal with
                            [|- _ = _ (_ (_ _ (if Len then globalize_aux (?la (?lb ?lc))
                              else localize_aux (?ra (?rb ?rc))) _))] =>
                            replace (if Len then globalize_aux (la (lb lc))
                              else localize_aux (ra (rb rc)))
                            with ((if Len then globalize_aux else localize_aux) (la (lb (bods_gl p))))
                          end.
                          2: { destruct Len... }
                          simpl.
                          assert (LenInEq : length_length < length
                            (filter
                              (fun x : TypeName * Name * list (ScopedName * expr) =>
                               eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                              (bods_gl p))).
                          { unfold length_length in *. unfold bods_gl in *.
                            case_eq Len; intros; unfold Len in *... apply Nat.ltb_lt...
                          }
                          clear LenAux. generalize LenInEq. generalize (length_length).
                          assert (exists g', bods_gl p = g' ++ bods_gl p) as gEq.
                          { exists []... }
                          generalize gEq. clear gEq. unfold globalize_aux in *.
                          generalize (bods_gl p) at - 1. generalize dependent l_init.
                          unfold m1 in *. unfold m2 in *. unfold m1_m2 in *.
                          unfold bods_gl in *. generalize Len.
                          generalize x0Global. generalize x0. generalize l_tail.
                          clear H3 H IHes0 Len1 Len2 es Heseq lEq ctxts Hctxtseq l''Eq ts Htseq l'Eq e
                            switch' Len'1 Len'2 H0 H1 LenInEq aEq.
                          clear. clear a es0 ts0 ctxts0 l l'' l0 l1 t l2.
                          generalize d_a. generalize d'. clear. induction c; intros.
                          + simpl in LenInEq. omega.
                          + simpl.
                            case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst a))); intros.
                            * unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
                              rewrite H.
                              assert (exists qn, forall d', filter (gfunbods_filterfun_g (unscope (fst x0)))
                                (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) =
                                [(qn, nth (length l_init) (snd a) d')]) as H0.
                              { exists (fst a). intros. unfold gfunbods_filterfun_g. clear - H6 H gEq x0Global.
                                match goal with [_ : ?flt' = l_init ++ _ |- _] => set (flt:=flt') end.
                                assert (forall dx, x0 = nth (length l_init) flt dx) as H0.
                                { unfold flt. rewrite H6. intros. rewrite app_nth2... rewrite Nat.sub_diag... }
                                evar (dx : (ScopedName * list TypeName)%type).
                                rewrite H0 with (dx:=dx).
                                erewrite filter_ext.
                                - erewrite <- filter_compose.
                                  match goal with [|- _ ?f' (filter ?g0' ?m') = _] =>
                                    set (g0:=g0'); set (f:=f'); set (m:=m') end.
                                  replace (filter g0 m) with m.
                                  2: {
                                    assert (forall me, In me m -> g0 me = true).
                                    { intros. unfold m in H1. rewrite in_map_iff in H1.
                                      do 2 (destruct H1). subst me.
                                      match goal with [H : eq_TypeName ?e1 (fst (fst a)) = _ |- _] =>
                                        change (eq_TypeName e1 (fst (fst a))) with
                                          ((fun x => eq_TypeName e1 (fst (fst x))) (fst a, x)) in H
                                      end.
                                      unfold g0...
                                    }
                                    unfold g0. induction m... simpl. rewrite <- IHm.
                                    - unfold g0 in H1. rewrite H1... apply in_eq.
                                    - intros. apply H1. apply in_cons...
                                  }
                                  assert (tnEq : tn = fst (unscope (fst x0))).
                                  { assert (In x0 (l_init ++ x0 :: l_tail)).
                                    { clear. induction l_init; try apply in_eq; try apply in_cons... }
                                    rewrite <- H6 in H1. rewrite filter_In in H1. destruct H1.
                                    rewrite eq_TypeName_eq in H2...
                                  }
                                  assert (map fst (snd a) = map fst (l_init ++ x0 :: l_tail)).
                                  { pose proof (program_cfun_bods_typecheck_g p) as H3.
                                    unfold cfun_bods_g_typecheck in H3. rewrite Forall_forall in H3.
                                    pose proof (program_cfun_bods_typecheck_l p) as H3_l.
                                    unfold cfun_bods_l_typecheck in H3_l. rewrite Forall_forall in H3_l.

                                    assert (exists ctx t (ctorlist : list (ScopedName * list TypeName))
                                      (bindings_exprs : list expr)
                                      (bindings_types : list TypeName),
                                      program_skeleton p // (fst (fst a) :: ctx) ||- bindings_exprs :: bindings_types /\
                                      index_list 1 ctx = combine bindings_exprs bindings_types /\
                                      lookup_ctors (program_skeleton p) (fst (fst a)) = Some ctorlist /\
                                      Forall
                                       (fun x : ScopedName * expr * (ScopedName * list TypeName) =>
                                        let (y, y0) := x in
                                        let (sn, _) := y in
                                        let (sn', _) := y0 in sn = sn')
                                        (combine (snd a) ctorlist) /\
                                        program_skeleton p ///
                                          map (fun ctor : ScopedName * list TypeName =>
                                               snd ctor ++ bindings_types) ctorlist |||-
                                          map snd (snd a) ::: repeat t (length (snd a))) as TypStuff.
                                    { destruct gEq.
                                      case_eq Len; intros; rewrite H1 in e.
                                      - assert (In a (program_cfun_bods_g p)) as Typ.
                                        { rewrite e. clear. induction x; try apply in_eq... right... }
                                        apply H3 in Typ. destruct Typ as [qn [args [t0 [_ Typ]]]].
                                        inversion Typ. subst qn0 t0 bindings cases prog.
                                        do 5 eexists. repeat split; eauto.
                                      - assert (In a (program_cfun_bods_l p)) as Typ.
                                        { rewrite e. clear. induction x; try apply in_eq... right... }
                                        apply H3_l in Typ. destruct Typ as [qn [args [t0 [_ Typ]]]].
                                        inversion Typ. subst qn0 t0 bindings cases prog.
                                        do 5 eexists. repeat split; eauto.
                                    }
                                    destruct TypStuff as [ctx [t0 [ctorlist [bindings_exprs [bindings_types
                                      [H4 [H5 [H11 [H12 H13]]]]]]]]].

                                    rewrite <- H6.
                                    unfold lookup_ctors in H11.
                                    case_eq (filter (eq_TypeName (fst (fst a)))
                                      (skeleton_dts (program_skeleton p)));
                                     intros; unfold QName in *; rewrite H1 in H11; try discriminate.
                                    inversion H11; subst. rewrite eq_TypeName_eq in H. rewrite H.
                                    clear - H12 H13. apply listTypeDeriv'_lemma_ctx in H13.
                                    repeat (rewrite map_length in H13). rewrite Nat.eqb_eq in H13.
                                    generalize H12 H13. clear. generalize (skeleton_ctors (program_skeleton p)).
                                    intros. evar (g : ScopedName * list TypeName -> bool).
                                    rewrite filter_ext with (g0:=g);
                                     [rewrite filter_ext with (g0:=g) in H13|];
                                     [rewrite filter_ext with (g0:=g) in H12 | |].
                                    - generalize dependent (snd a). generalize dependent (filter g c).
                                      unfold g in *. clear g.
                                      induction l; intros l0 H Len; destruct l0; try discriminate...
                                      simpl in *. inversion Len. inversion H. subst. rewrite IHl...
                                      destruct p0. destruct a0. subst...
                                    - unfold g in *. intros. destruct a0.
                                      instantiate (1:=fun x =>
                                        eq_TypeName (fst (unscope (fst x))) (fst (fst a)))...
                                    - unfold g in *. intros. destruct a0...
                                    - unfold g in *. intros. destruct a0... apply eq_TypeName_symm.
                                  }
                                  assert (In (fst a, nth (length l_init) (snd a) d'0) m).
                                  { unfold m. rewrite in_map_iff. exists (nth (length l_init) (snd a) d'0).
                                    split... apply nth_In. apply (f_equal (@length _)) in H1.
                                    repeat (rewrite map_length in H1). rewrite app_length in H1.
                                    simpl in H1. omega.
                                  }
                                  assert (f (fst a, nth (length l_init) (snd a) d'0) = true).
                                  { assert (fst (nth (length l_init) (snd a) d'0) = fst x0).
                                    { rewrite <- map_nth. rewrite H1. repeat (rewrite map_app).
                                      rewrite app_nth2; try repeat (rewrite map_length)...
                                      rewrite Nat.sub_diag...
                                    }
                                    symmetry in H3. rewrite <- eq_ScopedName_eq in H3.
                                    match goal with [_ : eq_ScopedName ?e1 (fst ?e2) = _ |- _] =>
                                      change (eq_ScopedName e1 (fst e2)) with
                                        ((fun x => eq_ScopedName e1 (fst (snd x))) (fst a, e2)) in H3
                                    end.
                                    unfold f...
                                  }
                                  pose proof (conj H2 H3). rewrite <- filter_In in H4.
                                  apply in_split in H4. do 2 destruct H4.
                                  destruct x; [destruct x1 |]...
                                  + simpl in *. unfold QName in *.
                                    unfold m in H4. apply (f_equal (map snd)) in H4. simpl in H4.
                                    unfold f in H4. change
                                      (fun x : TypeName * Name * (ScopedName * expr) =>
                                       eq_ScopedName (fst x0) (fst (snd x))) with
                                      (fun x : TypeName * Name * (ScopedName * expr) =>
                                       (fun y => eq_ScopedName (fst x0) (fst y)) (snd x)) in H4.
                                    rewrite filter_map in H4. rewrite map_map in H4. simpl in H4.
                                    rewrite map_id in H4. apply (f_equal (map fst)) in H4.
                                    rewrite filter_map in H4. rewrite H1 in H4. rewrite <- H6 in H4.
                                    change
                                      (fun x : ScopedName * list TypeName =>
                                       eq_TypeName tn (fst (unscope (fst x)))) with
                                      (fun x : ScopedName * list TypeName =>
                                       (fun y => eq_TypeName tn (fst (unscope y))) (fst x)) in H4.
                                    rewrite filter_map in H4. rewrite filter_compose in H4.
                                    subst. exfalso. clear - H4. generalize H4.
                                    generalize (nth (length l_init) (snd a) d'0). clear.
                                    pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
                                    unfold dts_ctor_names_unique in Uniq. generalize Uniq.
                                    generalize (map fst (skeleton_ctors (program_skeleton p))).
                                    clear. induction l; intros; try discriminate.
                                    inversion Uniq; subst. simpl in H4.
                                    case_eq (eq_ScopedName (fst x0) a); intros.
                                    * rewrite eq_ScopedName_eq in H. subst. rewrite eq_ScopedName_refl in H4.
                                      rewrite eq_TypeName_refl in H4. simpl in H4. inversion H4.
                                      pose proof (in_eq (fst (snd p0)) (map fst (map snd x1))).
                                      rewrite <- H3 in H. rewrite filter_In in H. destruct H.
                                      rewrite andb_true_iff in H5. destruct H5. rewrite eq_ScopedName_eq in H5.
                                      rewrite <- H5 in H...
                                    * rewrite H in H4. simpl in H4. simpl in IHl. eapply IHl...
                                  + simpl in *. unfold QName in *.
                                    unfold m in H4. apply (f_equal (map snd)) in H4. simpl in H4.
                                    unfold f in H4. change
                                      (fun x : TypeName * Name * (ScopedName * expr) =>
                                       eq_ScopedName (fst x0) (fst (snd x))) with
                                      (fun x : TypeName * Name * (ScopedName * expr) =>
                                       (fun y => eq_ScopedName (fst x0) (fst y)) (snd x)) in H4.
                                    rewrite filter_map in H4. rewrite map_map in H4. simpl in H4.
                                    rewrite map_id in H4. apply (f_equal (map fst)) in H4.
                                    rewrite filter_map in H4. rewrite H1 in H4. rewrite <- H6 in H4.
                                    change
                                      (fun x : ScopedName * list TypeName =>
                                       eq_TypeName tn (fst (unscope (fst x)))) with
                                      (fun x : ScopedName * list TypeName =>
                                       (fun y => eq_TypeName tn (fst (unscope y))) (fst x)) in H4.
                                    rewrite filter_map in H4. rewrite filter_compose in H4.
                                    subst. exfalso. clear - H4. generalize H4.
                                    generalize (nth (length l_init) (snd a) d'0). clear.
                                    pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
                                    unfold dts_ctor_names_unique in Uniq. generalize Uniq.
                                    generalize (map fst (skeleton_ctors (program_skeleton p))).
                                    clear. induction l; intros; try discriminate.
                                    inversion Uniq; subst. simpl in H4.
                                    case_eq (eq_ScopedName (fst x0) a0); intros.
                                    * rewrite eq_ScopedName_eq in H. subst. rewrite eq_ScopedName_refl in H4.
                                      rewrite eq_TypeName_refl in H4. simpl in H4. inversion H4.
                                      rewrite map_app in H4. simpl in H4.
                                      assert (In (fst p) (map fst (map snd x ++ p :: map snd x1))).
                                      { clear. rewrite in_map_iff. exists p. split...
                                        induction (map snd x); try apply in_eq. right...
                                      }
                                      rewrite map_app in H3. simpl in H3. rewrite <- H3 in H.
                                      rewrite filter_In in H. destruct H.
                                      rewrite andb_true_iff in H5. destruct H5. rewrite eq_ScopedName_eq in H5.
                                      rewrite <- H5 in H...
                                    * rewrite H in H4. simpl in H4. simpl in IHl. eapply IHl...
                                - intros. inversion x0Global. destruct a0. destruct q. destruct p0.
                                  simpl. destruct s... rewrite <- H0. rewrite <- H2.
                                  rewrite eq_TypeName_symm. rewrite andb_comm...
                              }
                              destruct H0 as [qn H0]. rewrite filter_app.
                              match goal with [|- _ = _ (_ (_ _ ((if Len then ?la else ?lb) (?lc1 ++ ?lc2)) _))] =>
                                replace ((if Len then la else lb) (lc1 ++ lc2))
                                with (((if Len then la else lb) lc1) ++ ((if Len then la else lb) lc2))
                              end.
                              2:{ unfold localize_aux. destruct Len; rewrite map_app... }
                              unfold QName in *. erewrite H0. case_eq Len; intros; rewrite H1 in *.
                              -- destruct length_length; simpl; [ rewrite map_nth|]...
                                 apply IHc.
                                 ++ destruct gEq as [g' gEq]. exists (g'++[a]). rewrite <- app_assoc...
                                 ++ simpl in LenInEq. rewrite H in LenInEq. simpl in LenInEq. omega.
                              -- destruct length_length; simpl; [ rewrite map_nth|]...
                                 apply IHc.
                                 ++ destruct gEq as [g' gEq]. exists (g'++[a]). rewrite <- app_assoc...
                                 ++ simpl in LenInEq. rewrite H in LenInEq. simpl in LenInEq. omega.
                            * unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
                              rewrite H.
                              assert (filter (gfunbods_filterfun_g (unscope (fst x0)))
                                (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = []) as H0.
                              { induction (snd a)... simpl. destruct a. destruct p0. destruct a0. simpl.
                                destruct s... simpl in *. rewrite eq_TypeName_symm. rewrite H... }
                              rewrite filter_app.
                              match goal with [|- _ = _ (_ (_ _ ((if Len then ?la else ?lb) (?lc1 ++ ?lc2)) _))] =>
                                replace ((if Len then la else lb) (lc1 ++ lc2))
                                with (((if Len then la else lb) lc1) ++ ((if Len then la else lb) lc2))
                              end.
                              2:{ unfold localize_aux. destruct Len; rewrite map_app... }
                              unfold QName in *. rewrite H0. case_eq Len; intros; rewrite H1 in *.
                              -- apply IHc.
                                 ++ destruct gEq as [g' gEq]. exists (g'++[a]). rewrite <- app_assoc...
                                 ++ simpl in LenInEq. rewrite H in LenInEq...
                              -- apply IHc.
                                 ++ destruct gEq as [g' gEq]. exists (g'++[a]). rewrite <- app_assoc...
                                 ++ simpl in LenInEq. rewrite H in LenInEq...
                      }

                      assert (mctxtEq : exists m0 m0', length m0 = length l_init /\
                        mctxt = m0 ++ (switch_indices_ctx l0 (length (snd x0))) :: m0').
                      { exists (firstn (length l_init) mctxt).
                        exists (skipn (S (length l_init)) mctxt).
                        assert (length (firstn (S (length l_init)) mctxt) = S (length l_init))
                          as LenAux.
                        { rewrite firstn_length. apply Nat.min_l.
                          unfold mctxt. subst ctorlist. rewrite map_length.
                          erewrite filter_ext.
                          + rewrite H6. rewrite app_length. simpl. omega.
                          + intros. destruct a0. simpl.
                            rewrite <- tnEq. apply eq_TypeName_symm.
                        }
                        split.
                        - clear - LenAux. generalize dependent mctxt.
                          generalize dependent (length l_init).
                          induction n; intros; try rewrite firstn_O...
                          simpl. destruct mctxt; try discriminate. simpl. rewrite IHn...
                        - rewrite <- firstn_skipn with (n:=S (length l_init)) at 1.
                          rewrite <- (app_nil_l (skipn _ _)) at 2. rewrite app_comm_cons.
                          rewrite app_assoc. f_equal.
                          evar (dctor : (ScopedName * list TypeName)%type).
                          rewrite firstn_nth with (d:=snd dctor ++ bindings_types)... subst ctorlist.
                          evar (ddtor : (ScopedName * list TypeName * TypeName)%type).
                          f_equal. f_equal.
                          replace l0 with (nth (length l) ctxts (snd (fst ddtor) ++ snd x0)).
                          2: { rewrite <- lEq. rewrite app_nth2...
                               rewrite Nat.sub_diag. rewrite H0... }
                          subst ctxts. unfold mctxt.
                          change (snd dctor ++ bindings_types) with
                           ((fun x => snd x ++ bindings_types) dctor).
                          rewrite map_nth.
                          change (snd (fst ddtor) ++ snd x0) with
                            ((fun x => snd (fst x) ++ snd x0) ddtor).
                          rewrite map_nth.
                          erewrite filter_ext; [rewrite H6|].
                          2: { intros. destruct a0. simpl.
                               rewrite eq_TypeName_symm. f_equal...
                          }
                          rewrite app_nth2... rewrite Nat.sub_diag. simpl.
                          match goal with [|- _ = _ (?lhs' ++ ?rhs') _] =>
                            set (lhs:=lhs'); set (rhs:=rhs')
                          end.
                          assert (switch_indices_ctx (lhs ++ rhs) (length rhs)
                            = rhs ++ lhs) as Switch.
                          { unfold switch_indices_ctx. generalize rhs lhs. clear.
                            induction rhs; intros.
                            - simpl. rewrite app_nil_r at 1. rewrite Nat.sub_0_r.
                              rewrite skipn_all_app. simpl. rewrite app_nil_r.
                              rewrite Nat.sub_0_r. apply firstn_all.
                            - repeat (rewrite app_length). simpl. rewrite Nat.add_sub.
                              rewrite skipn_all_app. simpl. f_equal.
                              rewrite <- IHrhs. rewrite firstn_app. rewrite Nat.sub_diag.
                              rewrite firstn_all. rewrite firstn_O. rewrite app_nil_r.
                              rewrite app_length. rewrite Nat.add_sub.
                              rewrite skipn_all_app. rewrite firstn_app.
                              rewrite firstn_all. rewrite Nat.sub_diag. rewrite firstn_O.
                              rewrite app_nil_r...
                          }
                          rewrite Switch. unfold lhs. unfold rhs. clear lhs rhs Switch.
                          f_equal.
                          unfold lookup_cfun_sig_g in SigLookup.
                          unfold lookup_cfun_sig_l in SigLookup.
                          unfold lookup_cfun_sig_x in SigLookup.
                          assert (bindings_types = ctx).
                          { apply listTypeDeriv_lemma in H4. clear - H4 H5.
                            rewrite Nat.eqb_eq in H4. generalize dependent bindings_types.
                            generalize dependent bindings_exprs. generalize dependent 0.
                            induction ctx; intros.
                            - simpl in H5. destruct bindings_types...
                              destruct bindings_exprs; discriminate.
                            - simpl in *. destruct bindings_types.
                              + destruct bindings_exprs; try discriminate.
                              + destruct bindings_exprs; try discriminate. f_equal.
                                * simpl in *. inversion H5; subst...
                                * inversion H5; subst. eapply IHctx...
                          }
                          subst bindings_types. unfold cfun_sig in *. unfold QName in *.
                          match goal with [H : ((if Len then ?f1 else ?f2) ?ps ?fa) = _ |- _] =>
                            set (f1':=f1) in H; set (f2':=f2) in H;
                            set (ps':=ps) in H; set (fa':=fa) in H
                          end.
                          assert ((if Len then f1' else f2') ps' fa'
                           = if Len then f1' ps' fa' else f2' ps' fa') as  SigLookupEq.
                          { destruct Len... }
                          rewrite SigLookupEq in SigLookup. clear SigLookupEq.
                          unfold f1' in *. unfold f2' in *.
                          match goal with [H : (if Len then ?f1 ?sg else ?f1 ?sl) = _ |- _] =>
                            replace (if Len then f1 sg else f1 sl)
                            with (f1 (if Len then sg else sl)) in H
                          end.
                          2:{ destruct Len... }
                          apply find_some in SigLookup. rewrite eq_QName_eq in SigLookup.
                          simpl in SigLookup. rewrite <- (proj2 SigLookup) in SigLookup.
                          apply proj1 in SigLookup.
                          apply (In_nth _ _ ((fun x => (unscope (fst (fst x)), snd (fst x), snd x)) ddtor))
                           in SigLookup.
                          destruct SigLookup as [x [xLen ctxEq]]. pose proof ctxEq as ctxEq'.
                          apply (f_equal (fun x => snd (fst x))) in ctxEq. simpl in ctxEq. rewrite <- ctxEq.
                          assert (LenSigs : length_length < length (filter
                            (fun x1 : TypeName * Name * list TypeName * TypeName =>
                             eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
                            ((if Len then skeleton_cfun_sigs_g else skeleton_cfun_sigs_l)
                             (program_skeleton p)))).
                          { unfold length_length in *. case_eq Len; intros; unfold Len in *.
                            - rewrite sigs_bods_g_length. apply Nat.ltb_lt...
                            - apply Tmp in H9. rewrite sigs_bods_l_length...
                          }
                          unfold length_length in *.
                          case_eq Len; intros; rewrite H9 in *.
                          + rewrite app_nth1.
                            2: { rewrite map_length. rewrite Len'1... }
                            pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p))
                            as Uniq.
                            unfold cfun_sigs_names_unique in Uniq.
                            match goal with [|- snd (fst ?lhs') = snd (fst ?rhs')] =>
                              set (lhs:=lhs'); set (rhs:=rhs') end.
                            set (rhs':=(fun x => (unscope (fst (fst x)), snd (fst x), snd x)) rhs).
                            replace (snd (fst rhs)) with (snd (fst rhs'))...
                            assert (In lhs (skeleton_cfun_sigs_g (program_skeleton p))).
                            { unfold lhs. apply nth_In... }
                            assert (In rhs' (skeleton_cfun_sigs_g (program_skeleton p))).
                            { unfold rhs'. set (rhs_fn:=fun x : ScopedName * list TypeName * TypeName
                                => (unscope (fst (fst x)), snd (fst x), snd x)).
                              change (unscope (fst (fst rhs)), snd (fst rhs), snd rhs) with (rhs_fn rhs).
                              unfold rhs. rewrite <- map_nth. rewrite map_map.
                              unfold rhs_fn. simpl.
                              rewrite map_ext with (g:=id); try (symmetry; repeat (rewrite <- surjective_pairing))...
                              rewrite map_id. eapply proj1. rewrite <- filter_In.
                              apply nth_In. rewrite Len'1...
                            }
                            assert (fst (fst lhs) = fst (fst rhs')).
                            { unfold lhs. unfold rhs'. unfold rhs. rewrite ctxEq'. simpl.
                              unfold fa'. unfold a'. rewrite <- map_nth. rewrite <- Len'1.
                              unfold bods_gl. rewrite H9.
                              erewrite filter_ext.
                              - rewrite filter_map.
                                pose proof (program_has_all_cfun_bods_g p) as Zip.
                                unfold has_all_cfun_bods in Zip.
                                unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
                                rewrite <- Zip. rewrite <- (map_nth _ _ ddtor).
                                rewrite map_map. simpl. rewrite <- map_nth with (d:=fst ddtor).
                                rewrite map_map. simpl. rewrite <- map_nth with (d:=fst (fst ddtor)).
                                rewrite map_map. simpl.
                                change (fun y : TypeName * Name * list TypeName * TypeName =>
                                  eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst y)))) with
                                  (fun y : TypeName * Name * list TypeName * TypeName =>
                                    (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x))
                                    ((fun z => fst (fst z)) y)).
                                rewrite filter_map. apply nth_indep.
                                unfold QName in *. rewrite Zip. rewrite Len'1. unfold Len in H9. clear - H9.
                                rewrite <- filter_map. rewrite map_length. apply Nat.ltb_lt...
                              - auto.
                            }
                            generalize Uniq. generalize H10. generalize H11. generalize H12.
                            generalize lhs. generalize rhs'. clear.
                            induction (skeleton_cfun_sigs_g (program_skeleton p)); intros;
                              [inversion H10|].
                            simpl in H11. simpl in H10. destruct H11; destruct H10.
                            * subst lhs. subst rhs'...
                            * rewrite H in Uniq. inversion Uniq; subst. rewrite <- H12 in H3.
                              apply (in_map (fun x => fst (fst x))) in H0. exfalso. apply H3...
                            * rewrite H0 in Uniq. inversion Uniq; subst. rewrite H12 in H3.
                              apply (in_map (fun x => fst (fst x))) in H. exfalso. apply H3...
                            * inversion Uniq. apply IHc...
                          + rewrite app_nth2.
                            2: { unfold Len in *. rewrite map_length. rewrite Len'1. clear - H9.
                              rewrite <- map_length with (f:=fun x => fst (fst x)). erewrite filter_ext.
                              - rewrite filter_map. rewrite (program_has_all_cfun_bods_g p).
                                rewrite <- map_length with (f:=fst) in H9. erewrite filter_ext in H9.
                                + rewrite filter_map in H9. apply Nat.ltb_ge...
                                + intros. simpl. change (eq_TypeName ?y (fst (fst a))) with
                                    ((fun x => eq_TypeName y (fst x)) (fst a))...
                              - eauto.
                            }
                            pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p))
                            as Uniq.
                            unfold cfun_sigs_names_unique in Uniq.
                            match goal with [|- snd (fst ?lhs') = snd (fst ?rhs')] =>
                              set (lhs:=lhs'); set (rhs:=rhs') end.
                            set (rhs':=(fun x => (unscope (fst (fst x)), snd (fst x), snd x)) rhs).
                            replace (snd (fst rhs)) with (snd (fst rhs'))...
                            assert (In lhs (skeleton_cfun_sigs_l (program_skeleton p))).
                            { unfold lhs. apply nth_In... }
                            assert (In rhs' (skeleton_cfun_sigs_l (program_skeleton p))).
                            { unfold rhs'. set (rhs_fn:=fun x : ScopedName * list TypeName * TypeName
                                => (unscope (fst (fst x)), (snd (fst x)), snd x)).
                              change (unscope (fst (fst rhs)), snd (fst rhs), snd rhs) with (rhs_fn rhs).
                              unfold rhs. rewrite <- map_nth. rewrite map_map.
                              unfold rhs_fn. simpl.
                              rewrite map_ext with (g:=id); try (symmetry; apply surjective_pairing).
                              rewrite map_id. eapply proj1. rewrite <- filter_In.
                              apply nth_In. rewrite Len'1.
                              erewrite cfun_bods_g_map_filter in LenSigs.
                              - rewrite map_map in LenSigs. rewrite map_length in LenSigs.
                                rewrite map_length. rewrite <- sigs_bods_g_length in LenSigs...
                              - rewrite filter_In in H6'. destruct H6'...
                              - rewrite filter_In in H6'. destruct H6'. unfold gfunsigs_filterfun_g in e0.
                                destruct x0. destruct s; try discriminate. apply Is_global_global.
                              - intros. destruct a0. destruct p0...
                            }
                            assert (fst (fst lhs) = fst (fst rhs')).
                            { unfold lhs. unfold rhs'. unfold rhs. rewrite ctxEq'. simpl.
                              unfold fa'. unfold a'. rewrite <- map_nth. rewrite <- Len'1.
                              unfold bods_gl. rewrite H9.
                              erewrite filter_ext with (l4:=program_cfun_bods_l p).
                              - rewrite filter_map.
                                pose proof (program_has_all_cfun_bods_l p) as Zip.
                                unfold has_all_cfun_bods in Zip.
                                unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
                                rewrite <- Zip. rewrite <- (map_nth _ _ ddtor).
                                rewrite map_map. simpl. rewrite <- map_nth with (d:=fst ddtor).
                                rewrite map_map. simpl. rewrite <- map_nth with (d:=fst (fst ddtor)).
                                rewrite map_map. simpl.
                                change (fun y : TypeName * Name * list TypeName * TypeName =>
                                  eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst y)))) with
                                  (fun y : TypeName * Name * list TypeName * TypeName =>
                                    (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x))
                                    ((fun z => fst (fst z)) y)).
                                rewrite filter_map.
                                assert (In x0 (skeleton_ctors (program_skeleton p))) as Aux1.
                                { rewrite filter_In in H6'. destruct H6'... }
                                assert (is_global (fst x0)) as Aux2.
                                { rewrite filter_In in H6'. destruct H6'. unfold gfunsigs_filterfun_g in e0.
                                  destruct x0. destruct s; try discriminate. apply Is_global_global.
                                }
                                erewrite cfun_bods_g_map_filter...
                                rewrite map_length. rewrite map_length. rewrite map_length.
                                rewrite sigs_bods_g_length. apply nth_indep.
                                rewrite Len'1. clear - Tmp Aux1 Aux2. rewrite map_length in Tmp.
                                rewrite <- filter_map. rewrite map_length. erewrite cfun_bods_g_map_filter in Tmp...
                                rewrite map_length in Tmp. rewrite sigs_bods_l_length...
                              - auto.
                            }
                            generalize Uniq. generalize H10. generalize H11. generalize H12.
                            generalize lhs. generalize rhs'. clear.
                            induction (skeleton_cfun_sigs_l (program_skeleton p)); intros;
                              [inversion H10|].
                            simpl in H11. simpl in H10. destruct H11; destruct H10.
                            * subst lhs. subst rhs'...
                            * rewrite H in Uniq. inversion Uniq; subst. rewrite <- H12 in H3.
                              apply (in_map (fun x => fst (fst x))) in H0. exfalso. apply H3...
                            * rewrite H0 in Uniq. inversion Uniq; subst. rewrite H12 in H3.
                              apply (in_map (fun x => fst (fst x))) in H. exfalso. apply H3...
                            * inversion Uniq. apply IHc...
                        }

                        assert (t = t0).
                        { evar (dx : (QName * list TypeName * TypeName)%type). assert (t = nth (length l') ts (snd dx)).
                          { rewrite <- l''Eq. rewrite H1. rewrite app_nth2; try (rewrite Len'2; omega).
                            replace (t::l2) with ([t]++l2)... rewrite app_nth1; try (rewrite Len'2; simpl; omega).
                            rewrite Len'2. rewrite Nat.sub_diag...
                          }
                          rewrite H9. clear H9.
                          case_eq Len; intros; rewrite H9 in *.
                          - clear - H9 SigLookup. unfold lookup_cfun_sig_g in SigLookup.
                            unfold lookup_cfun_sig_x in SigLookup. subst ts.
                            rewrite map_app. repeat (rewrite map_map). simpl.
                            unfold Len in *. rewrite Nat.ltb_lt in H9.
                            rewrite map_ext with (g:=snd)...
                            match goal with [|- _ _ (map snd ?mf' ++ _) _ = _] => set (mf:=mf') end.
                            assert (length l' < length mf).
                            { unfold mf. clear - H9. rewrite <- map_length with (f:=fun x => fst (fst (fst x))).
                              rewrite filter_map. rewrite <- map_map. rewrite (program_has_all_cfun_bods_g p).
                              rewrite map_map. rewrite <- filter_map. rewrite map_length...
                            }
                            rewrite app_nth1; try rewrite map_length...
                            pose proof (nth_In _  (fst d_a, snd (fst dx), snd dx) H11).
                            apply find_some in SigLookup.
                            destruct SigLookup as [SigLookup1 SigLookup2].
                            rewrite eq_QName_eq in SigLookup2. simpl in SigLookup2. subst qn.
                            unfold mf in *. unfold a' in *. unfold length_length in *.
                            unfold bods_gl in *.
                            rewrite <- Nat.ltb_lt in H9. rewrite H9 in *.
                            clear - SigLookup1 H12. clear e.
                            match goal with [|- ?goal = _] => set (tmp := goal) in * end.
                            case_eq (eq_TypeName tmp t0); intros; [apply eq_TypeName_eq|]... exfalso.
                            rewrite filter_In in H12. destruct H12 as [H12 _].
                            rewrite <- map_nth in SigLookup1.
                            change (fun x : TypeName * Name * list (ScopedName * expr) =>
                                    eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                              with (fun x : TypeName * Name * list (ScopedName * expr) =>
                                    (fun y => eq_TypeName (fst (unscope (fst x0))) (fst y)) (fst x)) in SigLookup1.
                            rewrite filter_map in SigLookup1.
                            rewrite <- (program_has_all_cfun_bods_g p) in SigLookup1.

                            pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
                            unfold cfun_sigs_names_unique in Uniq.
                            unfold tmp in H2. change (snd dx) with (snd (fst d_a, snd (fst dx), snd dx)) in H2.
                            rewrite map_nth in H2. clear tmp.
                            generalize SigLookup1. generalize H12. generalize H2. generalize Uniq.
                            generalize dx. generalize d_a. generalize ctx. generalize t0. generalize x0.
                            generalize (length l'). clear.
                            generalize (skeleton_cfun_sigs_g (program_skeleton p)) at 1 4 6.
                            induction c; intros; [inversion H12|].
                            inversion Uniq; subst. destruct H12; destruct SigLookup1...
                            + subst a. unfold QName in *. rewrite H0 in H2. simpl in H2.
                              rewrite eq_TypeName_refl in H2. discriminate.
                            + rewrite H in H1. apply H1. rewrite <- map_nth. rewrite <- map_nth. simpl.
                              apply (in_map (fun x => fst (fst x))) in H0. simpl in H0.
                              rewrite <- filter_map in H0. rewrite map_map...
                            + rewrite H0 in H1. apply H1. simpl.
                              apply (in_map (fun x => fst (fst x))) in H. do 2 rewrite <- map_nth in H.
                              rewrite map_map in H. rewrite <- filter_map...
                          - clear - Tmp H9 SigLookup Htseq. unfold lookup_cfun_sig_l in SigLookup.
                            unfold lookup_cfun_sig_x in SigLookup. subst ts.
                            rewrite map_app. repeat (rewrite map_map). simpl.
                            match goal with [|- _ _ (map _ ?mf' ++ _) _ = _] => set (mf:=mf') end.
                            assert (length l' >= length mf).
                            { unfold mf. clear - H9. rewrite <- map_length with (f:=fun x => fst (fst (fst x))).
                              rewrite filter_map. rewrite <- map_map. rewrite (program_has_all_cfun_bods_g p).
                              rewrite map_map. rewrite <- filter_map. rewrite map_length.
                              unfold Len in H9. rewrite Nat.ltb_ge in H9...
                            }
                            rewrite app_nth2; try rewrite map_length...
                            pose proof (Tmp eq_refl) as Tmp'.
                            rewrite <- map_length with (f:=fun x => fst (fst x)) in Tmp'.
                            rewrite filter_map in Tmp'. rewrite <- map_map in Tmp'.
                            rewrite <- (program_has_all_cfun_bods_l p) in Tmp'. rewrite map_map in Tmp'.
                            rewrite <- filter_map in Tmp'. rewrite map_length in Tmp'.
                            rewrite map_length in Tmp'.
                            pose proof (nth_In _  (fst d_a, snd (fst dx), snd dx) Tmp').
                            apply find_some in SigLookup.
                            destruct SigLookup as [SigLookup1 SigLookup2].
                            rewrite eq_QName_eq in SigLookup2. simpl in SigLookup2. subst qn.
                            unfold mf in *. unfold a' in *. unfold length_length in *.
                            unfold bods_gl in *.
                            rewrite H9 in *.
                            clear - SigLookup1 H4.
                            match goal with [|- ?goal = _] => set (tmp := goal) in * end.
                            case_eq (eq_TypeName tmp t0); intros; [apply eq_TypeName_eq|]... exfalso.
                            rewrite filter_In in H4. destruct H4 as [H4 _].
                            rewrite <- map_nth in SigLookup1.
                            change (fun x : TypeName * Name * list (ScopedName * expr) =>
                                    eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                              with (fun x : TypeName * Name * list (ScopedName * expr) =>
                                    (fun y => eq_TypeName (fst (unscope (fst x0))) (fst y)) (fst x)) in SigLookup1.
                            rewrite filter_map in SigLookup1.
                            rewrite <- (program_has_all_cfun_bods_l p) in SigLookup1.

                            pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
                            unfold cfun_sigs_names_unique in Uniq.
                            unfold tmp in H2. change (snd dx) with (snd (fst d_a, snd (fst dx), snd dx)) in H2.
                            rewrite map_nth in H2. clear tmp.
                            generalize SigLookup1. generalize H4. generalize H2. generalize Uniq.
                            generalize dx. generalize d_a. generalize ctx. generalize t0.
                            generalize (length l'). clear - H6'.
                            generalize (skeleton_cfun_sigs_l (program_skeleton p)) at 1 4 6.
                            induction c; intros; [inversion H4|].
                            inversion Uniq; subst. destruct H4; destruct SigLookup1...
                            + subst a. unfold QName in *.
                              match goal with [H2 : eq_TypeName (_ (_ ?n1 _ _)) _ = _ , _ : nth ?n2 _ _ = _ |- _] =>
                                replace n2 with n1 in H0 end.
                              2:{ erewrite cfun_bods_g_map_filter.
                               - rewrite map_length.
                                 rewrite <- (map_length (fun x => fst (fst x)) (filter _ (program_cfun_bods_g _))).
                                 rewrite filter_map.
                                 rewrite <- map_length with (f:=fun x => fst (fst (fst x))). rewrite filter_map.
                                 rewrite <- map_map. rewrite (program_has_all_cfun_bods_g p). rewrite map_map...
                               - clear - H6'. rewrite filter_In in H6'. destruct H6'...
                               - clear - H6'. rewrite filter_In in H6'. destruct H6'. unfold gfunsigs_filterfun_g in H0.
                                 destruct x0. destruct s; try discriminate. apply Is_global_global.
                              }
                              rewrite H0 in H2. simpl in H2.
                              rewrite eq_TypeName_refl in H2. discriminate.
                            + rewrite H in H1. apply H1. rewrite <- map_nth. rewrite <- map_nth. simpl.
                              apply (in_map (fun x => fst (fst x))) in H0. simpl in H0.
                              rewrite <- filter_map in H0. rewrite map_length in H0. rewrite map_map...
                            + rewrite H0 in H1. apply H1. simpl.
                              apply (in_map (fun x => fst (fst x))) in H. do 2 rewrite <- map_nth in H.
                              rewrite map_map in H. rewrite <- filter_map. rewrite map_length...
                        }

                        destruct mctxtEq as [m0 [m0' [m0Len mctxtEq]]].
                        destruct snda'Eq as [es_0 [es_0' [es_0Len snda'Eq]]].
                        unfold ctxt.
                        eapply ListTypeDeriv'_split with
                          (cs0:=m0)(cs0':=m0')(es0:=es_0)
                          (ts0:=repeat t0 (length es_0))(ts0':=repeat t0 (length es_0'))...
                        *** unfold ctxt. rewrite es_0Len...
                        *** rewrite es_0Len. rewrite repeat_length...
                        *** unfold ctxt in *. rewrite <- mctxtEq. rewrite <- snda'Eq. rewrite H9.
                            replace (repeat t0 (length es_0) ++ t0 :: repeat t0 (length es_0'))
                              with (repeat t0 (length (snd a')))...
                            apply (f_equal (@length _)) in snda'Eq. generalize snda'Eq.
                            rewrite map_length. generalize (snd a'). generalize es_0. generalize es_0'.
                            generalize e. clear. intros. rewrite app_length in snda'Eq. simpl in snda'Eq.
                            generalize dependent (length l). generalize (length es_0). generalize (length es_0').
                            clear. intros. subst. induction n0... simpl. rewrite IHn0...
Unshelve. all:(try (split; eauto; apply global));eauto.
- destruct x0. destruct s...
- destruct x0. destruct s...
- split; [|exact []]. destruct x0. destruct s...
- split; try exact (fst x0). exact (E_Var 0).
- split; try exact (fst x0). exact (E_Var 0).
- split; try exact (fst x0). exact (E_Var 0).
Grab Existential Variables. all:eauto.
Qed.

Corollary new_gfunbods_g_typecheck: forall p tn,
  Forall (no_matches tn) (map snd (flat_map snd (program_gfun_bods_g p))) ->
  Forall (no_matches tn) (map snd (flat_map snd (program_cfun_bods_l p))) ->
  Forall (no_matches tn) (map snd (flat_map snd (program_cfun_bods_g p))) ->
  gfun_bods_g_typecheck (refunctionalize_to_skeleton p tn) (new_gfun_bods_g p tn).
Proof with eauto.
intros. unfold gfun_bods_g_typecheck.
pose proof (program_gfun_bods_typecheck_g p).
pose proof (program_cfun_bods_typecheck_g p).
pose proof (program_cfun_bods_typecheck_l p).
unfold gfun_bods_g_typecheck in H2.
unfold cfun_bods_g_typecheck in H3.
unfold cfun_bods_l_typecheck in H4.
rewrite Forall_forall in *. intros.
unfold new_gfun_bods_g in H5.
apply in_app_or in H5. rewrite or_comm in H5. destruct H5.
- rewrite in_map_iff in H5. do 2 destruct H5. pose proof H6 as H6'.
  apply H2 in H6. destruct x. inversion H5; subst. simpl.
  do 3 destruct H6. exists x. exists x1. split.
  + unfold lookup_gfun_sig_g. simpl. unfold new_gfunsigs_g.
    unfold lookup_gfun_sig_g in H6. clear - H6.
    unfold lookup_gfun_sig_x in *. rewrite <- find_none_append...
    match goal with [|- ?lhs' = _] => set (lhs:=lhs') end.
    case_eq lhs; intros... exfalso. unfold lhs in *. apply find_some in H.
    apply find_some in H6. clear - H H6. simpl in *.
    destruct H. destruct H6. rewrite in_map_iff in H. do 2 destruct H.
    rewrite filter_In in H3. destruct H3. unfold gfunsigs_mapfun in *.
    destruct x2. destruct p0. destruct s; try discriminate.
    simpl in *. inversion H. subst. rewrite eq_QName_eq in *. simpl in *. subst.
    rewrite eq_TypeName_eq in *. subst. clear - H1 H3.
    pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as InCDts.
    unfold gfun_sigs_in_cdts in InCDts. rewrite Forall_forall in InCDts.
    pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)) as InDts.
    unfold dts_ctors_in_dts in InDts. rewrite Forall_forall in InDts.
    apply InCDts in H1. apply InDts in H3. simpl in *. clear - H1 H3.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
    unfold dts_cdts_disjoint in Disj. unfold not in Disj. eapply Disj.
    split...
  + set (cmtch:=E_CoMatch (fst x0) (index_list 0 x1) (snd x0)).
    assert (cmtch=cmtch)... apply (f_equal (refunctionalize_expr tn)) in H8.
    unfold cmtch in H8 at 1. cbn -[cmtch] in H8.
    replace (map (fun x : expr * TypeName => (refunctionalize_expr tn (fst x), snd x))
      (index_list 0 x1))
    with (index_list 0 x1) in H8.
    2:{ clear. generalize 0. induction x1; intros... simpl. f_equal. apply IHx1. }
    rewrite H8. unfold cmtch.
    apply refunctionalize_expr_preserves_typing...
    intros. inversion H9; subst; try discriminate. inversion H11; subst.
    * clear - H10 H14. generalize H14. clear H14. generalize dependent 0.
      induction x1; intros; [ inversion H14 |]. simpl in H14. destruct H14; subst.
      -- inversion H10; subst; try discriminate. inversion H0.
      -- eapply IHx1...
    * clear - H H11 H6' H14 H10. unfold no_matches in H.
      rewrite in_map_iff in H14. destruct H14. destruct H0.
      eapply H.
      -- rewrite in_map_iff. eexists. rewrite in_flat_map. rewrite and_comm. split...
      -- eauto.
- exists (fst x).
  rewrite in_map_iff in H5. do 2 (destruct H5).
  exists (snd x0). split.
  + unfold lookup_gfun_sig_g. simpl. unfold new_gfunsigs_g.
    rewrite filter_In in H6. destruct H6.
    unfold gfunsigs_filterfun_g in H7.
    case_eq (fst x0); intros.
    * destruct x0. simpl in H8. rewrite H8 in H7. discriminate.
    * replace (fst x) with (unscope (fst x0)). 2: { inversion H5... }
      apply gfun_sig_lookup with (q:=q)...
      destruct x0. simpl in *. rewrite H8 in H7. rewrite H8...
  + apply T_CoMatch with (bindings_exprs := map fst (index_list 0 (snd x0)))
      (bindings_types := snd x0)
      (dtorlist := (map (fun x => (global (fst (fst x)), snd (fst x), snd x)) (filter
        (fun x0 => eq_TypeName (fst (fst x)) (fst (fst (fst x0))))
        (skeleton_cfun_sigs_g (program_skeleton p)))) ++
       (map (fun x => (local (fst (fst x)), snd (fst x), snd x)) (filter
        (fun x0 => eq_TypeName (fst (fst x)) (fst (fst (fst x0))))
        (skeleton_cfun_sigs_l (program_skeleton p))))).
   * rewrite (combine_fst_snd (index_list 0 (snd x0))). f_equal.
     -- rewrite map_fst_combine... repeat (rewrite map_length)...
     -- generalize 0. generalize (snd x0). clear. induction l; intros...
        simpl. rewrite IHl...
   * rewrite <- (app_nil_l (snd x0)). apply index_list_typechecks...
   * unfold lookup_dtors. simpl.
     assert (eq_TypeName (fst (fst x)) tn = true) as eqTyp.
     { inversion H5. subst. simpl. rewrite filter_In in H6.
       destruct H6... destruct x0. simpl in *.
       destruct s; try discriminate. rewrite eq_TypeName_eq in *... }
     rewrite eqTyp. f_equal. unfold computeNewCoDatatype.
     rewrite filter_app.
     assert (filter (fun x1 : ScopedName * list TypeName * TypeName =>
         let (y,_) := x1 in let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst x)))
       (skeleton_dtors (program_skeleton p)) = []) as dtorsEq.
     { case_eq (filter (fun x1 : ScopedName * list TypeName * TypeName =>
                let (y, _) := x1 in let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst x)))
         (skeleton_dtors (program_skeleton p))); intros... exfalso.
       pose proof (in_eq p0 l). rewrite <- H7 in H8. rewrite filter_In in H8. destruct H8.
       pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)) as DtorInCdt.
       unfold cdts_dtors_in_cdts in DtorInCdt. rewrite Forall_forall in DtorInCdt.
       pose proof (DtorInCdt _ H8). destruct p0. simpl in *.
       rewrite filter_In in H6. destruct H6. destruct p0.
       rewrite eq_TypeName_eq in *. simpl in H10. rewrite H9 in H10.
       pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)) as CtorInDt.
       unfold dts_ctors_in_dts in CtorInDt. rewrite Forall_forall in CtorInDt.
       pose proof (CtorInDt _ H6). rewrite eqTyp in H10.
       unfold gfunsigs_filterfun_g in H11. destruct x0.
       destruct s0; try discriminate. rewrite eq_TypeName_eq in H11.
       simpl in H12. rewrite <- H11 in H12.
       pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
       unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=tn).
       split...
     }
     unfold Destructor in *. rewrite dtorsEq. rewrite app_nil_r.
     rewrite filter_app. f_equal.
     -- set (g:=fun y : QName * list TypeName * TypeName =>
                 (fun x1 => eq_TypeName (fst (unscope (fst (fst x1)))) tn)
                 ((fun x1 => (global (fst (fst x1)), snd (fst x1), snd x1)) y)).
        rewrite filter_ext with (g0:=g)... subst g. rewrite filter_map.
        set (g:=fun y : QName * list TypeName * TypeName =>
                 (fun x1 => eq_TypeName (fst (fst x)) (fst (unscope (fst (fst x1)))))
                 ((fun x1 => (global (fst (fst x1)), snd (fst x1), snd x1)) y)).
        rewrite filter_ext with (g0:=g)... subst g. rewrite filter_map.
        rewrite filter_compose.
        rewrite filter_ext with
          (g:=fun x1 => eq_TypeName (fst (fst x)) (fst (unscope (fst (fst x1)))))...
        intros. rewrite eq_TypeName_eq in eqTyp. rewrite eqTyp.
        destruct a. destruct p0. simpl. rewrite andb_diag. apply eq_TypeName_symm.
     -- set (g:=fun y : QName * list TypeName * TypeName =>
                 (fun x1 => eq_TypeName (fst (unscope (fst (fst x1)))) tn)
                 ((fun x1 => (local (fst (fst x1)), snd (fst x1), snd x1)) y)).
        rewrite filter_ext with (g0:=g)... subst g. rewrite filter_map.
        set (g:=fun y : QName * list TypeName * TypeName =>
                 (fun x1 => eq_TypeName (fst (fst x)) (fst (unscope (fst (fst x1)))))
                 ((fun x1 => (local (fst (fst x1)), snd (fst x1), snd x1)) y)).
        rewrite filter_ext with (g0:=g)... subst g. rewrite filter_map.
        rewrite filter_compose.
        rewrite filter_ext with
          (g:=fun x1 => eq_TypeName (fst (fst x)) (fst (unscope (fst (fst x1)))))...
        intros. rewrite eq_TypeName_eq in eqTyp. rewrite eqTyp.
        destruct a. destruct p0. simpl. rewrite andb_diag. apply eq_TypeName_symm.
   * clear - H5 H6. inversion H5. subst. clear - H6. rewrite Forall_forall. intros.
     destruct x. destruct p0. destruct p1. destruct p0. simpl in H.
     apply (in_map (fun x => (fst (fst x), snd x))) in H. simpl in H.
     rewrite map_fst_f_combine in H.
     apply (in_map (fun x => (fst x, (fun x => fst (fst x)) (snd x)))) in H. simpl in H.
     change (fun x : ScopedName * (ScopedName * list TypeName * TypeName) => (fst x, fst (fst (snd x))))
       with (fun x : ScopedName * (ScopedName * list TypeName * TypeName) =>
             (fst x, (fun x => fst (fst x)) (snd x))) in H.
     rewrite map_snd_f_combine in H.
     repeat (rewrite map_app in H). repeat (rewrite map_map in H).
     simpl in H. rewrite filter_In in H6. destruct H6 as [H6 H6GlobalAux].
     assert (is_global (fst x0)).
     { clear - H6GlobalAux. unfold gfunsigs_filterfun_g in H6GlobalAux.
       destruct x0. simpl. destruct s; try discriminate. apply Is_global_global.
     }
     unfold globalize_aux in H. rewrite map_map in H. simpl in H.
     unfold localize_aux in H. rewrite map_map in H. simpl in H.
     rewrite cfunbods_g_cfunsigs in H... rewrite cfunbods_l_cfunsigs in H...
     evar (d : ScopedName). apply (In_nth _ _ (d,d)) in H. destruct H as [n [H1 H2]].
     rewrite combine_nth in H2... inversion H2... Unshelve. all:eauto.
   * pose proof H0 as NoMatch_l. pose proof H1 as NoMatch_g.
     clear - H3 H4 H5 H6 NoMatch_g NoMatch_l.
     match goal with [|- _ /// ?ctxts' |||- ?es' ::: ?ts'] =>
       set (ctxts:=ctxts'); set (es:=es'); set (ts:=ts')
     end.
     assert (length ctxts = length es) as Len1.
     { unfold ctxts. unfold es. repeat (rewrite map_length). rewrite app_length.
       destruct x. simpl. inversion H5. subst. rewrite app_length.
       unfold globalize_aux. unfold localize_aux. repeat (rewrite map_map).
       assert (In x0 (skeleton_ctors (program_skeleton p))).
       { rewrite filter_In in H6. destruct H6... }
       assert (is_global (fst x0)).
       { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in H1.
         destruct x0. destruct s; try discriminate. apply Is_global_global.
       }
       pose proof (program_has_all_cfun_bods_g p) as Zip1.
       pose proof (program_has_all_cfun_bods_l p) as Zip2.
       unfold has_all_cfun_bods in *.
       f_equal; repeat (rewrite map_length).
       - erewrite cfun_bods_g_map_filter... rewrite map_length.
         rewrite <- map_length with (f:=fun x => fst (fst x)). unfold cfun_bod_named.
         rewrite <- map_length with (f:=fst).
         rewrite <- map_map.
         change (fun x : TypeName * Name * list TypeName * TypeName => ?t1 ?t2 (fst (fst (fst x))))
           with (fun x : TypeName * Name * list TypeName * TypeName => (fun y => t1 t2 (fst (fst y))) (fst x)).
         rewrite filter_map. rewrite map_length.
         erewrite filter_ext; [erewrite filter_ext with (l:=program_cfun_bods_g p) |].
         + rewrite filter_map. rewrite <- Zip1. rewrite <- map_map with (f:=fst).
           rewrite <- (filter_map (map fst _)). rewrite map_length...
         + intros. simpl. match goal with [|- ?lh1 ?lh2 = _] =>
             change (lh1 lh2) with ((fun x => lh1 (fst x)) (fst a)) end...
         + eauto.
       - erewrite cfun_bods_l_map_filter... rewrite map_length.
         rewrite <- map_length with (f:=fun x => fst (fst x)). unfold cfun_bod_named.
         rewrite <- map_length with (f:=fst).
         rewrite <- map_map.
         change (fun x : TypeName * Name * list TypeName * TypeName => ?t1 ?t2 (fst (fst (fst x))))
           with (fun x : TypeName * Name * list TypeName * TypeName => (fun y => t1 t2 (fst (fst y))) (fst x)).
         rewrite filter_map. rewrite map_length.
         erewrite filter_ext; [erewrite filter_ext with (l:=program_cfun_bods_l p) |].
         + rewrite filter_map. rewrite <- Zip2. rewrite <- map_map with (f:=fst).
           rewrite <- (filter_map (map fst _)). rewrite map_length...
         + intros. simpl. match goal with [|- ?lh1 ?lh2 = _] =>
             change (lh1 lh2) with ((fun x => lh1 (fst x)) (fst a)) end...
         + eauto.
     }
     assert (length es = length ts) as Len2.
     { unfold ts. unfold es. destruct x. inversion H5; subst. repeat (rewrite map_length).
       rewrite app_length. repeat (rewrite map_length). simpl. rewrite app_length.
       repeat (rewrite map_length). unfold globalize_aux. unfold localize_aux. repeat (rewrite map_length).
       assert (In x0 (skeleton_ctors (program_skeleton p))).
       { rewrite filter_In in H6. destruct H6... }
       assert (is_global (fst x0)).
       { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in H1.
         destruct x0. destruct s; try discriminate. apply Is_global_global.
       }
       erewrite cfun_bods_g_map_filter... erewrite cfun_bods_l_map_filter...
       repeat (rewrite map_length).
       pose proof (program_has_all_cfun_bods_g p) as Zip1.
       pose proof (program_has_all_cfun_bods_l p) as Zip2.
       unfold has_all_cfun_bods in *.
       rewrite <- map_length with (f:=fun x => fst (fst x)).
       change (fun x1 : TypeName * Name * list TypeName * TypeName =>
         eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
        with (fun x1 : TypeName * Name * list TypeName * TypeName =>
         (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) ((fun x => fst (fst x)) x1)).
       rewrite filter_map. unfold QName in *. rewrite Zip1.
       rewrite <- map_length with (f:=fun x => fst (fst x)).
       change (fun x1 : TypeName * Name * list TypeName * TypeName =>
         eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
        with (fun x1 : TypeName * Name * list TypeName * TypeName =>
         (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) ((fun x => fst (fst x)) x1)).
       rewrite filter_map. unfold QName in *. rewrite Zip2.
       do 2 rewrite <- (map_length fst (@filter (TypeName * Name * cfun_bod) _ _)).
       change (fun x : TypeName * Name * cfun_bod =>
         eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
        with (fun x : TypeName * Name * cfun_bod =>
         (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst x)).
       do 2 rewrite <- filter_map...
     }
     assert (exists l l' l'', length l = length l' /\ length l' = length l'' /\
       l ++ ctxts = ctxts /\ l' ++ es = es /\ l'' ++ ts = ts).
     { exists []. exists []. exists []... }
     generalize H. generalize ctxts at 1 3. generalize ts at 1 3. generalize es at 1 3.
     induction es0; intros.
     -- destruct H0 as [l [l' [l'' [Len'1 [Len'2 [lEq [l'Eq l''Eq]]]]]]].
        apply (f_equal (length (A:=_))) in lEq. rewrite Len1 in lEq.
        rewrite <- l'Eq in lEq. rewrite app_nil_r in lEq. rewrite <- Len'1 in lEq.
        destruct ctxts0; [|rewrite app_length in lEq; simpl in lEq; omega].
        rewrite app_nil_r in l'Eq. apply (f_equal (length (A:=_))) in l''Eq.
        rewrite app_length in l''Eq. rewrite <- Len2 in l''Eq.
        rewrite <- Len'2 in l''Eq. rewrite l'Eq in l''Eq.
        destruct ts0; [| simpl in l''Eq; omega].
        apply ListTypeDeriv'_Nil.
     -- destruct H0 as [l [l' [l'' [Len'1 [Len'2 [lEq [l'Eq l''Eq]]]]]]].
        case_eq ctxts0; intros; case_eq ts0; intros; simpl.
        ++ subst. apply (f_equal (length (A:=_))) in l'Eq.
           rewrite app_length in l'Eq. rewrite <- Len1 in l'Eq.
           rewrite <- Len'1 in l'Eq. rewrite <- lEq in l'Eq.
           simpl in l'Eq. rewrite app_nil_r in l'Eq. omega.
        ++ subst. apply (f_equal (length (A:=_))) in l'Eq.
           rewrite app_length in l'Eq. rewrite <- Len1 in l'Eq.
           rewrite <- Len'1 in l'Eq. rewrite <- lEq in l'Eq.
           simpl in l'Eq. rewrite app_nil_r in l'Eq. omega.
        ++ subst. apply (f_equal (length (A:=_))) in l''Eq.
           rewrite app_length in l''Eq. rewrite <- Len2 in l''Eq.
           rewrite <- Len'2 in l''Eq. rewrite <- l'Eq in l''Eq.
           rewrite app_length in l''Eq. simpl in l''Eq. omega.
        ++ apply ListTypeDeriv'_Cons.
           ** unfold es in l'Eq. destruct x. inversion H5; subst l3 q. clear H5.
              simpl in *. rewrite map_app in l'Eq.
              repeat (rewrite map_map in l'Eq). simpl in l'Eq.
              rewrite <- map_app in l'Eq.
              eapply new_gfunbods_g_typecheck_aux with
                (ctxts:=ctxts)(ctxts0:=ctxts0)(es:=es)(es0:=es0)(ts:=ts)(ts0:=ts0)...
           ** apply IHes0. exists (l++[l0]). exists (l'++[a]). exists (l''++[t]).
              split; try split; try (repeat (rewrite app_length); simpl; omega).
              split; try split; try (rewrite <- app_assoc; simpl; subst)...
              Unshelve. all:(split; try exact (fst x0); exact (E_Var 0)).
Qed.


(**************************************************************************************************)
(** Part 2: Typechecking local gfunbods                                                           *)
(**************************************************************************************************)

(* NOTE: This part has been 1:1 copied from tc global gfunbods with the appropriate names
   for local gfuns substituted for those for global gfuns.
   (Also, when destructing a ScopedName, the cases are switched appropriately.)
 *)

Lemma gfun_sig_lookup_l : forall x0 p tn l q,
  In x0 (skeleton_ctors (program_skeleton p)) ->
  fst x0 = local q ->
  eq_TypeName tn (fst (unscope (fst x0))) = true ->
  lookup_gfun_sig_x
    ((map gfunsigs_mapfun
          (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))))
     ++ l) (unscope (fst x0)) =
    Some (unscope (fst x0), snd x0).
Proof with auto.
intros.
apply in_split in H. do 2 (destruct H). rewrite H.
assert (exists l', skeleton_ctors (program_skeleton p) = l'++x++x0::x1).
{ exists []... }
clear H. rename H2 into H.
induction x.
- simpl. destruct x0. simpl in H0. subst. simpl in *. rewrite H1.
  simpl. rewrite eq_QName_refl...
- simpl. case_eq (gfunsigs_filterfun_l tn a); intros.
  + simpl.
    case_eq (eq_QName (unscope (fst x0)) (fst (gfunsigs_mapfun a)));
     intros.
    * pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)).
      unfold dts_ctor_names_unique in H4. destruct H.
      unfold gfunsigs_filterfun_l in H2. destruct a.
      destruct s; try discriminate. clear - H H0 H3 H4. rewrite H in H4.
      simpl in *. clear H. exfalso. induction x2.
      -- inversion H4. apply H2. clear - H0 H3. induction x.
         ++ rewrite eq_QName_eq in H3. subst. simpl. left. rewrite H0...
         ++ simpl. right. apply IHx.
      -- apply IHx2. inversion H4...
    * apply IHx. destruct H. exists (x2 ++ [a]). rewrite <- app_assoc...
  + apply IHx. destruct H. exists (x2 ++ [a]). rewrite <- app_assoc...
Qed.

Lemma filter_gfunbods_filterfun_l_unique :
forall p (a : QName) (a' : cfun_bod_named) q x0,
  is_local (fst x0) ->
  q = unscope (fst x0) ->
  In x0 (skeleton_ctors (program_skeleton p)) ->
  eq_TypeName (fst (unscope (fst x0))) (fst a) = true ->
  a = fst a' ->
  (exists l' l, l' ++ a' :: l = program_cfun_bods_g p) ->
  map fst
      (filter (gfunbods_filterfun_l q)
              (map (fun y : ScopedName * expr => (a, y)) (snd a')))
  = [a].
Proof with eauto.
intros p a a' q x0 Glob qEq x0In eqTyp eqA H.
assert (length (filter (gfunbods_filterfun_l q) (map (fun y => (a, y)) (snd a'))) = 1).
{ pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
  unfold cfun_sigs_names_unique in Uniq.
  case_eq (filter (gfunbods_filterfun_l q) (map (fun y => (a, y)) (snd a'))); intros.
  - exfalso. pose proof (program_cfun_bods_typecheck_g p) as Typ.
    unfold cfun_bods_g_typecheck in Typ.
    rewrite Forall_forall in Typ.
    assert (In a' (program_cfun_bods_g p)).
    { destruct H as [l1 [l2 H]]. rewrite <- H. clear.
      induction l1; try apply in_eq. right...
    }
    apply Typ in H1. destruct H1 as [qn [args [t [H1_1 H1_2]]]].
    inversion H1_2. subst.
    apply (f_equal (map (fun x => (fst x, fst (snd x))))) in H0.
    set (q:=unscope (fst x0)) in *. unfold QName in H0.
    rewrite filter_ext with (g:=fun y => (fun x => match x with
    | ((tn, _), local q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
    | _ => false
    end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    2: { intros. destruct a. simpl. destruct p0. destruct p1... }
    change
      (fun y : TypeName * Name * (ScopedName * expr) =>
        let (tn, _) := fst y in
        match fst (snd y) with
        | global _ => false
        | local q' => eq_TypeName tn (fst q) && eq_QName q q'
        end)
    with
      (fun y : TypeName * Name * (ScopedName * expr) => (fun x => match x with
        | ((tn, _), local q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
        | _ => false
        end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    rewrite filter_map in H0. rewrite map_map in H0. simpl in H0.
    match goal with [H0 : filter ?t ?t2 = _ |- _] => set (flt := filter t t2) in * end.
    assert (In (fst a', fst x0) flt); [|rewrite H0 in H1]...
    unfold flt. rewrite filter_In. split.
    + rewrite <- map_map. rewrite in_map_iff. exists (fst x0). split...
      assert (map fst (snd a') = map fst ctorlist) as CtorlistEq.
      { clear - H13 H14. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H14) as Len. clear H14.
        rewrite map_length in Len.
        unfold cfun_bod in *. generalize dependent ctorlist.
        generalize (@snd _ (list (prod ScopedName expr)) a'). induction l; intros.
        - destruct ctorlist; try discriminate...
        - destruct ctorlist; try discriminate. simpl. f_equal.
          + inversion H13. subst. destruct a. destruct p0...
          + apply IHl... inversion H13...
      }
      unfold QName in *. rewrite CtorlistEq.
      rewrite in_map_iff. exists x0. split...
      unfold lookup_ctors in H12.
      case_eq (filter (eq_TypeName (fst (fst a')))
         (skeleton_dts (program_skeleton p))); intros.
      * unfold cfun_bod in *. unfold QName in *. rewrite H1 in H12. discriminate.
      * unfold cfun_bod in *. unfold QName in *. rewrite H1 in H12. inversion H12.
        rewrite filter_In. split...
        destruct x0...
    + destruct a'. simpl. destruct q0. case_eq (fst x0); intros.
      * unfold q. rewrite H1. simpl. rewrite eq_QName_refl.
        simpl in eqTyp. rewrite eq_TypeName_eq in eqTyp. subst.
        unfold q. rewrite H1. simpl. rewrite eq_TypeName_refl...
      * inversion Glob. rewrite H1 in H3. discriminate.
  - clear eqTyp eqA. case_eq l; intros... exfalso. rewrite H1 in H0.
    pose proof (program_cfun_bods_typecheck_g p) as Typ.
    unfold cfun_bods_g_typecheck in Typ.
    rewrite Forall_forall in Typ.
    assert (In a' (program_cfun_bods_g p)).
    { destruct H as [l1 [l2 H]]. rewrite <- H. clear.
      induction l1; try apply in_eq. right...
    }
    apply Typ in H2. clear - H0 H2. destruct H2 as [qn [args [t [H2_1 H2_2]]]].
    inversion H2_2. subst.
    pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as Len.
    clear - H0 H11 H12 Len.
    unfold QName in H0.
    apply (f_equal (map (fun x => (fst x, fst (snd x))))) in H0.
    rewrite filter_ext with (g:=fun y => (fun x => match x with
    | ((tn, _), local q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
    | _ => false
    end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    2: { intros. destruct a0. simpl. destruct p3... }
    change
      (fun y : TypeName * Name * (ScopedName * expr) =>
        let (tn, _) := fst y in
        match fst (snd y) with
        | global _ => false
        | local q' => eq_TypeName tn (fst q) && eq_QName q q'
        end)
    with
      (fun y : TypeName * Name * (ScopedName * expr) => (fun x => match x with
        | ((tn, _), local q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
        | _ => false
        end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    rewrite filter_map in H0.
    rewrite map_map in H0. simpl in H0.
    assert (Unique.unique (map (fun x : ScopedName * expr => (a, fst x)) (snd a'))) as Uniq.
    { clear - H11 H12 Len. generalize H12. clear H12.
      assert (exists l, lookup_ctors (program_skeleton p) (fst (fst a')) = Some (l ++ ctorlist)).
      { exists []... }
      clear H11. generalize dependent ctorlist.
      change (list (ScopedName * expr)) with cfun_bod. generalize (snd a').
      induction c; intros.
      - apply Unique.Unique_nil.
      - simpl. apply Unique.Unique_cons.
        + clear - H H12 Len. destruct H as [l H].
          unfold lookup_ctors in H.
          destruct (filter (eq_TypeName (fst (fst a')))
            (skeleton_dts (program_skeleton p))); try discriminate.
          inversion H. clear H.
          pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
          unfold dts_ctor_names_unique in Uniq.
          apply (f_equal (map fst)) in H1.
          rewrite filter_ext with (g:=(fun y : ScopedName * list TypeName =>
             (fun x => eq_TypeName (fst (unscope x)) (fst (fst a')))
              (fst y))) in H1.
          2: { intros. destruct a1... }
          change (fun y => eq_TypeName (fst (unscope (fst y))) (fst (fst a')))
          with (fun y : ScopedName * list TypeName =>
                (fun x => eq_TypeName (fst (unscope x)) (fst (fst a')))
                (fst y)) in H1.
          rewrite filter_map in H1.
          pose proof (Unique.filter_unique _
            (fun x : ScopedName => eq_TypeName (fst (unscope x)) (fst (fst a'))) _ Uniq).
          rewrite H1 in H. clear - H12 H Len. rewrite map_app in H. apply app_unique_2 in H.
          inversion H; subst.
          * destruct ctorlist; simpl in H1; try discriminate.
          * destruct ctorlist; simpl in H0; try discriminate.
            inversion H0. subst. clear - H12 H1 Len. unfold not. intros. apply H1.
            inversion H12. subst. destruct a0. destruct p. subst. simpl in *.
            rewrite in_map_iff in H. destruct H as [x [H_1 H_2]].
            apply (in_map fst) in H_2. inversion H_1; subst.
            replace (map fst ctorlist) with (map fst c)...
            clear - H4 Len. generalize dependent ctorlist. induction c; intros.
            -- destruct ctorlist; try discriminate...
            -- destruct ctorlist; try discriminate. inversion H4. subst.
               destruct a. destruct p. simpl. f_equal...
        + destruct ctorlist.
          * apply IHc with (ctorlist:=[]); try inversion Len...
          * apply IHc with (ctorlist:=ctorlist); try inversion H12...
            destruct H as [l0 H]. exists (l0++[p0]). rewrite <- app_assoc...
    }
    eapply Unique.filter_unique in Uniq.
    unfold QName in *. rewrite H0 in Uniq.
    set (ml:=map (fun x : TypeName * Name * (ScopedName * expr) => (fst x, fst (snd x))) l0).
    pose proof (in_eq (fst p0, fst (snd p0)) ((fst p1, fst (snd p1)) :: ml)).
    pose proof (in_cons (fst p0, fst (snd p0)) _ _ (in_eq (fst p1, fst (snd p1)) ml)).
    unfold ml in *. pose proof H as Aux1. pose proof H1 as Aux2.
    rewrite <- H0 in Aux1. rewrite <- H0 in Aux2.
    rewrite filter_In in Aux1. rewrite filter_In in Aux2.
    inversion Uniq. subst. apply H4.
    assert (fst p0 = fst p1) as Eq1.
    { clear - Aux1 Aux2. destruct Aux1 as [Aux1 _]. destruct Aux2 as [Aux2 _].
      rewrite in_map_iff in Aux1. rewrite in_map_iff in Aux2.
      destruct Aux1 as [tmp1 [Aux1 _]]. destruct Aux2 as [tmp2 [Aux2 _]].
      inversion Aux1. inversion Aux2. subst...
    }
    assert (fst (snd p0) = fst (snd p1)) as Eq2.
    { destruct Aux1 as [_ Aux1]. destruct Aux2 as [_ Aux2]. clear - Aux1 Aux2.
      case_eq (fst (snd p0)); intros; rewrite H in Aux1; destruct (fst p0).
      - case_eq (fst (snd p1)); intros; rewrite H0 in Aux2; destruct (fst p1).
        + rewrite andb_true_iff in Aux1. destruct Aux1 as [_ Aux1].
          rewrite andb_true_iff in Aux2. destruct Aux2 as [_ Aux2].
          rewrite eq_QName_eq in Aux1. rewrite eq_QName_eq in Aux2. subst...
        + discriminate.
      - discriminate.
    }
    rewrite Eq1. rewrite Eq2. apply in_eq.
}
case_eq (filter (gfunbods_filterfun_l q) (map (fun y => (a, y)) (snd a'))); intros.
- apply (f_equal (length (A:=_))) in H1. rewrite H0 in H1. simpl in H1. discriminate.
- destruct l.
  + destruct p0. simpl. inversion H1. pose proof (in_eq (q0,p0) []).
    rewrite <- H3 in H2. rewrite filter_In in H2. destruct H2. rewrite in_map_iff in H2.
    destruct H2. inversion H2. inversion H5...
  + apply (f_equal (length (A:=_))) in H1. rewrite H0 in H1. simpl in H1. discriminate.
Qed.

Lemma filter_gfunbods_filterfun_l_unique_l :
forall p (a : QName) (a' : cfun_bod_named) q x0,
  is_local (fst x0) ->
  q = unscope (fst x0) ->
  In x0 (skeleton_ctors (program_skeleton p)) ->
  eq_TypeName (fst (unscope (fst x0))) (fst a) = true ->
  a = fst a' ->
  (exists l' l, l' ++ a' :: l = program_cfun_bods_l p) ->
  map fst
      (filter (gfunbods_filterfun_l q)
              (map (fun y : ScopedName * expr => (a, y)) (snd a')))
  = [a].
Proof with eauto.
intros p a a' q x0 Glob qEq x0In eqTyp eqA H.
assert (length (filter (gfunbods_filterfun_l q) (map (fun y => (a, y)) (snd a'))) = 1).
{ pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
  unfold cfun_sigs_names_unique in Uniq.
  case_eq (filter (gfunbods_filterfun_l q) (map (fun y => (a, y)) (snd a'))); intros.
  - exfalso. pose proof (program_cfun_bods_typecheck_l p) as Typ.
    unfold cfun_bods_l_typecheck in Typ.
    rewrite Forall_forall in Typ.
    assert (In a' (program_cfun_bods_l p)).
    { destruct H as [l1 [l2 H]]. rewrite <- H. clear.
      induction l1; try apply in_eq. right...
    }
    apply Typ in H1. destruct H1 as [qn [args [t [H1_1 H1_2]]]].
    inversion H1_2. subst.
    apply (f_equal (map (fun x => (fst x, fst (snd x))))) in H0.
    set (q:=unscope (fst x0)) in *. unfold QName in H0.
    rewrite filter_ext with (g:=fun y => (fun x => match x with
    | ((tn, _), local q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
    | _ => false
    end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    2: { intros. destruct a. simpl. destruct p0. destruct p1... }
    change
      (fun y : TypeName * Name * (ScopedName * expr) =>
        let (tn, _) := fst y in
        match fst (snd y) with
        | global _ => false
        | local q' => eq_TypeName tn (fst q) && eq_QName q q'
        end)
    with
      (fun y : TypeName * Name * (ScopedName * expr) => (fun x => match x with
        | ((tn, _), local q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
        | _ => false
        end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    rewrite filter_map in H0. rewrite map_map in H0. simpl in H0.
    match goal with [H0 : filter ?t ?t2 = _ |- _] => set (flt := filter t t2) in * end.
    assert (In (fst a', fst x0) flt); [|rewrite H0 in H1]...
    unfold flt. rewrite filter_In. split.
    + rewrite <- map_map. rewrite in_map_iff. exists (fst x0). split...
      assert (map fst (snd a') = map fst ctorlist) as CtorlistEq.
      { clear - H13 H14. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H14) as Len. clear H14.
        rewrite map_length in Len.
        unfold cfun_bod in *. generalize dependent ctorlist.
        generalize (@snd _ (list (prod ScopedName expr)) a'). induction l; intros.
        - destruct ctorlist; try discriminate...
        - destruct ctorlist; try discriminate. simpl. f_equal.
          + inversion H13. subst. destruct a. destruct p0...
          + apply IHl... inversion H13...
      }
      unfold QName in *. rewrite CtorlistEq.
      rewrite in_map_iff. exists x0. split...
      unfold lookup_ctors in H12.
      case_eq (filter (eq_TypeName (fst (fst a')))
         (skeleton_dts (program_skeleton p))); intros.
      * unfold cfun_bod in *. unfold QName in *. rewrite H1 in H12. discriminate.
      * unfold cfun_bod in *. unfold QName in *. rewrite H1 in H12. inversion H12.
        rewrite filter_In. split...
        destruct x0...
    + destruct a'. simpl. destruct q0. case_eq (fst x0); intros.
      * unfold q. rewrite H1. simpl. rewrite eq_QName_refl.
        simpl in eqTyp. rewrite eq_TypeName_eq in eqTyp. subst.
        unfold q. rewrite H1. simpl. rewrite eq_TypeName_refl...
      * inversion Glob. rewrite H1 in H3. discriminate.
  - clear eqTyp eqA. case_eq l; intros... exfalso. rewrite H1 in H0.
    pose proof (program_cfun_bods_typecheck_l p) as Typ.
    unfold cfun_bods_l_typecheck in Typ.
    rewrite Forall_forall in Typ.
    assert (In a' (program_cfun_bods_l p)).
    { destruct H as [l1 [l2 H]]. rewrite <- H. clear.
      induction l1; try apply in_eq. right...
    }
    apply Typ in H2. clear - H0 H2. destruct H2 as [qn [args [t [H2_1 H2_2]]]].
    inversion H2_2. subst.
    pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as Len.
    clear - H0 H11 H12 Len.
    unfold QName in H0.
    apply (f_equal (map (fun x => (fst x, fst (snd x))))) in H0.
    rewrite filter_ext with (g:=fun y => (fun x => match x with
    | ((tn, _), local q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
    | _ => false
    end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    2: { intros. destruct a0. simpl. destruct p3... }
    change
      (fun y : TypeName * Name * (ScopedName * expr) =>
        let (tn, _) := fst y in
        match fst (snd y) with
        | global _ => false
        | local q' => eq_TypeName tn (fst q) && eq_QName q q'
        end)
    with
      (fun y : TypeName * Name * (ScopedName * expr) => (fun x => match x with
        | ((tn, _), local q') => andb (eq_TypeName tn (fst q)) (eq_QName q q')
        | _ => false
        end) ((fun x => (fst x, fst (snd x))) y)) in H0.
    rewrite filter_map in H0.
    rewrite map_map in H0. simpl in H0.
    assert (Unique.unique (map (fun x : ScopedName * expr => (a, fst x)) (snd a'))) as Uniq.
    { clear - H11 H12 Len. generalize H12. clear H12.
      assert (exists l, lookup_ctors (program_skeleton p) (fst (fst a')) = Some (l ++ ctorlist)).
      { exists []... }
      clear H11. generalize dependent ctorlist.
      change (list (ScopedName * expr)) with cfun_bod. generalize (snd a').
      induction c; intros.
      - apply Unique.Unique_nil.
      - simpl. apply Unique.Unique_cons.
        + clear - H H12 Len. destruct H as [l H].
          unfold lookup_ctors in H.
          destruct (filter (eq_TypeName (fst (fst a')))
            (skeleton_dts (program_skeleton p))); try discriminate.
          inversion H. clear H.
          pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
          unfold dts_ctor_names_unique in Uniq.
          apply (f_equal (map fst)) in H1.
          rewrite filter_ext with (g:=(fun y : ScopedName * list TypeName =>
             (fun x => eq_TypeName (fst (unscope x)) (fst (fst a')))
              (fst y))) in H1.
          2: { intros. destruct a1... }
          change (fun y => eq_TypeName (fst (unscope (fst y))) (fst (fst a')))
          with (fun y : ScopedName * list TypeName =>
                (fun x => eq_TypeName (fst (unscope x)) (fst (fst a')))
                (fst y)) in H1.
          rewrite filter_map in H1.
          pose proof (Unique.filter_unique _
            (fun x : ScopedName => eq_TypeName (fst (unscope x)) (fst (fst a'))) _ Uniq).
          rewrite H1 in H. clear - H12 H Len. rewrite map_app in H. apply app_unique_2 in H.
          inversion H; subst.
          * destruct ctorlist; simpl in H1; try discriminate.
          * destruct ctorlist; simpl in H0; try discriminate.
            inversion H0. subst. clear - H12 H1 Len. unfold not. intros. apply H1.
            inversion H12. subst. destruct a0. destruct p. subst. simpl in *.
            rewrite in_map_iff in H. destruct H as [x [H_1 H_2]].
            apply (in_map fst) in H_2. inversion H_1; subst.
            replace (map fst ctorlist) with (map fst c)...
            clear - H4 Len. generalize dependent ctorlist. induction c; intros.
            -- destruct ctorlist; try discriminate...
            -- destruct ctorlist; try discriminate. inversion H4. subst.
               destruct a. destruct p. simpl. f_equal...
        + destruct ctorlist.
          * apply IHc with (ctorlist:=[]); try inversion Len...
          * apply IHc with (ctorlist:=ctorlist); try inversion H12...
            destruct H as [l0 H]. exists (l0++[p0]). rewrite <- app_assoc...
    }
    eapply Unique.filter_unique in Uniq.
    unfold QName in *. rewrite H0 in Uniq.
    set (ml:=map (fun x : TypeName * Name * (ScopedName * expr) => (fst x, fst (snd x))) l0).
    pose proof (in_eq (fst p0, fst (snd p0)) ((fst p1, fst (snd p1)) :: ml)).
    pose proof (in_cons (fst p0, fst (snd p0)) _ _ (in_eq (fst p1, fst (snd p1)) ml)).
    unfold ml in *. pose proof H as Aux1. pose proof H1 as Aux2.
    rewrite <- H0 in Aux1. rewrite <- H0 in Aux2.
    rewrite filter_In in Aux1. rewrite filter_In in Aux2.
    inversion Uniq. subst. apply H4.
    assert (fst p0 = fst p1) as Eq1.
    { clear - Aux1 Aux2. destruct Aux1 as [Aux1 _]. destruct Aux2 as [Aux2 _].
      rewrite in_map_iff in Aux1. rewrite in_map_iff in Aux2.
      destruct Aux1 as [tmp1 [Aux1 _]]. destruct Aux2 as [tmp2 [Aux2 _]].
      inversion Aux1. inversion Aux2. subst...
    }
    assert (fst (snd p0) = fst (snd p1)) as Eq2.
    { destruct Aux1 as [_ Aux1]. destruct Aux2 as [_ Aux2]. clear - Aux1 Aux2.
      case_eq (fst (snd p0)); intros; rewrite H in Aux1; destruct (fst p0).
      - case_eq (fst (snd p1)); intros; rewrite H0 in Aux2; destruct (fst p1).
        + rewrite andb_true_iff in Aux1. destruct Aux1 as [_ Aux1].
          rewrite andb_true_iff in Aux2. destruct Aux2 as [_ Aux2].
          rewrite eq_QName_eq in Aux1. rewrite eq_QName_eq in Aux2. subst...
        + discriminate.
      - discriminate.
    }
    rewrite Eq1. rewrite Eq2. apply in_eq.
}
case_eq (filter (gfunbods_filterfun_l q) (map (fun y => (a, y)) (snd a'))); intros.
- apply (f_equal (length (A:=_))) in H1. rewrite H0 in H1. simpl in H1. discriminate.
- destruct l.
  + destruct p0. simpl. inversion H1. pose proof (in_eq (q0,p0) []).
    rewrite <- H3 in H2. rewrite filter_In in H2. destruct H2. rewrite in_map_iff in H2.
    destruct H2. inversion H2. inversion H5...
  + apply (f_equal (length (A:=_))) in H1. rewrite H0 in H1. simpl in H1. discriminate.
Qed.

Lemma cfunbods_g_cfunsigs_l : forall p (x0 : ScopedName * list TypeName),
  In x0 (skeleton_ctors (program_skeleton p)) ->
  is_local (fst x0) ->
  map (fun x : QName * (ScopedName * expr) => global (fst x))
      (filter (gfunbods_filterfun_l (unscope (fst x0)))
              (flat_map
                 (fun x : QName * list (ScopedName * expr) =>
                  map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                 (program_cfun_bods_g p)))
= map (fun x : QName * list TypeName * TypeName => global (fst (fst x)))
      (filter (fun x1 : TypeName * Name * list TypeName * TypeName =>
               eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
              (skeleton_cfun_sigs_g (program_skeleton p))).
Proof with auto.
intros p x0 x0In Glob. pose proof (program_has_all_cfun_bods_g p) as H.
unfold has_all_cfun_bods in H.
rewrite <- map_map with (f:=fst).
change (fun x : QName * list TypeName * TypeName => global (fst (fst x)))
  with (fun y : QName * list TypeName * TypeName => (fun x => global (fst x)) (fst y)).
repeat (rewrite <- map_map with (f:=fst)). f_equal.
remember (program_cfun_bods_g p) as l.
remember (skeleton_cfun_sigs_g (program_skeleton p)) as l2.
assert (exists l' l2', length l' = length l2' /\
  l' ++ l = program_cfun_bods_g p /\
  l2' ++ l2 = skeleton_cfun_sigs_g (program_skeleton p)).
{ exists []. exists []... }
rewrite Heql in H. rewrite Heql2 in H.
clear Heql. clear Heql2. generalize dependent l2.
induction l.
- induction l2... intros H0.
  destruct H0 as [l' [l2' [Len [H1 H2]]]].
  apply (f_equal (length (A:=_))) in H. repeat (rewrite map_length in H).
  rewrite app_nil_r in H1. rewrite <- H1 in H. rewrite <- H2 in H.
  unfold cfun_bod_named in *. rewrite Len in H. rewrite app_length in H.
  simpl in H. omega.
- induction l2. intros H0.
  + destruct H0 as [l' [l2' [Len [H1 H2]]]].
    apply (f_equal (length (A:=_))) in H. repeat (rewrite map_length in H).
    rewrite app_nil_r in H2. rewrite <- H1 in H. rewrite <- H2 in H.
    unfold cfun_sig in *. rewrite <- Len in H. rewrite app_length in H.
    simpl in H. omega.
  + simpl. rewrite filter_app. rewrite map_app.
    case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst a0)))); intros.
    * unfold QName in *. rewrite H0. simpl.
      match goal with
        [ |- ?t = fst (fst a0) :: ?t2] => change (fst (fst a0) :: t2) with ([fst (fst a0)] ++ t2)
      end.
      rewrite IHl with (l2:=l2).
      2: {
        destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]]. exists (l'++[a]). exists (l2'++[a0]).
        repeat (rewrite app_length). split...
        repeat (rewrite <- app_assoc). simpl. split...
      }
      unfold QName in *. f_equal.
      assert (fst (fst a0) = fst a).
      { destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]].
        apply (f_equal (map fst)) in H1_1. apply (f_equal (map (fun x => fst (fst x)))) in H1_2.
        unfold QName in *. rewrite H in H1_2. rewrite <- H1_1 in H1_2.
        clear - H1_2 Len. generalize dependent l2'. induction l'; intros.
        - destruct l2'; try discriminate. simpl in H1_2. inversion H1_2. rewrite H0...
        - destruct l2'; try discriminate. apply IHl' with (l2':=l2')...
          simpl in H1_2. inversion H1_2... }
      unfold cfun_bod in *. unfold QName in *. rewrite <- H2.
      assert (exists l' l, l' ++ a :: l = program_cfun_bods_g p).
      { destruct H1. destruct H1. destruct H1. destruct H1. destruct H3.
        exists x. exists l...
      }
      apply filter_gfunbods_filterfun_l_unique with (p:=p) (x0:=x0)...
    * unfold QName in *. rewrite H0.
      assert (filter (gfunbods_filterfun_l (unscope (fst x0)))
        (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = nil).
      { clear - H0 H H1. unfold gfunbods_filterfun_l. induction (snd a)...
        simpl. destruct a. simpl. destruct q. destruct a1. destruct s...
        destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]].
        assert (t = fst (fst (fst a0))).
        { clear IHc.
          apply (f_equal (map fst)) in H1_1. apply (f_equal (map (fun x => fst (fst x)))) in H1_2.
          unfold QName in *. rewrite H in H1_2. rewrite <- H1_1 in H1_2.
          clear - H1_2 Len. generalize dependent l2'. induction l'; intros.
          - destruct l2'; try discriminate. simpl in H1_2. inversion H1_2. rewrite H0...
          - destruct l2'; try discriminate. apply IHl' with (l2':=l2')...
            simpl in H1_2. inversion H1_2...
        }
        subst. rewrite eq_TypeName_symm in H0. unfold QName in *. rewrite H0. simpl...
      }
      unfold QName in *. unfold cfun_bod in *. rewrite H2. simpl.
      apply IHl.
      destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]]. exists (l'++[a]). exists (l2'++[a0]).
      repeat (rewrite app_length). split...
      repeat (rewrite <- app_assoc). simpl. split...
Qed.

Lemma cfunbods_l_cfunsigs_l : forall p (x0 : ScopedName * list TypeName),
  In x0 (skeleton_ctors (program_skeleton p)) ->
  is_local (fst x0) ->
  map (fun x : QName * (ScopedName * expr) => local (fst x))
      (filter (gfunbods_filterfun_l (unscope (fst x0)))
              (flat_map
                 (fun x : QName * list (ScopedName * expr) =>
                  map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                 (program_cfun_bods_l p)))
= map (fun x : QName * list TypeName * TypeName => local (fst (fst x)))
      (filter (fun x1 : TypeName * Name * list TypeName * TypeName =>
               eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
              (skeleton_cfun_sigs_l (program_skeleton p))).
Proof with auto.
intros p x0 x0In Glob. pose proof (program_has_all_cfun_bods_l p) as H.
unfold has_all_cfun_bods in H.
rewrite <- map_map with (f:=fst).
change (fun x : QName * list TypeName * TypeName => local (fst (fst x)))
  with (fun y : QName * list TypeName * TypeName => (fun x => local (fst x)) (fst y)).
repeat (rewrite <- map_map with (f:=fst)). f_equal.
remember (program_cfun_bods_l p) as l.
remember (skeleton_cfun_sigs_l (program_skeleton p)) as l2.
assert (exists l' l2', length l' = length l2' /\
  l' ++ l = program_cfun_bods_l p /\
  l2' ++ l2 = skeleton_cfun_sigs_l (program_skeleton p)).
{ exists []. exists []... }
rewrite Heql in H. rewrite Heql2 in H.
clear Heql. clear Heql2. generalize dependent l2.
induction l.
- induction l2... intros H0.
  destruct H0 as [l' [l2' [Len [H1 H2]]]].
  apply (f_equal (length (A:=_))) in H. repeat (rewrite map_length in H).
  rewrite app_nil_r in H1. rewrite <- H1 in H. rewrite <- H2 in H.
  unfold cfun_bod_named in *. rewrite Len in H. rewrite app_length in H.
  simpl in H. omega.
- induction l2. intros H0.
  + destruct H0 as [l' [l2' [Len [H1 H2]]]].
    apply (f_equal (length (A:=_))) in H. repeat (rewrite map_length in H).
    rewrite app_nil_r in H2. rewrite <- H1 in H. rewrite <- H2 in H.
    unfold cfun_sig in *. rewrite <- Len in H. rewrite app_length in H.
    simpl in H. omega.
  + simpl. rewrite filter_app. rewrite map_app.
    case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst a0)))); intros.
    * unfold QName in *. rewrite H0. simpl.
      match goal with
        [ |- ?t = fst (fst a0) :: ?t2] => change (fst (fst a0) :: t2) with ([fst (fst a0)] ++ t2)
      end.
      rewrite IHl with (l2:=l2).
      2: {
        destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]]. exists (l'++[a]). exists (l2'++[a0]).
        repeat (rewrite app_length). split...
        repeat (rewrite <- app_assoc). simpl. split...
      }
      unfold QName in *. f_equal.
      assert (fst (fst a0) = fst a).
      { destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]].
        apply (f_equal (map fst)) in H1_1. apply (f_equal (map (fun x => fst (fst x)))) in H1_2.
        unfold QName in *. rewrite H in H1_2. rewrite <- H1_1 in H1_2.
        clear - H1_2 Len. generalize dependent l2'. induction l'; intros.
        - destruct l2'; try discriminate. simpl in H1_2. inversion H1_2. rewrite H0...
        - destruct l2'; try discriminate. apply IHl' with (l2':=l2')...
          simpl in H1_2. inversion H1_2... }
      unfold cfun_bod in *. unfold QName in *. rewrite <- H2.
      assert (exists l' l, l' ++ a :: l = program_cfun_bods_l p).
      { destruct H1. destruct H1. destruct H1. destruct H1. destruct H3.
        exists x. exists l...
      }
      apply filter_gfunbods_filterfun_l_unique_l with (p:=p) (x0:=x0)...
    * unfold QName in *. rewrite H0.
      assert (filter (gfunbods_filterfun_l (unscope (fst x0)))
        (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = nil).
      { clear - H0 H H1. unfold gfunbods_filterfun_l. induction (snd a)...
        simpl. destruct a. simpl. destruct q. destruct a1. destruct s...
        destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]].
        assert (t = fst (fst (fst a0))).
        { clear IHc.
          apply (f_equal (map fst)) in H1_1. apply (f_equal (map (fun x => fst (fst x)))) in H1_2.
          unfold QName in *. rewrite H in H1_2. rewrite <- H1_1 in H1_2.
          clear - H1_2 Len. generalize dependent l2'. induction l'; intros.
          - destruct l2'; try discriminate. simpl in H1_2. inversion H1_2. rewrite H0...
          - destruct l2'; try discriminate. apply IHl' with (l2':=l2')...
            simpl in H1_2. inversion H1_2...
        }
        subst. rewrite eq_TypeName_symm in H0. unfold QName in *. rewrite H0. simpl...
      }
      unfold QName in *. unfold cfun_bod in *. rewrite H2. simpl.
      apply IHl.
      destruct H1 as [l' [l2' [Len [H1_1 H1_2]]]]. exists (l'++[a]). exists (l2'++[a0]).
      repeat (rewrite app_length). split...
      repeat (rewrite <- app_assoc). simpl. split...
Qed.

Definition map_alternative_for_filter_l q d (x : cfun_bod_named) :=
  (fst x, from_some_default d
           (find (fun y =>
                  match fst y with
                  | local q' => eq_QName q q'
                  | _ => false
                  end) (snd x))).

Lemma cfun_bods_g_map_filter_l : forall p x0 (d : ScopedName * expr),
  In x0 (skeleton_ctors (program_skeleton p)) ->
  is_local (fst x0) ->
  filter (gfunbods_filterfun_l (unscope (fst x0)))
          (flat_map
            (fun x : QName * list (ScopedName * expr) =>
             map (fun y : ScopedName * expr => (fst x, y)) (snd x))
            (program_cfun_bods_g p)) =
  map (map_alternative_for_filter_l (unscope (fst x0)) d)
      (filter (fun x => eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
              (program_cfun_bods_g p)).
Proof with eauto.
intros. unfold map_alternative_for_filter_l.
assert (exists l', l' ++ program_cfun_bods_g p = program_cfun_bods_g p).
{ exists []... }
generalize H1. clear H1. generalize (program_cfun_bods_g p) at - 2.
induction c; intros... simpl.
case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst a))); intros.
- unfold QName in *. rewrite H2. simpl. rewrite filter_app.
  rewrite <- (app_nil_l (map _ (filter _ _))). rewrite app_comm_cons. f_equal.
  + rewrite combine_fst_snd. rewrite (combine_fst_snd (filter _ _)). f_equal.
    * destruct H1. eapply filter_gfunbods_filterfun_l_unique...
    * assert (exists a',
        filter (gfunbods_filterfun_l (unscope (fst x0)))
          (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = [a']).
      { case_eq (filter (gfunbods_filterfun_l (unscope (fst x0)))
         (map (fun y : ScopedName * expr => (fst a, y)) (snd a))); intros.
        - apply (f_equal (map fst)) in H3. destruct H1.
          erewrite filter_gfunbods_filterfun_l_unique in H3...
          simpl in H3. discriminate.
        - apply (f_equal (map fst)) in H3. destruct H1.
          erewrite filter_gfunbods_filterfun_l_unique in H3...
          destruct l; try discriminate. exists p0...
      }
      simpl. unfold cfun_bod in *. unfold QName in *. destruct H3. rewrite H3.
      generalize H3. clear.
      generalize ((@snd (prod TypeName Name) (list (prod ScopedName expr)) a)).
      induction l; intros; try discriminate. simpl. destruct a0. simpl.
      destruct s.
      -- simpl in H3. case_eq (eq_QName (unscope (fst x0)) q); intros.
         ++ rewrite H in H3. destruct a. destruct q0. simpl in *.
            case_eq (eq_TypeName t (fst (unscope (fst x0)))); intros.
            ** rewrite H0 in H3. simpl in *. inversion H3...
            ** rewrite H0 in H3. simpl in H3.
               pose proof (in_eq x []). rewrite <- H3 in H1.
               rewrite filter_In in H1. destruct H1.
               unfold gfunbods_filterfun_l in H2. destruct x. destruct p.
               destruct p0. destruct s; try discriminate.
               rewrite in_map_iff in H1. do 2 (destruct H1). inversion H1.
               subst. rewrite andb_true_iff in H2. rewrite (proj1 H2) in H0.
               discriminate.
         ++ rewrite H in H3. destruct a. destruct q0. simpl in H3.
            rewrite andb_false_r in H3.
            pose proof (in_eq x []). rewrite <- H3 in H0.
            rewrite filter_In in H0. destruct H0.
            unfold gfunbods_filterfun_g in H1. destruct x. destruct p.
            destruct p0. destruct s; try discriminate.
            rewrite in_map_iff in H0. do 2 (destruct H0). inversion H0.
            subst. apply IHl...
      -- simpl in IHl. apply IHl. simpl in H3. destruct a. simpl in H3.
         destruct q0...
  + apply IHc. destruct H1. exists (x++[a]). rewrite <- app_assoc...
- unfold QName in *. rewrite H2. rewrite filter_app.
  assert (filter (gfunbods_filterfun_l (unscope (fst x0)))
    (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = []).
  { clear - H2. induction (snd a)... simpl. destruct a. simpl.
    destruct q. destruct a0. destruct s... simpl in H2.
    rewrite eq_TypeName_symm in H2. rewrite H2... }
  unfold QName in *. unfold cfun_bod in *. rewrite H3. apply IHc.
  destruct H1. exists (x++[a]). rewrite <- app_assoc...
Qed.

Lemma cfun_bods_l_map_filter_l : forall p x0 (d : ScopedName * expr),
  In x0 (skeleton_ctors (program_skeleton p)) ->
  is_local (fst x0) ->
  filter (gfunbods_filterfun_l (unscope (fst x0)))
          (flat_map
            (fun x : QName * list (ScopedName * expr) =>
             map (fun y : ScopedName * expr => (fst x, y)) (snd x))
            (program_cfun_bods_l p)) =
  map (map_alternative_for_filter_l (unscope (fst x0)) d)
      (filter (fun x => eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
              (program_cfun_bods_l p)).
Proof with eauto.
intros. unfold map_alternative_for_filter_l.
assert (exists l', l' ++ program_cfun_bods_l p = program_cfun_bods_l p).
{ exists []... }
generalize H1. clear H1. generalize (program_cfun_bods_l p) at - 2.
induction c; intros... simpl.
case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst a))); intros.
- unfold QName in *. rewrite H2. simpl. rewrite filter_app.
  rewrite <- (app_nil_l (map _ (filter _ _))). rewrite app_comm_cons. f_equal.
  + rewrite combine_fst_snd. rewrite (combine_fst_snd (filter _ _)). f_equal.
    * destruct H1. eapply filter_gfunbods_filterfun_l_unique_l...
    * assert (exists a',
        filter (gfunbods_filterfun_l (unscope (fst x0)))
          (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = [a']).
      { case_eq (filter (gfunbods_filterfun_l (unscope (fst x0)))
         (map (fun y : ScopedName * expr => (fst a, y)) (snd a))); intros.
        - apply (f_equal (map fst)) in H3. destruct H1.
          erewrite filter_gfunbods_filterfun_l_unique_l in H3...
          simpl in H3. discriminate.
        - apply (f_equal (map fst)) in H3. destruct H1.
          erewrite filter_gfunbods_filterfun_l_unique_l in H3...
          destruct l; try discriminate. exists p0...
      }
      simpl. unfold cfun_bod in *. unfold QName in *. destruct H3. rewrite H3.
      generalize H3. clear.
      generalize ((@snd (prod TypeName Name) (list (prod ScopedName expr)) a)).
      induction l; intros; try discriminate. simpl. destruct a0. simpl.
      destruct s.
      -- simpl in H3. case_eq (eq_QName (unscope (fst x0)) q); intros.
         ++ rewrite H in H3. destruct a. destruct q0. simpl in *.
            case_eq (eq_TypeName t (fst (unscope (fst x0)))); intros.
            ** rewrite H0 in H3. simpl in *. inversion H3...
            ** rewrite H0 in H3. simpl in H3.
               pose proof (in_eq x []). rewrite <- H3 in H1.
               rewrite filter_In in H1. destruct H1.
               unfold gfunbods_filterfun_l in H2. destruct x. destruct p.
               destruct p0. destruct s; try discriminate.
               rewrite in_map_iff in H1. do 2 (destruct H1). inversion H1.
               subst. rewrite andb_true_iff in H2. rewrite (proj1 H2) in H0.
               discriminate.
         ++ rewrite H in H3. destruct a. destruct q0. simpl in H3.
            rewrite andb_false_r in H3.
            pose proof (in_eq x []). rewrite <- H3 in H0.
            rewrite filter_In in H0. destruct H0.
            unfold gfunbods_filterfun_g in H1. destruct x. destruct p.
            destruct p0. destruct s; try discriminate.
            rewrite in_map_iff in H0. do 2 (destruct H0). inversion H0.
            subst. apply IHl...
      -- simpl in IHl. apply IHl. simpl in H3. destruct a. simpl in H3.
         destruct q0...
  + apply IHc. destruct H1. exists (x++[a]). rewrite <- app_assoc...
- unfold QName in *. rewrite H2. rewrite filter_app.
  assert (filter (gfunbods_filterfun_l (unscope (fst x0)))
    (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = []).
  { clear - H2. induction (snd a)... simpl. destruct a. simpl.
    destruct q. destruct a0. destruct s... simpl in H2.
    rewrite eq_TypeName_symm in H2. rewrite H2... }
  unfold QName in *. unfold cfun_bod in *. rewrite H3. apply IHc.
  destruct H1. exists (x++[a]). rewrite <- app_assoc...
Qed.

Lemma lookup_l_cfun_nth : forall p tn sig n m1 d' d_a
  (x0 : ScopedName * list TypeName) (d_l0 :  QName * list TypeName * TypeName),
In x0 (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))) ->
m1 = globalize_aux
        (filter (gfunbods_filterfun_l (unscope (fst x0)))
           (flat_map
              (fun x : QName * list (ScopedName * expr) =>
               map (fun y : ScopedName * expr => (fst x, y)) (snd x))
              (program_cfun_bods_g p))) ->
n < length (filter (fun x : TypeName * Name * list (ScopedName * expr) =>
                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                    (program_cfun_bods_g p)) ->
lookup_cfun_sig_scoped (program_skeleton p)
  (fst (nth n m1
            (global (fst (map_alternative_for_filter_l (unscope (fst x0)) d' d_a)),
             snd (map_alternative_for_filter_l (unscope (fst x0)) d' d_a)))) = Some sig ->
nth n
  (filter
     (fun x1 : TypeName * Name * list TypeName * TypeName =>
      eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
     (skeleton_cfun_sigs_g (program_skeleton p) ++
      skeleton_cfun_sigs_l (program_skeleton p))) d_l0 = sig.
Proof with auto.
intros p tn sig n m1 d' d_a x0 d_l0 x0In H H0 H1. subst m1. unfold map_alternative_for_filter_l in H1. simpl in H1.
unfold globalize_aux in H1. rewrite <- map_nth in H1. simpl in H1.
rewrite map_map in H1. simpl in H1. unfold lookup_cfun_sig_scoped in H1.
rewrite <- map_map in H1. rewrite map_nth in H1. unfold lookup_cfun_sig_g in H1.
unfold lookup_cfun_sig_x in H1. rewrite filter_app.
pose proof (program_has_all_cfun_bods_g p) as Zip.
unfold has_all_cfun_bods in Zip.
assert (n < length
 (filter (fun x1 : TypeName * Name * list TypeName * TypeName =>
          eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
 (skeleton_cfun_sigs_g (program_skeleton p)))) as Len.
{ rewrite <- map_length with (f:=fun x : TypeName * Name * list TypeName * TypeName => fst (fst (fst x))).
  erewrite filter_ext.
  - rewrite filter_map. rewrite <- map_map. rewrite <- filter_map. rewrite map_length.
    unfold gfun_bod_named in *. unfold gfun_bod in *. unfold QName in *. rewrite Zip.
    rewrite <- filter_map. rewrite map_length. apply H0.
  - intros...
}
rewrite app_nth1... apply find_some in H1. destruct H1.
rewrite filter_In in x0In. destruct x0In.
unfold gfunsigs_filterfun_l in H3. destruct x0. destruct s; try discriminate.
pose proof (cfunbods_g_cfunsigs_l p (local q, l) H2 (Is_local_local _)) as Aux.
simpl in *. rewrite <- map_map in Aux.
change (fun x : QName * list TypeName * TypeName => global (fst (fst x)))
  with (fun y : QName * list TypeName * TypeName => (fun x => global (fst x)) (fst y)) in Aux.
rewrite <- (map_map fst) in Aux. rewrite <- (map_map fst) in Aux.
assert (forall l l', map global l = map global l' -> l = l') as Aux2.
{ clear. induction l; intros.
  - destruct l'... inversion H.
  - destruct l'; inversion H. f_equal...
}
apply Aux2 in Aux. rewrite Aux in H1. evar (d_ts : list TypeName). evar (d_t : TypeName).
replace (fst d_a) with ((fun x => fst (fst x)) (fst d_a, d_ts, d_t)) in H1...
rewrite map_map in H1.
change (fst (fst (fst d_a, d_ts, d_t))) with ((fun x => fst (fst x)) (fst d_a, d_ts, d_t)) in H1.
rewrite map_nth in H1. rewrite nth_indep with (d':=d_l0) in H1...
clear - H H1 Len. pose proof (nth_In _ d_l0 Len).
assert (In sig (filter (fun x : TypeName * Name * list TypeName * TypeName =>
                        eq_TypeName (fst q) (fst (fst (fst x))))
                       (skeleton_cfun_sigs_g (program_skeleton p)))) as sigIn.
{ clear - H H1 H0. rewrite filter_In. split...
  rewrite eq_QName_eq in H1. unfold QName in *. rewrite <- H1.
  rewrite filter_In in H0. destruct H0...
}
clear Len. pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
unfold gfun_sigs_names_unique in Uniq.
set (flt:=fun x1 : TypeName * Name => eq_TypeName (fst q) (fst x1)).
apply Unique.filter_unique with (f:=flt) in Uniq. rewrite <- filter_map in Uniq.
rewrite eq_QName_eq in H1.
generalize sigIn H1 H H0 Uniq. clear. generalize (skeleton_cfun_sigs_g (program_skeleton p)).
intros. unfold flt in *. unfold QName in *.
set (flt':=fun x1 : TypeName * Name * list TypeName * TypeName => eq_TypeName (fst q) (fst (fst (fst x1)))) in *.
unfold cfun_sig in *. unfold QName in *. generalize dependent (filter flt' c). clear.
intros. generalize dependent (nth n l d_l0). intros. generalize dependent p.
induction l; intros; [inversion sigIn |].
simpl in Uniq. inversion Uniq; subst. destruct H0.
- destruct sigIn; subst... exfalso. apply H3. apply in_map with (f:=fun x => fst (fst x)) in H0. rewrite H1...
- destruct sigIn; subst... exfalso. apply H3. apply in_map with (f:=fun x => fst (fst x)) in H. rewrite <- H1...
Unshelve. all:eauto.
Qed.

Lemma lookup_l_cfun_nth_l : forall p tn sig n m1 d' d_a
  (x0 : ScopedName * list TypeName) (d_l0 :  QName * list TypeName * TypeName),
In x0 (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))) ->
m1 = localize_aux
        (filter (gfunbods_filterfun_l (unscope (fst x0)))
           (flat_map
              (fun x : QName * list (ScopedName * expr) =>
               map (fun y : ScopedName * expr => (fst x, y)) (snd x))
              (program_cfun_bods_l p))) ->
n >= length (filter (fun x : TypeName * Name * list (ScopedName * expr) =>
                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                    (program_cfun_bods_g p)) ->
n - length (filter (gfunbods_filterfun_l (unscope (fst x0)))
                   (flat_map (fun x : QName * list (ScopedName * expr) =>
                      map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                          (program_cfun_bods_g p))) <
 length (filter (fun x : TypeName * Name * list (ScopedName * expr) =>
                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                    (program_cfun_bods_l p))  ->
lookup_cfun_sig_scoped (program_skeleton p)
  (fst (nth (n - length
                        (map
                           (fun x : QName * (ScopedName * expr) =>
                            switch_indices_aux (program_skeleton p)
                              (fst (global (fst x), snd x)) (length (snd x0)) tn
                              (snd (snd (global (fst x), snd x))))
                           (filter (gfunbods_filterfun_l (unscope (fst x0)))
                              (flat_map
                                 (fun x : QName * list (ScopedName * expr) =>
                                  map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                                 (program_cfun_bods_g p))))) m1
            (local (fst (map_alternative_for_filter_l (unscope (fst x0)) d' d_a)),
             snd (map_alternative_for_filter_l (unscope (fst x0)) d' d_a)))) = Some sig ->
nth n
  (filter
     (fun x1 : TypeName * Name * list TypeName * TypeName =>
      eq_TypeName (fst (unscope (fst  x0))) (fst (fst (fst x1))))
     (skeleton_cfun_sigs_g (program_skeleton p) ++
      skeleton_cfun_sigs_l (program_skeleton p))) d_l0 = sig.
Proof with auto.
intros p tn sig n m1 d' d_a x0 d_l0 x0In H H0 H0' H1. subst m1. unfold map_alternative_for_filter_l in H1. simpl in H1.
unfold localize_aux in H1. rewrite <- map_nth in H1. simpl in H1.
rewrite map_map in H1. simpl in H1. unfold lookup_cfun_sig_scoped in H1.
rewrite <- map_map in H1. rewrite map_nth in H1. unfold lookup_cfun_sig_l in H1.
unfold lookup_cfun_sig_x in H1. rewrite filter_app.
pose proof (program_has_all_cfun_bods_g p) as Zip.
unfold has_all_cfun_bods in Zip.
assert (n >= length
 (filter (fun x1 : TypeName * Name * list TypeName * TypeName =>
          eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
 (skeleton_cfun_sigs_g (program_skeleton p)))) as Len.
{ rewrite <- map_length with (f:=fun x : TypeName * Name * list TypeName * TypeName => fst (fst (fst x))).
  erewrite filter_ext.
  - rewrite filter_map. rewrite <- map_map. rewrite <- filter_map. rewrite map_length.
    unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite Zip.
    rewrite <- filter_map. rewrite map_length. apply H0.
  - intros...
}
rewrite app_nth2... apply find_some in H1. destruct H1.
rewrite filter_In in x0In. destruct x0In.
unfold gfunsigs_filterfun_g in H3. destruct x0. destruct s; try discriminate.
pose proof (cfunbods_l_cfunsigs_l p (local q, l) H2 (Is_local_local _)) as Aux.
simpl in *. rewrite <- map_map in Aux.
change (fun x : QName * list TypeName * TypeName => local (fst (fst x)))
  with (fun y : QName * list TypeName * TypeName => (fun x => local (fst x)) (fst y)) in Aux.
rewrite <- (map_map fst) in Aux. rewrite <- (map_map fst) in Aux.
assert (forall l l', map local l = map local l' -> l = l') as Aux2.
{ clear. induction l; intros.
  - destruct l'... inversion H.
  - destruct l'; inversion H. f_equal...
}
apply Aux2 in Aux. rewrite Aux in H1. evar (d_ts : list TypeName). evar (d_t :  TypeName).
replace (fst d_a) with (fst (fst (fst d_a, d_ts, d_t))) in H1...
repeat (rewrite map_nth in H1). clear Len.
assert (Len : n -
  length
    (map
       (fun x : QName * (ScopedName * expr) =>
        switch_indices_aux (program_skeleton p) (global (fst x)) (length l) tn (snd (snd x)))
       (filter (gfunbods_filterfun_l q)
         (flat_map
             (fun x : QName * list (ScopedName * expr) =>
              map (fun y : ScopedName * expr => (fst x, y)) (snd x))
             (program_cfun_bods_g p)))) <
  length
    (filter (fun x1 : TypeName * Name * list TypeName * TypeName => eq_TypeName (fst q) (fst (fst (fst x1))))
       (skeleton_cfun_sigs_l (program_skeleton p)))).
{ change q with (unscope (fst (local q, l))).
  erewrite cfun_bods_g_map_filter_l; try apply Is_local_local...
  repeat (rewrite map_length). rewrite <- sigs_bods_g_length.
  change q with (unscope (fst (local q, l))) in H0'.
  erewrite cfun_bods_g_map_filter_l in H0'; try apply Is_local_local...
  rewrite map_length in H0'.
  change q with (unscope (fst (local q, l))) in H0'.
  rewrite <- sigs_bods_g_length in H0'. rewrite <- sigs_bods_l_length in H0'...
}
rewrite nth_indep with (d':=d_l0) in H1...
clear - H H1 Len H2. pose proof (nth_In _ d_l0 Len).
assert (In sig (filter (fun x : TypeName * Name * list TypeName * TypeName =>
                        eq_TypeName (fst q) (fst (fst (fst x))))
                       (skeleton_cfun_sigs_l (program_skeleton p)))) as sigIn.
{ clear - H H1 H0. rewrite filter_In. split...
  rewrite eq_QName_eq in H1. unfold QName in *. rewrite <- H1.
  rewrite filter_In in H0. destruct H0...
}
clear Len. pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
unfold cfun_sigs_names_unique in Uniq.
set (flt:=fun x1 : TypeName * Name => eq_TypeName (fst q) (fst x1)).
apply Unique.filter_unique with (f:=flt) in Uniq. rewrite <- filter_map in Uniq.
rewrite eq_QName_eq in H1.
change q with (unscope (fst (local q, l))) in H1.
erewrite cfun_bods_g_map_filter_l in H1; try apply Is_local_local...  simpl in H1.
change q with (unscope (fst (local q, l))) in H0.
erewrite cfun_bods_g_map_filter_l in H0; try apply Is_local_local... simpl in H0.
repeat (rewrite map_length in H1). repeat (rewrite map_length in H0).
change q with (unscope (fst (local q, l))) in H1.
rewrite <- sigs_bods_g_length in H1. simpl in H1.
change q with (unscope (fst (local q, l))) in H0.
rewrite <- sigs_bods_g_length in H0. simpl in H0.
generalize sigIn H1 H H0 Uniq. clear. generalize (skeleton_cfun_sigs_l (program_skeleton p)).
intros. unfold flt in *. unfold QName in *.
set (flt':=fun x1 : TypeName * Name * list TypeName * TypeName => eq_TypeName (fst q) (fst (fst (fst x1)))) in *.
unfold cfun_sig in *. unfold QName in *. generalize dependent (filter flt' c). clear.
intros.
generalize dependent (nth (n - length (filter flt' (skeleton_cfun_sigs_g (program_skeleton p)))) l d_l0).
intros. generalize dependent p0.
induction l; intros; [inversion sigIn |].
simpl in Uniq. inversion Uniq; subst. destruct H0.
- destruct sigIn; subst... exfalso. apply H3. apply in_map with (f:=fun x => fst (fst x)) in H0. rewrite H1...
- destruct sigIn; subst... exfalso. apply H3. apply in_map with (f:=fun x => fst (fst x)) in H. rewrite <- H1...
Unshelve. all:eauto.
+ split; try exact (global q). exact (E_Var 0).
+ split; try exact (global q). exact (E_Var 0).
Qed.


Lemma new_gfunbods_l_typecheck_aux:
  forall (p : program) (tn : TypeName)
         (x0 : ScopedName * list TypeName),
    (forall x : expr,
              In x (map snd (flat_map snd (program_cfun_bods_g p))) ->
              no_matches tn x) ->
    (forall x : expr,
              In x (map snd (flat_map snd (program_cfun_bods_l p))) ->
              no_matches tn x) ->
    In x0
       (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))) ->
    forall (es : list expr) (ctxts : list (list TypeName)),
      es = map snd
        (map
           (fun x : ScopedName * (ScopedName * expr) =>
            (fst x,
            switch_indices_aux (program_skeleton p)
              (fst x) (length (snd x0)) tn
              (snd (snd x))))
           (globalize_aux
              (filter (gfunbods_filterfun_l (unscope (fst x0)))
                 (flat_map
                    (fun x : QName * list (ScopedName * expr) =>
                     map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                    (program_cfun_bods_g p)))) ++
         map
           (fun x : ScopedName * (ScopedName * expr) =>
            (fst x,
            switch_indices_aux (program_skeleton p)
              (fst x) (length (snd x0)) tn
              (snd (snd x))))
           (localize_aux
              (filter (gfunbods_filterfun_l (unscope (fst x0)))
                 (flat_map
                    (fun x : QName * list (ScopedName * expr) =>
                     map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                    (program_cfun_bods_l p))))) ->
      ctxts = map
           (fun dtor : ScopedName * list TypeName * TypeName =>
            snd (fst dtor) ++ snd x0)
           (map (fun x : QName * list TypeName * TypeName => (global (fst (fst x)), snd (fst x), snd x))
              (filter
                 (fun x1 : TypeName * Name * list TypeName * TypeName =>
                  eq_TypeName (fst (unscope (fst x0)))
                    (fst (fst (fst x1))))
                 (skeleton_cfun_sigs_g (program_skeleton p))) ++
            map (fun x : QName * list TypeName * TypeName => (local (fst (fst x)), snd (fst x), snd x))
              (filter
                 (fun x1 : TypeName * Name * list TypeName * TypeName =>
                  eq_TypeName (fst (unscope (fst x0)))
                    (fst (fst (fst x1))))
                 (skeleton_cfun_sigs_l (program_skeleton p)))) ->
      length ctxts = length es ->
      forall ts : list TypeName,
        ts = map snd
          (map
             (fun x : QName * list TypeName * TypeName =>
              (global (fst (fst x)), snd (fst x), snd x))
             (filter
                (fun x1 : TypeName * Name * list TypeName * TypeName =>
                 eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
                (skeleton_cfun_sigs_g (program_skeleton p))) ++
           map
             (fun x : QName * list TypeName * TypeName =>
              (local (fst (fst x)), snd (fst x), snd x))
             (filter
                (fun x1 : TypeName * Name * list TypeName * TypeName =>
                 eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
                (skeleton_cfun_sigs_l (program_skeleton p)))) ->
        length es = length ts ->
        (exists (l : list (list TypeName)) (l' : list expr)
                (l'' : list TypeName),
            length l = length l' /\
            length l' = length l'' /\
            l ++ ctxts = ctxts /\ l' ++ es = es /\ l'' ++ ts = ts) ->
        forall (a : expr) (es0 : list expr),
          (forall (ts0 : list TypeName) (ctxts0 : list (list TypeName)),
              (exists (l : list (list TypeName)) (l' : list expr)
                      (l'' : list TypeName),
                  length l = length l' /\
                  length l' = length l'' /\
                  l ++ ctxts0 = ctxts /\ l' ++ es0 = es /\ l'' ++ ts0 = ts) ->
              refunctionalize_to_skeleton p tn /// ctxts0 |||- es0 ::: ts0) ->
          forall (ts0 : list TypeName) (ctxts0 l : list (list TypeName))
                 (l' : list expr) (l'' : list TypeName),
            length l = length l' ->
            length l' = length l'' ->
            l ++ ctxts0 = ctxts ->
            l' ++ a :: es0 =
            map
              (fun x : ScopedName * (ScopedName * expr) =>
                 switch_indices_aux (program_skeleton p) (fst x)
                                    (length (snd x0)) tn (snd (snd x)))
              (globalize_aux
                 (filter (gfunbods_filterfun_l (unscope (fst x0)))
                         (flat_map
                            (fun x : QName * list (ScopedName * expr) =>
                               map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                            (program_cfun_bods_g p))) ++
                 localize_aux
                 (filter (gfunbods_filterfun_l (unscope (fst x0)))
                         (flat_map
                            (fun x : QName * list (ScopedName * expr) =>
                               map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                            (program_cfun_bods_l p)))) ->
            l'' ++ ts0 = ts ->
            forall (l0 : list TypeName) (l1 : list (list TypeName)),
              ctxts0 = l0 :: l1 ->
              forall (t : TypeName) (l2 : list TypeName),
                ts0 = t :: l2 ->
                refunctionalize_to_skeleton p tn / l0 |- a : t.
Proof with eauto.
  intros p tn x0 NoMatch_g NoMatch_l H6 es ctxts Heseq Hctxtseq Len1 ts Htseq Len2 H a es0 IHes0 ts0 ctxts0
    l l' l'' Len'1 Len'2 lEq l'Eq l''Eq l0 l1 H0 t l2 H1.
  set (Len:=length l' <?
                 length
                   (filter
                      (fun x : TypeName * Name * list (ScopedName * expr) =>
                         eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                      (program_cfun_bods_g p))).
                  match goal with [l'Eq : l' ++ a :: es0 = map _ (?m1' ++ ?m2') |- _] =>
                    set (m1 := m1') in *; set (m2:= m2') in * end.
                  evar (d_a : cfun_bod_named). evar (d' : (ScopedName * expr)%type).
                  set (fn := (fun y : ScopedName * (ScopedName * expr) =>
                    switch_indices_aux (program_skeleton p) (fst y) (length (snd x0)) tn (snd (snd y)))).
                  set (global_local:=if Len then global else local).
                  set (length_length:=if Len then length l' else
                    length l' - length (map
                     (fun x : QName * (ScopedName * expr) =>
                      switch_indices_aux (program_skeleton p)
                        (fst (global (fst x), snd x)) (length (snd x0)) tn
                        (snd (snd (global (fst x), snd x))))
                      (filter (gfunbods_filterfun_l (unscope (fst x0)))
                        (flat_map
                          (fun x : QName * list (ScopedName * expr) =>
                           map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                        (program_cfun_bods_g p))))).
                  set (m1_m2:=if Len then m1 else m2).
                  assert (aEq : a = nth length_length
                    (map (fun x => switch_indices_aux (program_skeleton p) (fst x) (length (snd x0))
                           tn (snd (snd x))) m1_m2)
                    (fn
                     ((fun x => (global_local (fst x), snd x))
                      (map_alternative_for_filter_l (unscope (fst x0)) d' d_a)))).
                  { evar (d'' : expr). apply (f_equal (fun x => nth (length l') x d'')) in l'Eq.
                    rewrite app_nth2 in l'Eq... rewrite Nat.sub_diag in l'Eq. simpl in l'Eq.
                    rewrite l'Eq. unfold fn. unfold d''. unfold d''.
                    case_eq Len; intros.
                    - unfold Len in *. unfold length_length.
                      unfold m1_m2. unfold m1. unfold globalize_aux. unfold localize_aux.
                      rewrite H2. rewrite map_app. rewrite map_map.
                      rewrite app_nth1... rewrite map_length. apply Nat.ltb_lt.
                      erewrite cfun_bods_g_map_filter_l; try rewrite map_length...
                      * rewrite filter_In in H6. destruct H6...
                      * rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                        destruct x0. destruct s; try discriminate.
                        apply Is_local_local.
                    - unfold Len in *. unfold length_length.
                      unfold m1_m2. unfold m1. unfold m2. unfold globalize_aux. unfold localize_aux.
                      rewrite H2. rewrite map_app. rewrite map_map.
                      rewrite app_nth2... rewrite map_length. apply Nat.ltb_ge.
                      erewrite cfun_bods_g_map_filter_l; try rewrite map_length...
                      * rewrite filter_In in H6. destruct H6...
                      * rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                        destruct x0. destruct s; try discriminate.
                        apply Is_local_local.
                  }
                  rewrite aEq. rewrite map_nth.
                  unfold switch_indices_aux.
                  match goal with [|- (_ / _ |- (refunctionalize_expr tn (proj1_sig ?s)) : _)] =>
                    set (switch' := s)
                  end.
                  destruct switch' as [switch Switch] eqn:switchEq. simpl.
                  apply refunctionalize_expr_preserves_typing.
                  +++ clear - switchEq.
                      replace switch with (proj1_sig switch').
                      2: { rewrite switchEq... }
                      match goal with
                      | [|- ?goal] => replace goal with (no_matches tn (proj1_sig switch'))
                      end...
                      apply switch_indices_no_match.
                      assert (forall x : expr,
                        In x ((map snd (flat_map snd (program_cfun_bods_g p ++ program_cfun_bods_l p)))) ->
                        no_matches tn x) as NoMatch.
                      { rewrite flat_map_concat_map. rewrite map_app. rewrite concat_app.
                        rewrite map_app. intros. repeat (rewrite <- flat_map_concat_map in H2).
                        apply in_app_or in H2. destruct H2; [apply NoMatch_g | apply NoMatch_l]...
                      }
                      apply NoMatch.
                      rewrite in_map_iff. eexists. apply and_comm.
                      rewrite in_flat_map. evar (d : (QName * list (ScopedName * expr))%type).
                      set (cfun_bods_g_l := program_cfun_bods_g p ++ program_cfun_bods_l p).
                      split.
                      *** exists (nth (length l') (filter
                           (fun x : TypeName * Name * cfun_bod =>
                            eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                           cfun_bods_g_l) d).
                          split.
                          ---- eapply proj1. rewrite <- filter_In. unfold length_length. unfold cfun_bods_g_l.
                               do 2 rewrite filter_app. case_eq Len; intros; unfold Len in *.
                               ++++ apply nth_In. rewrite Nat.ltb_lt in H2. rewrite app_length.
                                    unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. omega.
                               ++++ apply nth_In. apply (f_equal (@length _)) in Hctxtseq.
                                    rewrite map_length in Hctxtseq. rewrite app_length in Hctxtseq.
                                    repeat (rewrite map_length in Hctxtseq). rewrite <- app_length in Hctxtseq.
                                    apply (f_equal (@length _)) in lEq. rewrite Hctxtseq in lEq. rewrite H0 in lEq.
                                    rewrite <- Len'1. clear - lEq. rewrite app_length in lEq at 1. simpl in lEq.
                                    rewrite app_length in *.
                                    rewrite <- sigs_bods_g_length. rewrite <- sigs_bods_l_length.
                                    unfold QName in *. rewrite <- lEq. omega.
                          ---- shelve.
                      *** eauto. Unshelve. all:eauto. 3:{
                          unfold length_length in *. unfold m1_m2 in *.
                          unfold global_local in *. unfold cfun_bods_g_l in *.
                          case_eq Len; intros.
                          1:{
                          assert (Tmp2 : nth (length l')
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_g p ++ program_cfun_bods_l p)) d
                            = nth (length l')
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_g p)) d).
                          { rewrite filter_app. rewrite app_nth1... apply Nat.ltb_lt... }
                          rewrite Tmp2. unfold Len in *. clear Len. rename H2 into Len.
                          unfold m1. rewrite filter_In in H6. destruct H6.
                          unfold gfunsigs_filterfun_l in e. destruct x0. destruct s; try discriminate.
                          rewrite cfun_bods_g_map_filter_l with (d:=d'); try apply Is_local_local...
                          unfold globalize_aux. repeat (rewrite map_map). simpl.
                          match goal with [|- In (_ (_ _ (_ ?fn' _) ?dd')) _] =>
                            set (fn:=fn'); set (dd:=dd') end.
                          replace dd with (fn d_a)... rewrite map_nth.
                          unfold fn. simpl.
                          assert (forall {A} l f d (x : A), find f l = Some x ->
                            In (from_some_default d (find f l)) l).
                          { clear. intros. induction l; try discriminate.
                            simpl. destruct (f a) eqn:fEq; [left|]...
                            right. apply IHl. simpl in H. rewrite fEq in H...
                          }
                          rewrite Nat.ltb_lt in Len. rewrite nth_indep with (d':=d)...
                          match goal with [|- In (_ _ (_ ?f _)) ?l] => case_eq (find f l); intros end;
                           [apply H2 with (x:=p0)|]... exfalso.
                          pose proof (program_cfun_bods_typecheck_g p) as Typ.
                          unfold cfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
                          assert (In (nth (length l')
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst q) (fst (fst x)))
                              (program_cfun_bods_g p)) d) (program_cfun_bods_g p)).
                          { eapply proj1. rewrite <- filter_In. apply nth_In... }
                          apply Typ in H4. do 4 (destruct H4). inversion H5; subst.
                          apply listTypeDeriv'_lemma_ctx in H19. do 2 (rewrite map_length in H19).
                          rewrite Nat.eqb_eq in H19. clear - (**)Len(**) H3 H17 H18 H19. unfold lookup_ctors in H17.
                          match goal with
                          | _ : match ?dstr with _ => _ end = _ |- _ => destruct dstr
                          end; try discriminate. inversion H17; subst. clear H17.
                          rewrite Forall_forall in H18. evar (d_c : (ScopedName * list TypeName)%type).
                          pose proof (conj i e) as FilterAux.
                          change (eq_TypeName tn (fst q)) with
                           ((fun x => eq_TypeName tn (fst (unscope (fst x)))) (local q, l3))
                           in FilterAux.
                          rewrite <- filter_In in FilterAux.
                          apply In_nth with (d:=d_c) in FilterAux. destruct FilterAux as [n [nEq nthEq]].
                          evar (d_e : (ScopedName * expr)%type). set (nth_e := nth n
                            (snd (nth (length l')  (filter
                              (fun x0 : TypeName * Name * cfun_bod =>
                               eq_TypeName tn (fst (fst x0))) (program_cfun_bods_g p)) d)) d_e).
                          apply find_none with (x:=(local q, snd nth_e)) in H3;
                            [simpl in H3; rewrite eq_QName_refl in H3; discriminate|].
                          apply (f_equal fst) in nthEq. simpl in nthEq.
                          rewrite <- nthEq.
                          assert (fst (nth n (filter
                            (fun x : ScopedName * list TypeName =>
                             eq_TypeName tn (fst (unscope (fst x))))
                            (skeleton_ctors (program_skeleton p))) d_c) = fst nth_e).
                          { unfold nth_e. symmetry.
                            rewrite eq_TypeName_eq in e. subst tn.
                            match goal with [|- fst (_ _ ?lhs _) = fst (_ _ ?rhs _)] =>
                              specialize H18 with (x:=(nth n lhs d_e, nth n rhs d_c));
                              set (LenAux':=length lhs=length rhs)
                            end.
                            assert LenAux' as LenAux.
                            { unfold LenAux'. clear LenAux'. unfold QName in *. unfold cfun_bod in *.
                              rewrite <- H19. f_equal. apply filter_ext. intros. destruct a0.
                              match goal with [|- _ _ (_ (_ (_ _ ?fltrd' _))) = _] => set (fltrd:=fltrd') end.
                              assert (In (nth (length l') fltrd d) fltrd).
                              { apply nth_In. simpl in Len. unfold fltrd... }
                              unfold fltrd in H0. rewrite filter_In in H0. destruct H0.
                              symmetry. unfold fltrd. rewrite eq_TypeName_eq in H1. rewrite <- H1.
                              apply eq_TypeName_symm.
                            }
                            rewrite <- combine_nth in H18...
                            match goal with [_ : In ?x (combine ?l1 ?l2) -> _ |- _] =>
                              set (H' := In x (combine l1 l2)) end.
                            assert H'. { unfold H'. clear H'.
                            match goal with [|- In (_ _ (_ (_ (_ _ ?fltrd' _)) _) _) _] => set (fltrd:=fltrd') end.
                            assert (In (nth (length l') fltrd d) fltrd).
                            { apply nth_In. simpl in Len. unfold fltrd... }
                            erewrite filter_ext with (f:=fun x : ScopedName * list TypeName
                              => let (n0, _) := x in eq_TypeName _ _).
                            - apply nth_In. unfold fltrd in *.
                              rewrite combine_length. rewrite <- H19. erewrite filter_ext.
                              + rewrite Nat.min_id...
                              + intros. destruct a0. rewrite eq_TypeName_symm. f_equal.
                                rewrite filter_In in H0. destruct H0. symmetry. apply eq_TypeName_eq...
                            - intros. destruct a0. rewrite eq_TypeName_symm. f_equal.
                              unfold fltrd in *. rewrite filter_In in H0. destruct H0.
                              rewrite eq_TypeName_eq in H1... }
                            unfold H' in *. apply H18 in H0. rewrite combine_nth in H0...
                            match goal with [|- fst ?lhs' = fst ?rhs'] =>
                              set (lhs:=lhs') in *; set (rhs:=rhs') in * end.
                            destruct lhs. destruct rhs...
                          }
                          unfold ctor in *. rewrite H0. rewrite <- surjective_pairing.
                          unfold nth_e. rewrite eq_TypeName_eq in e. subst tn.
                          apply nth_In. rewrite <- H19. erewrite filter_ext; [apply nEq|].
                          intros. destruct a0. simpl. rewrite eq_TypeName_symm. f_equal.
                          match goal with [|- fst (fst (_ _ ?fltrd' _)) = _] => set (fltrd:=fltrd') end.
                          assert (In (nth (length l') fltrd d) fltrd).
                          { apply nth_In. simpl in Len. unfold fltrd... }
                          unfold fltrd in H1. rewrite filter_In in H1. destruct H1.
                          symmetry. unfold fltrd. apply eq_TypeName_eq...
                          }

                          1:{
                          set (lngth:=length l' -
                            length
                              (map
                                (fun x : QName * (ScopedName * expr) =>
                                 switch_indices_aux (program_skeleton p) (fst (global (fst x), snd x))
                                 (length (snd x0)) tn (snd (snd (global (fst x), snd x))))
                              (filter (gfunbods_filterfun_l (unscope (fst x0)))
                                (flat_map
                                  (fun x : QName * list (ScopedName * expr) =>
                                   map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                                (program_cfun_bods_g p))))).
                          assert (Tmp : lngth < length (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_l p))).
                          { unfold lngth in *. clear lngth. unfold Len in *. rewrite <- Len'1 in *.
                            erewrite cfun_bods_g_map_filter_l.
                            2:{ rewrite filter_In in H6. destruct H6... }
                            2:{ rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                                destruct x0. destruct s; try discriminate. apply Is_local_local. }
                            rewrite H0 in lEq. rewrite Hctxtseq in lEq. rewrite Nat.ltb_ge in H2.
                            apply (f_equal (@length _)) in lEq. rewrite map_length in *.
                            repeat (rewrite app_length in lEq). simpl in lEq.
                            repeat (rewrite map_length in lEq). rewrite map_length.
                            clear switch' switchEq Switch length_length m1_m2. clear - lEq H2.
                            erewrite filter_ext in lEq.
                            - rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                              erewrite filter_ext with (l0:=skeleton_cfun_sigs_l _) in lEq.
                              + rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                                rewrite (program_has_all_cfun_bods_g p) in lEq.
                                rewrite (program_has_all_cfun_bods_l p) in lEq.
                                repeat (rewrite <- filter_map in lEq). repeat (rewrite map_length in lEq).
                                erewrite filter_ext in lEq;
                                  [ erewrite filter_ext with (l0:=program_cfun_bods_l _) in lEq |].
                                * generalize lEq. clear lEq.
                                  do 2 instantiate (1:=fun x : TypeName * Name * cfun_bod =>
                                    eq_TypeName (fst (unscope (fst x0))) (fst (fst x))).
                                  intros. eapply plus_lt_reg_l. unfold cfun_bod_named in *. unfold cfun_bod in *.
                                  unfold QName in *. rewrite <- lEq. omega.
                                * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                                    with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                                * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                                    with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                              + eauto.
                            - eauto.
                          }
                          assert (Tmp2 : nth lngth
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_l p)) d
                            = nth (length l')
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                                    (program_cfun_bods_g p ++ program_cfun_bods_l p)) d).
                          { unfold lngth in *. rewrite filter_app. rewrite app_nth2.
                            - erewrite cfun_bods_g_map_filter_l.
                              + rewrite map_map. rewrite map_length...
                              + rewrite filter_In in H6. destruct H6...
                              + rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_g in e.
                                destruct x0. destruct s; try discriminate. apply Is_local_local.
                            - unfold Len in H2. apply Nat.ltb_ge...
                          }
                          rewrite <- Tmp2. unfold Len in *. clear Len. rename H2 into Len.
                          unfold m2. rewrite filter_In in H6. destruct H6.
                          unfold gfunsigs_filterfun_l in e. destruct x0. destruct s; try discriminate.
                          rewrite cfun_bods_l_map_filter_l with (d:=d'); try apply Is_local_local...
                          unfold localize_aux. repeat (rewrite map_map). simpl.
                          match goal with [|- In (_ (_ _ (_ ?fn' _) ?dd')) _] =>
                            set (fn:=fn'); set (dd:=dd') end.
                          replace dd with (fn d_a)... rewrite map_nth.
                          unfold fn. simpl.
                          assert (forall {A} l f d (x : A), find f l = Some x ->
                            In (from_some_default d (find f l)) l).
                          { clear. intros. induction l; try discriminate.
                            simpl. destruct (f a) eqn:fEq; [left|]...
                            right. apply IHl. simpl in H. rewrite fEq in H...
                          }
                          rewrite nth_indep with (d':=d)...
                          match goal with [|- In (_ _ (_ ?f _)) ?l] => case_eq (find f l); intros end;
                           [apply H2 with (x:=p0)|]... exfalso.
                          pose proof (program_cfun_bods_typecheck_l p) as Typ.
                          unfold cfun_bods_l_typecheck in Typ. rewrite Forall_forall in Typ.
                          assert (In (nth lngth
                            (filter (fun x : TypeName * Name * cfun_bod =>
                                     eq_TypeName (fst q) (fst (fst x)))
                              (program_cfun_bods_l p)) d) (program_cfun_bods_l p)).
                          { eapply proj1. rewrite <- filter_In. apply nth_In... }
                          apply Typ in H4. do 4 (destruct H4). inversion H5; subst.
                          apply listTypeDeriv'_lemma_ctx in H19. do 2 (rewrite map_length in H19).
                          rewrite Nat.eqb_eq in H19. clear - (**)Len(**) H3 H17 H18 H19 i e Tmp. unfold lookup_ctors in H17.
                          match goal with
                          | _ : match ?dstr with _ => _ end = _ |- _ => destruct dstr
                          end; try discriminate. inversion H17; subst. clear H17.
                          rewrite Forall_forall in H18. evar (d_c : (ScopedName * list TypeName)%type).
                          pose proof (conj i e) as FilterAux.
                          change (eq_TypeName tn (fst q)) with
                           ((fun x => eq_TypeName tn (fst (unscope (fst x)))) (local q, l3))
                           in FilterAux.
                          rewrite <- filter_In in FilterAux.
                          apply In_nth with (d:=d_c) in FilterAux. destruct FilterAux as [n [nEq nthEq]].
                          evar (d_e : (ScopedName * expr)%type). set (nth_e := nth n
                            (snd (nth lngth  (filter
                              (fun x0 : TypeName * Name * cfun_bod =>
                               eq_TypeName tn (fst (fst x0))) (program_cfun_bods_l p)) d)) d_e).
                          apply find_none with (x:=(local q, snd nth_e)) in H3;
                            [simpl in H3; rewrite eq_QName_refl in H3; discriminate|].
                          apply (f_equal fst) in nthEq. simpl in nthEq.
                          rewrite <- nthEq.
                          assert (fst (nth n (filter
                            (fun x : ScopedName * list TypeName =>
                             eq_TypeName tn (fst (unscope (fst x))))
                            (skeleton_ctors (program_skeleton p))) d_c) = fst nth_e).
                          { unfold nth_e. symmetry.
                            rewrite eq_TypeName_eq in e. subst tn.
                            match goal with [|- fst (_ _ ?lhs _) = fst (_ _ ?rhs _)] =>
                              specialize H18 with (x:=(nth n lhs d_e, nth n rhs d_c));
                              set (LenAux':=length lhs=length rhs)
                            end.
                            assert LenAux' as LenAux.
                            { unfold LenAux'. clear LenAux'. unfold QName in *. unfold cfun_bod in *.
                              rewrite <- H19. f_equal. apply filter_ext. intros. destruct a0.
                              match goal with [|- _ _ (_ (_ (_ _ ?fltrd' _))) = _] => set (fltrd:=fltrd') end.
                              assert (In (nth lngth fltrd d) fltrd).
                              { apply nth_In. unfold lngth. unfold fltrd... }
                              unfold fltrd in H0. rewrite filter_In in H0. destruct H0.
                              symmetry. unfold fltrd. rewrite eq_TypeName_eq in H1. rewrite <- H1.
                              apply eq_TypeName_symm.
                            }
                            rewrite <- combine_nth in H18...
                            match goal with [_ : In ?x (combine ?l1 ?l2) -> _ |- _] =>
                              set (H' := In x (combine l1 l2)) end.
                            assert H'. { unfold H'. clear H'.
                            match goal with [|- In (_ _ (_ (_ (_ _ ?fltrd' _)) _) _) _] => set (fltrd:=fltrd') end.
                            assert (In (nth lngth fltrd d) fltrd).
                            { apply nth_In. unfold lngth. unfold fltrd... }
                            erewrite filter_ext with (f:=fun x : ScopedName * list TypeName
                              => let (n0, _) := x in eq_TypeName _ _).
                            - apply nth_In. unfold fltrd in *.
                              rewrite combine_length. rewrite <- H19. erewrite filter_ext.
                              + rewrite Nat.min_id...
                              + intros. destruct a0. rewrite eq_TypeName_symm. f_equal.
                                rewrite filter_In in H0. destruct H0. symmetry. apply eq_TypeName_eq...
                            - intros. destruct a0. rewrite eq_TypeName_symm. f_equal.
                              unfold fltrd in *. rewrite filter_In in H0. destruct H0.
                              rewrite eq_TypeName_eq in H1... }
                            unfold H' in *. apply H18 in H0. rewrite combine_nth in H0...
                            match goal with [|- fst ?lhs' = fst ?rhs'] =>
                              set (lhs:=lhs') in *; set (rhs:=rhs') in * end.
                            destruct lhs. destruct rhs...
                          }
                          unfold ctor in *. rewrite H0. rewrite <- surjective_pairing.
                          unfold nth_e. rewrite eq_TypeName_eq in e. subst tn.
                          apply nth_In. rewrite <- H19. erewrite filter_ext; [apply nEq|].
                          intros. destruct a0. simpl. rewrite eq_TypeName_symm. f_equal.
                          match goal with [|- fst (fst (_ _ ?fltrd' _)) = _] => set (fltrd:=fltrd') end.
                          assert (In (nth lngth fltrd d) fltrd).
                          { apply nth_In. unfold lngth. unfold fltrd... }
                          unfold fltrd in H1. rewrite filter_In in H1. destruct H1.
                          symmetry. unfold fltrd. apply eq_TypeName_eq...
                          } } all:shelve.
                  +++ assert (exists sig, lookup_cfun_sig_scoped (program_skeleton p)
                        (fst (nth length_length m1_m2 (global_local (fst
                          (map_alternative_for_filter_l (unscope (fst x0)) d' d_a)),
                           snd (map_alternative_for_filter_l (unscope (fst x0)) d' d_a)))) =
                        Some sig) as SwitchAux1.
                      { unfold length_length. unfold m1_m2. unfold global_local.
                        case_eq Len; intros; unfold Len in *.
                        - unfold m1. rewrite <- map_nth. simpl.
                          unfold globalize_aux. rewrite map_map. simpl.
                          match goal with [|- exists _, _ _ ?nth' = _] => set (nthSn:=nth') end.
                          assert (In nthSn (map (fun x => global (fst x)) (program_cfun_bods_g p))).
                          { unfold nthSn. erewrite cfun_bods_g_map_filter_l.
                            2: { rewrite filter_In in H6. destruct H6... }
                            2: { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                                 destruct x0. destruct s; try discriminate. apply Is_local_local.
                            }
                          rewrite map_map. simpl. change (global (fst d_a))
                          with ((fun x => global (fst x)) d_a). rewrite map_nth.
                          match goal with [|- In (_ (_ ?y)) _] =>
                            change (global (fst y)) with ((fun x => global (fst x)) y) end.
                          apply in_map. eapply proj1. rewrite <- filter_In. apply nth_In.
                          apply Nat.ltb_lt...
                          }
                          rewrite <- map_map in H3. rewrite in_map_iff in H3. do 2 (destruct H3).
                          pose proof (program_has_all_cfun_bods_g p) as Zip.
                          unfold has_all_cfun_bods in Zip. rewrite <- Zip in H4.
                          unfold lookup_cfun_sig_scoped. rewrite <- H3. unfold lookup_cfun_sig_g.
                          unfold lookup_cfun_sig_x. case_eq (find (fun sig => eq_QName x (fst (fst sig)))
                            (skeleton_cfun_sigs_g (program_skeleton p))); intros...
                          rewrite in_map_iff in H4. do 2 (destruct H4).
                          apply find_none with (x:=x1) in H5... rewrite H4 in H5.
                          rewrite eq_QName_refl in H5. discriminate.
                        - unfold m2. rewrite <- map_nth. simpl.
                          unfold localize_aux. rewrite map_map. simpl.
                          match goal with [|- exists _, _ _ ?nth' = _] => set (nthSn:=nth') end.
                          assert (In nthSn (map (fun x => local (fst x)) (program_cfun_bods_l p))).
                          { unfold nthSn. erewrite cfun_bods_l_map_filter_l.
                            2: { rewrite filter_In in H6. destruct H6... }
                            2: { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                                 destruct x0. destruct s; try discriminate. apply Is_local_local.
                            }
                            rewrite map_map. simpl. change (local (fst d_a))
                            with ((fun x => local (fst x)) d_a). rewrite map_nth.
                            match goal with [|- In (_ (_ ?y)) _] =>
                              change (local (fst y)) with ((fun x => local (fst x)) y) end.
                            apply in_map. eapply proj1. rewrite <- filter_In. apply nth_In.
                            unfold Len in *. rewrite <- Len'1 in *.
                            erewrite cfun_bods_g_map_filter_l.
                            2:{ rewrite filter_In in H6. destruct H6... }
                            2:{ rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                                destruct x0. destruct s; try discriminate. apply Is_local_local. }
                            rewrite H0 in lEq. rewrite Hctxtseq in lEq. rewrite Nat.ltb_ge in H2.
                            apply (f_equal (@length _)) in lEq. rewrite map_length in *.
                            repeat (rewrite app_length in lEq). simpl in lEq.
                            repeat (rewrite map_length in lEq). rewrite map_length.
                            clear switch' switchEq Switch length_length aEq m1_m2. clear - lEq H2.
                            erewrite filter_ext in lEq.
                            - rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                              erewrite filter_ext with (l0:=skeleton_cfun_sigs_l _) in lEq.
                              + rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                                rewrite (program_has_all_cfun_bods_g p) in lEq.
                                rewrite (program_has_all_cfun_bods_l p) in lEq.
                                repeat (rewrite <- filter_map in lEq). repeat (rewrite map_length in lEq).
                                erewrite filter_ext in lEq;
                                  [ erewrite filter_ext with (l0:=program_cfun_bods_l _) in lEq |].
                                * generalize lEq. clear lEq.
                                  do 2 instantiate (1:=fun x : TypeName * Name * cfun_bod =>
                                    eq_TypeName (fst (unscope (fst x0))) (fst (fst x))).
                                  intros. eapply plus_lt_reg_l. unfold cfun_bod_named in *. unfold cfun_bod in *.
                                  unfold QName in *. rewrite <- lEq. omega.
                                * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                                    with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                                * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                                    with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                              + eauto.
                            - eauto.
                          }
                          rewrite <- map_map in H3. rewrite in_map_iff in H3. do 2 (destruct H3).
                          pose proof (program_has_all_cfun_bods_l p) as Zip.
                          unfold has_all_cfun_bods in Zip. rewrite <- Zip in H4.
                          unfold lookup_cfun_sig_scoped. rewrite <- H3. unfold lookup_cfun_sig_l.
                          unfold lookup_cfun_sig_x. case_eq (find (fun sig => eq_QName x (fst (fst sig)))
                            (skeleton_cfun_sigs_l (program_skeleton p))); intros...
                          rewrite in_map_iff in H4. do 2 (destruct H4).
                          apply find_none with (x:=x1) in H5... rewrite H4 in H5.
                          rewrite eq_QName_refl in H5. discriminate.
                      }

                      assert (Tmp : Len = false ->
                        length l' -
                            length
                              (map
                                (fun x : QName * (ScopedName * expr) =>
                                 switch_indices_aux (program_skeleton p)
                                  (fst (global (fst x), snd x)) (length (snd x0)) tn
                                  (snd (snd (global (fst x), snd x))))
                                (filter (gfunbods_filterfun_l (unscope (fst x0)))
                                   (flat_map
                                     (fun x : QName * list (ScopedName * expr) =>
                                      map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                                   (program_cfun_bods_g p)))) <
                          length (filter (fun x : TypeName * Name * cfun_bod =>
                            eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                            (program_cfun_bods_l p))).
                      { intros. unfold Len in *. rewrite <- Len'1 in *.
                        erewrite cfun_bods_g_map_filter_l.
                        2:{ rewrite filter_In in H6. destruct H6... }
                        2:{ rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                        destruct x0. destruct s; try discriminate. apply Is_local_local. }
                        rewrite H0 in lEq. rewrite Hctxtseq in lEq.
                        apply (f_equal (@length _)) in lEq. rewrite map_length in *.
                        repeat (rewrite app_length in lEq). simpl in lEq.
                        repeat (rewrite map_length in lEq). rewrite map_length.
                        clear switch' switchEq Switch length_length m1_m2 aEq SwitchAux1. clear - lEq H2.
                        erewrite filter_ext in lEq.
                        - rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                          erewrite filter_ext with (l0:=skeleton_cfun_sigs_l _) in lEq.
                          + rewrite <- map_length with (f:=fun x => fst (fst x)) in lEq. rewrite filter_map in lEq.
                            rewrite (program_has_all_cfun_bods_g p) in lEq.
                            rewrite (program_has_all_cfun_bods_l p) in lEq.
                            repeat (rewrite <- filter_map in lEq). repeat (rewrite map_length in lEq).
                            erewrite filter_ext in lEq;
                              [ erewrite filter_ext with (l0:=program_cfun_bods_l _) in lEq |].
                            * generalize lEq. clear lEq.
                              do 2 instantiate (1:=fun x : TypeName * Name * cfun_bod =>
                              eq_TypeName (fst (unscope (fst x0))) (fst (fst x))).
                              intros. eapply plus_lt_reg_l. unfold cfun_bod_named in *. unfold cfun_bod in *.
                              unfold QName in *. rewrite <- lEq. rewrite Nat.ltb_ge in H2. omega.
                            * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                               with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                            * intros. simpl. change (eq_TypeName (fst (unscope (fst x0))) (fst (fst a)))
                               with ((fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst a))...
                          + eauto.
                        - auto.
                      }

                      destruct SwitchAux1 as [sig SwitchAux1].
                      apply Switch with (sig:=sig)...
                      { evar (d_l0 : (QName * list TypeName * TypeName)%type).
                        replace l0 with (nth (length l') ctxts
                          ((fun x => snd x ++ snd x0) (fst d_l0))).
                        2:{ rewrite <- lEq. rewrite <- Len'1. rewrite app_nth2...
                            rewrite H0. rewrite Nat.sub_diag... }
                        replace sig with (nth (length l') (filter
                          (fun x1 : TypeName * Name * list TypeName * TypeName =>
                           eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
                          (skeleton_cfun_sigs_g (program_skeleton p) ++
                           skeleton_cfun_sigs_l (program_skeleton p))) d_l0).
                        2: { unfold length_length in *. unfold m1_m2 in *. unfold global_local in *.
                          case_eq Len; intros; unfold Len in *; rewrite H2 in *.
                          - rewrite Nat.ltb_lt in H2. eapply lookup_l_cfun_nth...
                          - rewrite Nat.ltb_ge in H2.
                            eapply lookup_l_cfun_nth_l... rewrite map_length in Tmp...
                        }
                        subst ctxts. rewrite map_app. repeat (rewrite map_map). simpl.
                        rewrite <- map_app. rewrite <- filter_app.
                        change (snd (fst d_l0) ++ snd x0)
                        with ((fun x => snd (fst x) ++ snd x0) d_l0). rewrite map_nth.
                        rewrite app_length. rewrite plus_comm...
                      }
                      clear switch switchEq Switch SwitchAux1 sig.
                      rewrite map_nth in aEq.
                      set (bods_gl := if Len then program_cfun_bods_g else program_cfun_bods_l).
                      assert (aEq' : a =
                        switch_indices_aux (program_skeleton p)
                          (global_local (fst (nth length_length
                            (filter
                              (fun x : TypeName * Name * cfun_bod =>
                               eq_TypeName (fst (unscope (fst x0)))
                              (fst (fst x))) (bods_gl p)) d_a)))
                          (length (snd x0)) tn
                          (snd
                            (from_some_default d'
                              (find
                                (fun y : ScopedName * expr =>
                                 match fst y with
                                 | global _ => false
                                 | local q' => eq_QName (unscope (fst x0)) q'
                                 end)
                          (snd (nth length_length
                            (filter
                              (fun x : TypeName * Name * cfun_bod =>
                               eq_TypeName (fst (unscope (fst x0)))
                            (fst (fst x))) (bods_gl p)) d_a)))))).
                      { unfold m1_m2 in *. unfold global_local in *. unfold length_length in *.
                        unfold bods_gl in *.
                        case_eq Len; intros; rewrite H2 in aEq; unfold m1 in *; unfold m2 in *.
                        - rewrite cfun_bods_g_map_filter_l with (d:=d') in aEq.
                          2: { rewrite filter_In in H6. destruct H6... }
                          2: { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                               destruct x0. destruct s; try discriminate. apply Is_local_local.
                          }
                          unfold globalize_aux in aEq. rewrite map_map in aEq.
                          change (global (fst (map_alternative_for_filter_l (unscope (fst x0))
                                              d' d_a)),
                                 snd  (map_alternative_for_filter_l (unscope (fst x0)) d' d_a))
                          with ((fun x => (global (fst (map_alternative_for_filter_l (unscope (fst x0))
                                                    d' x)),
                                      snd (map_alternative_for_filter_l (unscope (fst x0)) d' x))) d_a)
                          in aEq.
                          rewrite map_nth in aEq...
                        - rewrite cfun_bods_l_map_filter_l with (d:=d') in aEq.
                          2: { rewrite filter_In in H6. destruct H6... }
                          2: { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in e.
                               destruct x0. destruct s; try discriminate. apply Is_local_local.
                          }
                          unfold localize_aux in aEq. rewrite map_map in aEq.
                          change (local (fst (map_alternative_for_filter_l (unscope (fst x0))
                                              d' d_a)),
                                 snd  (map_alternative_for_filter_l (unscope (fst x0)) d' d_a))
                          with ((fun x => (local (fst (map_alternative_for_filter_l (unscope (fst x0))
                                                    d' x)),
                                      snd (map_alternative_for_filter_l (unscope (fst x0)) d' x))) d_a)
                          in aEq.
                          rewrite map_nth in aEq...
                      }
                      clear aEq. rename aEq' into aEq.
                      match goal with
                        [aEq : a = switch_indices_aux _ _ _ _ (snd (_ _ (_ _ (snd ?a'_0)))) |- _] =>
                         set (a':=a'_0) in * end.
                      assert (In a' (bods_gl p)) as Typ.
                      { unfold a'. eapply proj1. rewrite <- filter_In. apply nth_In.
                        unfold length_length. unfold bods_gl. case_eq Len; intros.
                        - apply Nat.ltb_lt...
                        - apply Tmp in H2...
                      }
                      pose proof (program_cfun_bods_typecheck_g p) as H3.
                      unfold cfun_bods_g_typecheck in H3. rewrite Forall_forall in H3.
                      pose proof (program_cfun_bods_typecheck_l p) as H3_l.
                      unfold cfun_bods_l_typecheck in H3_l. rewrite Forall_forall in H3_l.
                      assert (exists qn ctx t (ctorlist : list (ScopedName * list TypeName))
                        (bindings_exprs : list expr)
                        (bindings_types : list TypeName),
                        (if Len then lookup_cfun_sig_g else lookup_cfun_sig_l) (program_skeleton p) (fst a')
                          = Some (qn, ctx, t) /\
                        program_skeleton p //  (fst (fst a') :: ctx) ||- bindings_exprs :: bindings_types /\
                        index_list 1 ctx = combine bindings_exprs bindings_types /\
                        lookup_ctors (program_skeleton p) (fst (fst a')) = Some ctorlist /\
                        Forall
                         (fun x : ScopedName * expr * (ScopedName * list TypeName) =>
                          let (y, y0) := x in
                          let (sn, _) := y in
                          let (sn', _) := y0 in sn = sn')
                         (combine (snd a') ctorlist) /\
                        program_skeleton p ///
                          map (fun ctor : ScopedName * list TypeName =>
                               snd ctor ++ bindings_types) ctorlist |||-
                          map snd (snd a') ::: repeat t (length (snd a'))) as TypStuff.
                      { unfold bods_gl in Typ.
                        case_eq Len; intros; rewrite H2 in Typ.
                        - apply H3 in Typ. destruct Typ as [qn [args [t0 [SigLookup Typ]]]].
                          inversion Typ. subst qn0 t0 bindings cases prog.
                          do 6 eexists. repeat split; eauto.
                        - apply H3_l in Typ. destruct Typ as [qn [args [t0 [SigLookup Typ]]]].
                          inversion Typ. subst qn0 t0 bindings cases prog.
                          do 6 eexists. repeat split; eauto.
                      }
                      destruct TypStuff as [qn [ctx [t0 [ctorlist [bindings_exprs [bindings_types
                        [SigLookup [H4 [H5 [H7 [H8 H13]]]]]]]]]]].

                      match goal with [H13 : _ /// ?mctxt' |||- _ ::: _ |- _] =>
                          set (mctxt := mctxt') in * end.

                      pose proof H6 as H6'.
                      replace (filter (gfunsigs_filterfun_l tn)
                          (skeleton_ctors (program_skeleton p))) with
                        (filter (fun x => eq_TypeName tn (fst (unscope (fst x)))
                                  && match (fst x) with local _ => true | _ => false end)
                          (skeleton_ctors (program_skeleton p))) in H6.
                      2: { apply filter_ext. intros. unfold gfunsigs_filterfun_l.
                           destruct a0.
                           destruct s; simpl; try rewrite andb_false_r...
                           rewrite andb_true_r... }
                      rewrite <- filter_compose in H6. rewrite filter_filter in H6.
                      rewrite filter_In in H6. apply proj1 in H6.
                      apply in_split in H6. destruct H6 as [l_init [l_tail H6]].
                      unfold lookup_ctors in H7.
                      case_eq (filter (eq_TypeName (fst (fst a')))
                        (skeleton_dts (program_skeleton p))); intros;
                        unfold cfun_bod in *; rewrite H2 in H7; try discriminate.
                      inversion H7.
                      assert (fst (fst a') = tn) as tnEq.
                      { unfold a'. rewrite filter_In in H6'. destruct H6'.
                        unfold gfunsigs_filterfun_l in H11. destruct x0.
                        destruct s; try discriminate. rewrite eq_TypeName_eq in H11. subst tn.
                        simpl. unfold length_length in *. unfold bods_gl in *. case_eq Len; intros.
                        - unfold Len in H11. rewrite Nat.ltb_lt in H11.
                          pose proof (nth_In _ d_a H11).
                          rewrite filter_In in H12. destruct H12. simpl in H14.
                          unfold length_length in H14.
                          symmetry. apply eq_TypeName_eq...
                        - apply Tmp in H11. pose proof (nth_In _ d_a H11).
                          rewrite filter_In in H12. destruct H12. simpl in H14.
                          symmetry. apply eq_TypeName_eq...
                      }
                      match goal with [|- (_ / _ |- ?e' : _)] => set (e:=e') end.
                      assert (snda'Eq : exists es_0 es_0', length es_0 = length l_init /\
                        map snd (snd a') = es_0 ++ e :: es_0').
                      { exists (firstn (length l_init) (map snd (snd a'))).
                        exists (skipn (S (length l_init)) (map snd (snd a'))).
                        assert (length (firstn (S (length l_init)) (map snd (snd a'))) = S (length l_init))
                          as LenAux.
                        { rewrite firstn_length. apply Nat.min_l. subst ctorlist.
                          apply listTypeDeriv'_lemma_ctx in H13. rewrite beq_nat_true_iff in H13.
                          unfold cfun_bod. rewrite <- H13. unfold mctxt. rewrite map_length.
                          erewrite filter_ext.
                          - rewrite H6. rewrite app_length. simpl. omega.
                          - intros. destruct a0. rewrite <- tnEq. rewrite eq_TypeName_symm...
                        }
                        assert (x0Global : is_local (fst x0)).
                        { clear - H6'. rewrite filter_In in H6'. destruct H6'.
                          unfold gfunsigs_filterfun_l in H0. destruct x0. simpl.
                          destruct s; try discriminate. apply Is_local_local.
                        }
                        split.
                        - clear - LenAux. generalize dependent (map snd (snd a')).
                          generalize dependent (length l_init).
                          induction n; intros; try rewrite firstn_O...
                          simpl. destruct l3; try discriminate. simpl. rewrite IHn...
                        - rewrite <- firstn_skipn with (n:=S (length l_init)) at 1.
                          rewrite <- (app_nil_l (skipn _ _)) at 2. rewrite app_comm_cons.
                          rewrite app_assoc. f_equal.
                          rewrite firstn_nth with
                            (d:=snd (snd (map_alternative_for_filter (unscope (fst x0)) d' d_a)))...
                          f_equal. f_equal. unfold e. unfold a'.
                          unfold m1_m2. unfold m1. unfold m2.

                          change (snd (snd
                            (map_alternative_for_filter (unscope (fst x0)) d' d_a)))
                          with ((fun x => snd (snd x))
                            (map_alternative_for_filter (unscope (fst x0)) d' d_a)).
                          unfold global_local in *.
                          match goal with [|- _ = _ (_ (_ _ _ ((if Len then global else local) ?l, ?r)))] =>
                            replace ((if Len then global else local) l, r) with
                              (if Len then (global l, r) else (local l, r))
                          end.
                          2:{ destruct Len... }
                          match goal with
                            [|- _ = _ (_ (_ _ (if Len then globalize_aux (?la (?lb ?lc))
                              else localize_aux (?ra (?rb ?rc))) _))] =>
                            replace (if Len then globalize_aux (la (lb lc))
                              else localize_aux (ra (rb rc)))
                            with ((if Len then globalize_aux else localize_aux) (la (lb (bods_gl p))))
                          end.
                          2: { destruct Len... }
                          simpl.
                          assert (LenInEq : length_length < length
                            (filter
                              (fun x : TypeName * Name * list (ScopedName * expr) =>
                               eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                              (bods_gl p))).
                          { unfold length_length in *. unfold bods_gl in *.
                            case_eq Len; intros; unfold Len in *... apply Nat.ltb_lt...
                          }
                          clear LenAux. generalize LenInEq. generalize (length_length).
                          assert (exists g', bods_gl p = g' ++ bods_gl p) as gEq.
                          { exists []... }
                          generalize gEq. clear gEq. unfold globalize_aux in *.
                          generalize (bods_gl p) at - 1. generalize dependent l_init.
                          unfold m1 in *. unfold m2 in *. unfold m1_m2 in *.
                          unfold bods_gl in *. generalize Len.
                          generalize x0Global. generalize x0. generalize l_tail.
                          clear H3 H IHes0 Len1 Len2 es Heseq lEq ctxts Hctxtseq l''Eq ts Htseq l'Eq e
                            switch' Len'1 Len'2 H0 H1 LenInEq aEq.
                          clear. clear a es0 ts0 ctxts0 l l'' l0 l1 t l2.
                          generalize d_a. generalize d'. clear. induction c; intros.
                          + simpl in LenInEq. omega.
                          + simpl.
                            case_eq (eq_TypeName (fst (unscope (fst x0))) (fst (fst a))); intros.
                            * unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
                              rewrite H.
                              assert (exists qn, forall d', filter (gfunbods_filterfun_l (unscope (fst x0)))
                                (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) =
                                [(qn, nth (length l_init) (snd a) d')]) as H0.
                              { exists (fst a). intros. unfold gfunbods_filterfun_l. clear - H6 H gEq x0Global.
                                match goal with [_ : ?flt' = l_init ++ _ |- _] => set (flt:=flt') end.
                                assert (forall dx, x0 = nth (length l_init) flt dx) as H0.
                                { unfold flt. rewrite H6. intros. rewrite app_nth2... rewrite Nat.sub_diag... }
                                evar (dx : (ScopedName * list TypeName)%type).
                                rewrite H0 with (dx:=dx).
                                erewrite filter_ext.
                                - erewrite <- filter_compose.
                                  match goal with [|- _ ?f' (filter ?g0' ?m') = _] =>
                                    set (g0:=g0'); set (f:=f'); set (m:=m') end.
                                  replace (filter g0 m) with m.
                                  2: {
                                    assert (forall me, In me m -> g0 me = true).
                                    { intros. unfold m in H1. rewrite in_map_iff in H1.
                                      do 2 (destruct H1). subst me.
                                      match goal with [H : eq_TypeName ?e1 (fst (fst a)) = _ |- _] =>
                                        change (eq_TypeName e1 (fst (fst a))) with
                                          ((fun x => eq_TypeName e1 (fst (fst x))) (fst a, x)) in H
                                      end.
                                      unfold g0...
                                    }
                                    unfold g0. induction m... simpl. rewrite <- IHm.
                                    - unfold g0 in H1. rewrite H1... apply in_eq.
                                    - intros. apply H1. apply in_cons...
                                  }
                                  assert (tnEq : tn = fst (unscope (fst x0))).
                                  { assert (In x0 (l_init ++ x0 :: l_tail)).
                                    { clear. induction l_init; try apply in_eq; try apply in_cons... }
                                    rewrite <- H6 in H1. rewrite filter_In in H1. destruct H1.
                                    rewrite eq_TypeName_eq in H2...
                                  }
                                  assert (map fst (snd a) = map fst (l_init ++ x0 :: l_tail)).
                                  { pose proof (program_cfun_bods_typecheck_g p) as H3.
                                    unfold cfun_bods_g_typecheck in H3. rewrite Forall_forall in H3.
                                    pose proof (program_cfun_bods_typecheck_l p) as H3_l.
                                    unfold cfun_bods_l_typecheck in H3_l. rewrite Forall_forall in H3_l.

                                    assert (exists ctx t (ctorlist : list (ScopedName * list TypeName))
                                      (bindings_exprs : list expr)
                                      (bindings_types : list TypeName),
                                      program_skeleton p // (fst (fst a) :: ctx) ||- bindings_exprs :: bindings_types /\
                                      index_list 1 ctx = combine bindings_exprs bindings_types /\
                                      lookup_ctors (program_skeleton p) (fst (fst a)) = Some ctorlist /\
                                      Forall
                                       (fun x : ScopedName * expr * (ScopedName * list TypeName) =>
                                        let (y, y0) := x in
                                        let (sn, _) := y in
                                        let (sn', _) := y0 in sn = sn')
                                        (combine (snd a) ctorlist) /\
                                        program_skeleton p ///
                                          map (fun ctor : ScopedName * list TypeName =>
                                               snd ctor ++ bindings_types) ctorlist |||-
                                          map snd (snd a) ::: repeat t (length (snd a))) as TypStuff.
                                    { destruct gEq.
                                      case_eq Len; intros; rewrite H1 in e.
                                      - assert (In a (program_cfun_bods_g p)) as Typ.
                                        { rewrite e. clear. induction x; try apply in_eq... right... }
                                        apply H3 in Typ. destruct Typ as [qn [args [t0 [_ Typ]]]].
                                        inversion Typ. subst qn0 t0 bindings cases prog.
                                        do 5 eexists. repeat split; eauto.
                                      - assert (In a (program_cfun_bods_l p)) as Typ.
                                        { rewrite e. clear. induction x; try apply in_eq... right... }
                                        apply H3_l in Typ. destruct Typ as [qn [args [t0 [_ Typ]]]].
                                        inversion Typ. subst qn0 t0 bindings cases prog.
                                        do 5 eexists. repeat split; eauto.
                                    }
                                    destruct TypStuff as [ctx [t0 [ctorlist [bindings_exprs [bindings_types
                                      [H4 [H5 [H11 [H12 H13]]]]]]]]].

                                    rewrite <- H6.
                                    unfold lookup_ctors in H11.
                                    case_eq (filter (eq_TypeName (fst (fst a)))
                                      (skeleton_dts (program_skeleton p)));
                                     intros; unfold QName in *; rewrite H1 in H11; try discriminate.
                                    inversion H11; subst. rewrite eq_TypeName_eq in H. rewrite H.
                                    clear - H12 H13. apply listTypeDeriv'_lemma_ctx in H13.
                                    repeat (rewrite map_length in H13). rewrite Nat.eqb_eq in H13.
                                    generalize H12 H13. clear. generalize (skeleton_ctors (program_skeleton p)).
                                    intros. evar (g : ScopedName * list TypeName -> bool).
                                    rewrite filter_ext with (g0:=g);
                                     [rewrite filter_ext with (g0:=g) in H13|];
                                     [rewrite filter_ext with (g0:=g) in H12 | |].
                                    - generalize dependent (snd a). generalize dependent (filter g c).
                                      unfold g in *. clear g.
                                      induction l; intros l0 H Len; destruct l0; try discriminate...
                                      simpl in *. inversion Len. inversion H. subst. rewrite IHl...
                                      destruct p0. destruct a0. subst...
                                    - unfold g in *. intros. destruct a0.
                                      instantiate (1:=fun x =>
                                        eq_TypeName (fst (unscope (fst x))) (fst (fst a)))...
                                    - unfold g in *. intros. destruct a0...
                                    - unfold g in *. intros. destruct a0... apply eq_TypeName_symm.
                                  }
                                  assert (In (fst a, nth (length l_init) (snd a) d'0) m).
                                  { unfold m. rewrite in_map_iff. exists (nth (length l_init) (snd a) d'0).
                                    split... apply nth_In. apply (f_equal (@length _)) in H1.
                                    repeat (rewrite map_length in H1). rewrite app_length in H1.
                                    simpl in H1. omega.
                                  }
                                  assert (f (fst a, nth (length l_init) (snd a) d'0) = true).
                                  { assert (fst (nth (length l_init) (snd a) d'0) = fst x0).
                                    { rewrite <- map_nth. rewrite H1. repeat (rewrite map_app).
                                      rewrite app_nth2; try repeat (rewrite map_length)...
                                      rewrite Nat.sub_diag...
                                    }
                                    symmetry in H3. rewrite <- eq_ScopedName_eq in H3.
                                    match goal with [_ : eq_ScopedName ?e1 (fst ?e2) = _ |- _] =>
                                      change (eq_ScopedName e1 (fst e2)) with
                                        ((fun x => eq_ScopedName e1 (fst (snd x))) (fst a, e2)) in H3
                                    end.
                                    unfold f...
                                  }
                                  pose proof (conj H2 H3). rewrite <- filter_In in H4.
                                  apply in_split in H4. do 2 destruct H4.
                                  destruct x; [destruct x1 |]...
                                  + simpl in *. unfold QName in *.
                                    unfold m in H4. apply (f_equal (map snd)) in H4. simpl in H4.
                                    unfold f in H4. change
                                      (fun x : TypeName * Name * (ScopedName * expr) =>
                                       eq_ScopedName (fst x0) (fst (snd x))) with
                                      (fun x : TypeName * Name * (ScopedName * expr) =>
                                       (fun y => eq_ScopedName (fst x0) (fst y)) (snd x)) in H4.
                                    rewrite filter_map in H4. rewrite map_map in H4. simpl in H4.
                                    rewrite map_id in H4. apply (f_equal (map fst)) in H4.
                                    rewrite filter_map in H4. rewrite H1 in H4. rewrite <- H6 in H4.
                                    change
                                      (fun x : ScopedName * list TypeName =>
                                       eq_TypeName tn (fst (unscope (fst x)))) with
                                      (fun x : ScopedName * list TypeName =>
                                       (fun y => eq_TypeName tn (fst (unscope y))) (fst x)) in H4.
                                    rewrite filter_map in H4. rewrite filter_compose in H4.
                                    subst. exfalso. clear - H4. generalize H4.
                                    generalize (nth (length l_init) (snd a) d'0). clear.
                                    pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
                                    unfold dts_ctor_names_unique in Uniq. generalize Uniq.
                                    generalize (map fst (skeleton_ctors (program_skeleton p))).
                                    clear. induction l; intros; try discriminate.
                                    inversion Uniq; subst. simpl in H4.
                                    case_eq (eq_ScopedName (fst x0) a); intros.
                                    * rewrite eq_ScopedName_eq in H. subst. rewrite eq_ScopedName_refl in H4.
                                      rewrite eq_TypeName_refl in H4. simpl in H4. inversion H4.
                                      pose proof (in_eq (fst (snd p0)) (map fst (map snd x1))).
                                      rewrite <- H3 in H. rewrite filter_In in H. destruct H.
                                      rewrite andb_true_iff in H5. destruct H5. rewrite eq_ScopedName_eq in H5.
                                      rewrite <- H5 in H...
                                    * rewrite H in H4. simpl in H4. simpl in IHl. eapply IHl...
                                  + simpl in *. unfold QName in *.
                                    unfold m in H4. apply (f_equal (map snd)) in H4. simpl in H4.
                                    unfold f in H4. change
                                      (fun x : TypeName * Name * (ScopedName * expr) =>
                                       eq_ScopedName (fst x0) (fst (snd x))) with
                                      (fun x : TypeName * Name * (ScopedName * expr) =>
                                       (fun y => eq_ScopedName (fst x0) (fst y)) (snd x)) in H4.
                                    rewrite filter_map in H4. rewrite map_map in H4. simpl in H4.
                                    rewrite map_id in H4. apply (f_equal (map fst)) in H4.
                                    rewrite filter_map in H4. rewrite H1 in H4. rewrite <- H6 in H4.
                                    change
                                      (fun x : ScopedName * list TypeName =>
                                       eq_TypeName tn (fst (unscope (fst x)))) with
                                      (fun x : ScopedName * list TypeName =>
                                       (fun y => eq_TypeName tn (fst (unscope y))) (fst x)) in H4.
                                    rewrite filter_map in H4. rewrite filter_compose in H4.
                                    subst. exfalso. clear - H4. generalize H4.
                                    generalize (nth (length l_init) (snd a) d'0). clear.
                                    pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
                                    unfold dts_ctor_names_unique in Uniq. generalize Uniq.
                                    generalize (map fst (skeleton_ctors (program_skeleton p))).
                                    clear. induction l; intros; try discriminate.
                                    inversion Uniq; subst. simpl in H4.
                                    case_eq (eq_ScopedName (fst x0) a0); intros.
                                    * rewrite eq_ScopedName_eq in H. subst. rewrite eq_ScopedName_refl in H4.
                                      rewrite eq_TypeName_refl in H4. simpl in H4. inversion H4.
                                      rewrite map_app in H4. simpl in H4.
                                      assert (In (fst p) (map fst (map snd x ++ p :: map snd x1))).
                                      { clear. rewrite in_map_iff. exists p. split...
                                        induction (map snd x); try apply in_eq. right...
                                      }
                                      rewrite map_app in H3. simpl in H3. rewrite <- H3 in H.
                                      rewrite filter_In in H. destruct H.
                                      rewrite andb_true_iff in H5. destruct H5. rewrite eq_ScopedName_eq in H5.
                                      rewrite <- H5 in H...
                                    * rewrite H in H4. simpl in H4. simpl in IHl. eapply IHl...
                                - intros. inversion x0Global. destruct a0. destruct q. destruct p0.
                                  simpl. destruct s... rewrite <- H0. rewrite <- H2.
                                  rewrite eq_TypeName_symm. rewrite andb_comm...
                              }
                              destruct H0 as [qn H0]. rewrite filter_app.
                              match goal with [|- _ = _ (_ (_ _ ((if Len then ?la else ?lb) (?lc1 ++ ?lc2)) _))] =>
                                replace ((if Len then la else lb) (lc1 ++ lc2))
                                with (((if Len then la else lb) lc1) ++ ((if Len then la else lb) lc2))
                              end.
                              2:{ unfold localize_aux. destruct Len; rewrite map_app... }
                              unfold QName in *. erewrite H0. case_eq Len; intros; rewrite H1 in *.
                              -- destruct length_length; simpl; [ rewrite map_nth|]...
                                 apply IHc.
                                 ++ destruct gEq as [g' gEq]. exists (g'++[a]). rewrite <- app_assoc...
                                 ++ simpl in LenInEq. rewrite H in LenInEq. simpl in LenInEq. omega.
                              -- destruct length_length; simpl; [ rewrite map_nth|]...
                                 apply IHc.
                                 ++ destruct gEq as [g' gEq]. exists (g'++[a]). rewrite <- app_assoc...
                                 ++ simpl in LenInEq. rewrite H in LenInEq. simpl in LenInEq. omega.
                            * unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
                              rewrite H.
                              assert (filter (gfunbods_filterfun_l (unscope (fst x0)))
                                (map (fun y : ScopedName * expr => (fst a, y)) (snd a)) = []) as H0.
                              { induction (snd a)... simpl. destruct a. destruct p0. destruct a0. simpl.
                                destruct s... simpl in *. rewrite eq_TypeName_symm. rewrite H... }
                              rewrite filter_app.
                              match goal with [|- _ = _ (_ (_ _ ((if Len then ?la else ?lb) (?lc1 ++ ?lc2)) _))] =>
                                replace ((if Len then la else lb) (lc1 ++ lc2))
                                with (((if Len then la else lb) lc1) ++ ((if Len then la else lb) lc2))
                              end.
                              2:{ unfold localize_aux. destruct Len; rewrite map_app... }
                              unfold QName in *. rewrite H0. case_eq Len; intros; rewrite H1 in *.
                              -- apply IHc.
                                 ++ destruct gEq as [g' gEq]. exists (g'++[a]). rewrite <- app_assoc...
                                 ++ simpl in LenInEq. rewrite H in LenInEq...
                              -- apply IHc.
                                 ++ destruct gEq as [g' gEq]. exists (g'++[a]). rewrite <- app_assoc...
                                 ++ simpl in LenInEq. rewrite H in LenInEq...
                      }

                      assert (mctxtEq : exists m0 m0', length m0 = length l_init /\
                        mctxt = m0 ++ (switch_indices_ctx l0 (length (snd x0))) :: m0').
                      { exists (firstn (length l_init) mctxt).
                        exists (skipn (S (length l_init)) mctxt).
                        assert (length (firstn (S (length l_init)) mctxt) = S (length l_init))
                          as LenAux.
                        { rewrite firstn_length. apply Nat.min_l.
                          unfold mctxt. subst ctorlist. rewrite map_length.
                          erewrite filter_ext.
                          + rewrite H6. rewrite app_length. simpl. omega.
                          + intros. destruct a0. simpl.
                            rewrite <- tnEq. apply eq_TypeName_symm.
                        }
                        split.
                        - clear - LenAux. generalize dependent mctxt.
                          generalize dependent (length l_init).
                          induction n; intros; try rewrite firstn_O...
                          simpl. destruct mctxt; try discriminate. simpl. rewrite IHn...
                        - rewrite <- firstn_skipn with (n:=S (length l_init)) at 1.
                          rewrite <- (app_nil_l (skipn _ _)) at 2. rewrite app_comm_cons.
                          rewrite app_assoc. f_equal.
                          evar (dctor : (ScopedName * list TypeName)%type).
                          rewrite firstn_nth with (d:=snd dctor ++ bindings_types)... subst ctorlist.
                          evar (ddtor : (ScopedName * list TypeName * TypeName)%type).
                          f_equal. f_equal.
                          replace l0 with (nth (length l) ctxts (snd (fst ddtor) ++ snd x0)).
                          2: { rewrite <- lEq. rewrite app_nth2...
                               rewrite Nat.sub_diag. rewrite H0... }
                          subst ctxts. unfold mctxt.
                          change (snd dctor ++ bindings_types) with
                           ((fun x => snd x ++ bindings_types) dctor).
                          rewrite map_nth.
                          change (snd (fst ddtor) ++ snd x0) with
                            ((fun x => snd (fst x) ++ snd x0) ddtor).
                          rewrite map_nth.
                          erewrite filter_ext; [rewrite H6|].
                          2: { intros. destruct a0. simpl.
                               rewrite eq_TypeName_symm. f_equal...
                          }
                          rewrite app_nth2... rewrite Nat.sub_diag. simpl.
                          match goal with [|- _ = _ (?lhs' ++ ?rhs') _] =>
                            set (lhs:=lhs'); set (rhs:=rhs')
                          end.
                          assert (switch_indices_ctx (lhs ++ rhs) (length rhs)
                            = rhs ++ lhs) as Switch.
                          { unfold switch_indices_ctx. generalize rhs lhs. clear.
                            induction rhs; intros.
                            - simpl. rewrite app_nil_r at 1. rewrite Nat.sub_0_r.
                              rewrite skipn_all_app. simpl. rewrite app_nil_r.
                              rewrite Nat.sub_0_r. apply firstn_all.
                            - repeat (rewrite app_length). simpl. rewrite Nat.add_sub.
                              rewrite skipn_all_app. simpl. f_equal.
                              rewrite <- IHrhs. rewrite firstn_app. rewrite Nat.sub_diag.
                              rewrite firstn_all. rewrite firstn_O. rewrite app_nil_r.
                              rewrite app_length. rewrite Nat.add_sub.
                              rewrite skipn_all_app. rewrite firstn_app.
                              rewrite firstn_all. rewrite Nat.sub_diag. rewrite firstn_O.
                              rewrite app_nil_r...
                          }
                          rewrite Switch. unfold lhs. unfold rhs. clear lhs rhs Switch.
                          f_equal.
                          unfold lookup_cfun_sig_g in SigLookup.
                          unfold lookup_cfun_sig_l in SigLookup.
                          unfold lookup_cfun_sig_x in SigLookup.
                          assert (bindings_types = ctx).
                          { apply listTypeDeriv_lemma in H4. clear - H4 H5.
                            rewrite Nat.eqb_eq in H4. generalize dependent bindings_types.
                            generalize dependent bindings_exprs. generalize dependent 0.
                            induction ctx; intros.
                            - simpl in H5. destruct bindings_types...
                              destruct bindings_exprs; discriminate.
                            - simpl in *. destruct bindings_types.
                              + destruct bindings_exprs; try discriminate.
                              + destruct bindings_exprs; try discriminate. f_equal.
                                * simpl in *. inversion H5; subst...
                                * inversion H5; subst. eapply IHctx...
                          }
                          subst bindings_types. unfold cfun_sig in *. unfold QName in *.
                          match goal with [H : ((if Len then ?f1 else ?f2) ?ps ?fa) = _ |- _] =>
                            set (f1':=f1) in H; set (f2':=f2) in H;
                            set (ps':=ps) in H; set (fa':=fa) in H
                          end.
                          assert ((if Len then f1' else f2') ps' fa'
                           = if Len then f1' ps' fa' else f2' ps' fa') as  SigLookupEq.
                          { destruct Len... }
                          rewrite SigLookupEq in SigLookup. clear SigLookupEq.
                          unfold f1' in *. unfold f2' in *.
                          match goal with [H : (if Len then ?f1 ?sg else ?f1 ?sl) = _ |- _] =>
                            replace (if Len then f1 sg else f1 sl)
                            with (f1 (if Len then sg else sl)) in H
                          end.
                          2:{ destruct Len... }
                          apply find_some in SigLookup. rewrite eq_QName_eq in SigLookup.
                          simpl in SigLookup. rewrite <- (proj2 SigLookup) in SigLookup.
                          apply proj1 in SigLookup.
                          apply (In_nth _ _ ((fun x => (unscope (fst (fst x)), snd (fst x), snd x)) ddtor))
                           in SigLookup.
                          destruct SigLookup as [x [xLen ctxEq]]. pose proof ctxEq as ctxEq'.
                          apply (f_equal (fun x => snd (fst x))) in ctxEq. simpl in ctxEq. rewrite <- ctxEq.
                          assert (LenSigs : length_length < length (filter
                            (fun x1 : TypeName * Name * list TypeName * TypeName =>
                             eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
                            ((if Len then skeleton_cfun_sigs_g else skeleton_cfun_sigs_l)
                             (program_skeleton p)))).
                          { unfold length_length in *. case_eq Len; intros; unfold Len in *.
                            - rewrite sigs_bods_g_length. apply Nat.ltb_lt...
                            - apply Tmp in H9. rewrite sigs_bods_l_length...
                          }
                          unfold length_length in *.
                          case_eq Len; intros; rewrite H9 in *.
                          + rewrite app_nth1.
                            2: { rewrite map_length. rewrite Len'1... }
                            pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p))
                            as Uniq.
                            unfold cfun_sigs_names_unique in Uniq.
                            match goal with [|- snd (fst ?lhs') = snd (fst ?rhs')] =>
                              set (lhs:=lhs'); set (rhs:=rhs') end.
                            set (rhs':=(fun x => (unscope (fst (fst x)), snd (fst x), snd x)) rhs).
                            replace (snd (fst rhs)) with (snd (fst rhs'))...
                            assert (In lhs (skeleton_cfun_sigs_g (program_skeleton p))).
                            { unfold lhs. apply nth_In... }
                            assert (In rhs' (skeleton_cfun_sigs_g (program_skeleton p))).
                            { unfold rhs'. set (rhs_fn:=fun x : ScopedName * list TypeName * TypeName
                                => (unscope (fst (fst x)), snd (fst x), snd x)).
                              change (unscope (fst (fst rhs)), snd (fst rhs), snd rhs) with (rhs_fn rhs).
                              unfold rhs. rewrite <- map_nth. rewrite map_map.
                              unfold rhs_fn. simpl.
                              rewrite map_ext with (g:=id); try (symmetry; repeat (rewrite <- surjective_pairing))...
                              rewrite map_id. eapply proj1. rewrite <- filter_In.
                              apply nth_In. rewrite Len'1...
                            }
                            assert (fst (fst lhs) = fst (fst rhs')).
                            { unfold lhs. unfold rhs'. unfold rhs. rewrite ctxEq'. simpl.
                              unfold fa'. unfold a'. rewrite <- map_nth. rewrite <- Len'1.
                              unfold bods_gl. rewrite H9.
                              erewrite filter_ext.
                              - rewrite filter_map.
                                pose proof (program_has_all_cfun_bods_g p) as Zip.
                                unfold has_all_cfun_bods in Zip.
                                unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
                                rewrite <- Zip. rewrite <- (map_nth _ _ ddtor).
                                rewrite map_map. simpl. rewrite <- map_nth with (d:=fst ddtor).
                                rewrite map_map. simpl. rewrite <- map_nth with (d:=fst (fst ddtor)).
                                rewrite map_map. simpl.
                                change (fun y : TypeName * Name * list TypeName * TypeName =>
                                  eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst y)))) with
                                  (fun y : TypeName * Name * list TypeName * TypeName =>
                                    (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x))
                                    ((fun z => fst (fst z)) y)).
                                rewrite filter_map. apply nth_indep.
                                unfold QName in *. rewrite Zip. rewrite Len'1. unfold Len in H9. clear - H9.
                                rewrite <- filter_map. rewrite map_length. apply Nat.ltb_lt...
                              - auto.
                            }
                            generalize Uniq. generalize H10. generalize H11. generalize H12.
                            generalize lhs. generalize rhs'. clear.
                            induction (skeleton_cfun_sigs_g (program_skeleton p)); intros;
                              [inversion H10|].
                            simpl in H11. simpl in H10. destruct H11; destruct H10.
                            * subst lhs. subst rhs'...
                            * rewrite H in Uniq. inversion Uniq; subst. rewrite <- H12 in H3.
                              apply (in_map (fun x => fst (fst x))) in H0. exfalso. apply H3...
                            * rewrite H0 in Uniq. inversion Uniq; subst. rewrite H12 in H3.
                              apply (in_map (fun x => fst (fst x))) in H. exfalso. apply H3...
                            * inversion Uniq. apply IHc...
                          + rewrite app_nth2.
                            2: { unfold Len in *. rewrite map_length. rewrite Len'1. clear - H9.
                              rewrite <- map_length with (f:=fun x => fst (fst x)). erewrite filter_ext.
                              - rewrite filter_map. rewrite (program_has_all_cfun_bods_g p).
                                rewrite <- map_length with (f:=fst) in H9. erewrite filter_ext in H9.
                                + rewrite filter_map in H9. apply Nat.ltb_ge...
                                + intros. simpl. change (eq_TypeName ?y (fst (fst a))) with
                                    ((fun x => eq_TypeName y (fst x)) (fst a))...
                              - eauto.
                            }
                            pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p))
                            as Uniq.
                            unfold cfun_sigs_names_unique in Uniq.
                            match goal with [|- snd (fst ?lhs') = snd (fst ?rhs')] =>
                              set (lhs:=lhs'); set (rhs:=rhs') end.
                            set (rhs':=(fun x => (unscope (fst (fst x)), snd (fst x), snd x)) rhs).
                            replace (snd (fst rhs)) with (snd (fst rhs'))...
                            assert (In lhs (skeleton_cfun_sigs_l (program_skeleton p))).
                            { unfold lhs. apply nth_In... }
                            assert (In rhs' (skeleton_cfun_sigs_l (program_skeleton p))).
                            { unfold rhs'. set (rhs_fn:=fun x : ScopedName * list TypeName * TypeName
                                => (unscope (fst (fst x)), (snd (fst x)), snd x)).
                              change (unscope (fst (fst rhs)), snd (fst rhs), snd rhs) with (rhs_fn rhs).
                              unfold rhs. rewrite <- map_nth. rewrite map_map.
                              unfold rhs_fn. simpl.
                              rewrite map_ext with (g:=id); try (symmetry; apply surjective_pairing).
                              rewrite map_id. eapply proj1. rewrite <- filter_In.
                              apply nth_In. rewrite Len'1.
                              erewrite cfun_bods_g_map_filter_l in LenSigs.
                              - rewrite map_map in LenSigs. rewrite map_length in LenSigs.
                                rewrite map_length. rewrite <- sigs_bods_g_length in LenSigs...
                              - rewrite filter_In in H6'. destruct H6'...
                              - rewrite filter_In in H6'. destruct H6'. unfold gfunsigs_filterfun_l in e0.
                                destruct x0. destruct s; try discriminate. apply Is_local_local.
                              - intros. destruct a0. destruct p0...
                            }
                            assert (fst (fst lhs) = fst (fst rhs')).
                            { unfold lhs. unfold rhs'. unfold rhs. rewrite ctxEq'. simpl.
                              unfold fa'. unfold a'. rewrite <- map_nth. rewrite <- Len'1.
                              unfold bods_gl. rewrite H9.
                              erewrite filter_ext with (l4:=program_cfun_bods_l p).
                              - rewrite filter_map.
                                pose proof (program_has_all_cfun_bods_l p) as Zip.
                                unfold has_all_cfun_bods in Zip.
                                unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
                                rewrite <- Zip. rewrite <- (map_nth _ _ ddtor).
                                rewrite map_map. simpl. rewrite <- map_nth with (d:=fst ddtor).
                                rewrite map_map. simpl. rewrite <- map_nth with (d:=fst (fst ddtor)).
                                rewrite map_map. simpl.
                                change (fun y : TypeName * Name * list TypeName * TypeName =>
                                  eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst y)))) with
                                  (fun y : TypeName * Name * list TypeName * TypeName =>
                                    (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x))
                                    ((fun z => fst (fst z)) y)).
                                rewrite filter_map.
                                assert (In x0 (skeleton_ctors (program_skeleton p))) as Aux1.
                                { rewrite filter_In in H6'. destruct H6'... }
                                assert (is_local (fst x0)) as Aux2.
                                { rewrite filter_In in H6'. destruct H6'. unfold gfunsigs_filterfun_l in e0.
                                  destruct x0. destruct s; try discriminate. apply Is_local_local.
                                }
                                erewrite cfun_bods_g_map_filter_l...
                                rewrite map_length. rewrite map_length. rewrite map_length.
                                rewrite sigs_bods_g_length. apply nth_indep.
                                rewrite Len'1. clear - Tmp Aux1 Aux2. rewrite map_length in Tmp.
                                rewrite <- filter_map. rewrite map_length. erewrite cfun_bods_g_map_filter_l in Tmp...
                                rewrite map_length in Tmp. rewrite sigs_bods_l_length...
                              - auto.
                            }
                            generalize Uniq. generalize H10. generalize H11. generalize H12.
                            generalize lhs. generalize rhs'. clear.
                            induction (skeleton_cfun_sigs_l (program_skeleton p)); intros;
                              [inversion H10|].
                            simpl in H11. simpl in H10. destruct H11; destruct H10.
                            * subst lhs. subst rhs'...
                            * rewrite H in Uniq. inversion Uniq; subst. rewrite <- H12 in H3.
                              apply (in_map (fun x => fst (fst x))) in H0. exfalso. apply H3...
                            * rewrite H0 in Uniq. inversion Uniq; subst. rewrite H12 in H3.
                              apply (in_map (fun x => fst (fst x))) in H. exfalso. apply H3...
                            * inversion Uniq. apply IHc...
                        }

                        assert (t = t0).
                        { evar (dx : (QName * list TypeName * TypeName)%type). assert (t = nth (length l') ts (snd dx)).
                          { rewrite <- l''Eq. rewrite H1. rewrite app_nth2; try (rewrite Len'2; omega).
                            replace (t::l2) with ([t]++l2)... rewrite app_nth1; try (rewrite Len'2; simpl; omega).
                            rewrite Len'2. rewrite Nat.sub_diag...
                          }
                          rewrite H9. clear H9.
                          case_eq Len; intros; rewrite H9 in *.
                          - clear - H9 SigLookup. unfold lookup_cfun_sig_g in SigLookup.
                            unfold lookup_cfun_sig_x in SigLookup. subst ts.
                            rewrite map_app. repeat (rewrite map_map). simpl.
                            unfold Len in *. rewrite Nat.ltb_lt in H9.
                            rewrite map_ext with (g:=snd)...
                            match goal with [|- _ _ (map snd ?mf' ++ _) _ = _] => set (mf:=mf') end.
                            assert (length l' < length mf).
                            { unfold mf. clear - H9. rewrite <- map_length with (f:=fun x => fst (fst (fst x))).
                              rewrite filter_map. rewrite <- map_map. rewrite (program_has_all_cfun_bods_g p).
                              rewrite map_map. rewrite <- filter_map. rewrite map_length...
                            }
                            rewrite app_nth1; try rewrite map_length...
                            pose proof (nth_In _  (fst d_a, snd (fst dx), snd dx) H11).
                            apply find_some in SigLookup.
                            destruct SigLookup as [SigLookup1 SigLookup2].
                            rewrite eq_QName_eq in SigLookup2. simpl in SigLookup2. subst qn.
                            unfold mf in *. unfold a' in *. unfold length_length in *.
                            unfold bods_gl in *.
                            rewrite <- Nat.ltb_lt in H9. rewrite H9 in *.
                            clear - SigLookup1 H12. clear e.
                            match goal with [|- ?goal = _] => set (tmp := goal) in * end.
                            case_eq (eq_TypeName tmp t0); intros; [apply eq_TypeName_eq|]... exfalso.
                            rewrite filter_In in H12. destruct H12 as [H12 _].
                            rewrite <- map_nth in SigLookup1.
                            change (fun x : TypeName * Name * list (ScopedName * expr) =>
                                    eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                              with (fun x : TypeName * Name * list (ScopedName * expr) =>
                                    (fun y => eq_TypeName (fst (unscope (fst x0))) (fst y)) (fst x)) in SigLookup1.
                            rewrite filter_map in SigLookup1.
                            rewrite <- (program_has_all_cfun_bods_g p) in SigLookup1.

                            pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
                            unfold cfun_sigs_names_unique in Uniq.
                            unfold tmp in H2. change (snd dx) with (snd (fst d_a, snd (fst dx), snd dx)) in H2.
                            rewrite map_nth in H2. clear tmp.
                            generalize SigLookup1. generalize H12. generalize H2. generalize Uniq.
                            generalize dx. generalize d_a. generalize ctx. generalize t0. generalize x0.
                            generalize (length l'). clear.
                            generalize (skeleton_cfun_sigs_g (program_skeleton p)) at 1 4 6.
                            induction c; intros; [inversion H12|].
                            inversion Uniq; subst. destruct H12; destruct SigLookup1...
                            + subst a. unfold QName in *. rewrite H0 in H2. simpl in H2.
                              rewrite eq_TypeName_refl in H2. discriminate.
                            + rewrite H in H1. apply H1. rewrite <- map_nth. rewrite <- map_nth. simpl.
                              apply (in_map (fun x => fst (fst x))) in H0. simpl in H0.
                              rewrite <- filter_map in H0. rewrite map_map...
                            + rewrite H0 in H1. apply H1. simpl.
                              apply (in_map (fun x => fst (fst x))) in H. do 2 rewrite <- map_nth in H.
                              rewrite map_map in H. rewrite <- filter_map...
                          - clear - Tmp H9 SigLookup Htseq. unfold lookup_cfun_sig_l in SigLookup.
                            unfold lookup_cfun_sig_x in SigLookup. subst ts.
                            rewrite map_app. repeat (rewrite map_map). simpl.
                            match goal with [|- _ _ (map _ ?mf' ++ _) _ = _] => set (mf:=mf') end.
                            assert (length l' >= length mf).
                            { unfold mf. clear - H9. rewrite <- map_length with (f:=fun x => fst (fst (fst x))).
                              rewrite filter_map. rewrite <- map_map. rewrite (program_has_all_cfun_bods_g p).
                              rewrite map_map. rewrite <- filter_map. rewrite map_length.
                              unfold Len in H9. rewrite Nat.ltb_ge in H9...
                            }
                            rewrite app_nth2; try rewrite map_length...
                            pose proof (Tmp eq_refl) as Tmp'.
                            rewrite <- map_length with (f:=fun x => fst (fst x)) in Tmp'.
                            rewrite filter_map in Tmp'. rewrite <- map_map in Tmp'.
                            rewrite <- (program_has_all_cfun_bods_l p) in Tmp'. rewrite map_map in Tmp'.
                            rewrite <- filter_map in Tmp'. rewrite map_length in Tmp'.
                            rewrite map_length in Tmp'.
                            pose proof (nth_In _  (fst d_a, snd (fst dx), snd dx) Tmp').
                            apply find_some in SigLookup.
                            destruct SigLookup as [SigLookup1 SigLookup2].
                            rewrite eq_QName_eq in SigLookup2. simpl in SigLookup2. subst qn.
                            unfold mf in *. unfold a' in *. unfold length_length in *.
                            unfold bods_gl in *.
                            rewrite H9 in *.
                            clear - SigLookup1 H4.
                            match goal with [|- ?goal = _] => set (tmp := goal) in * end.
                            case_eq (eq_TypeName tmp t0); intros; [apply eq_TypeName_eq|]... exfalso.
                            rewrite filter_In in H4. destruct H4 as [H4 _].
                            rewrite <- map_nth in SigLookup1.
                            change (fun x : TypeName * Name * list (ScopedName * expr) =>
                                    eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
                              with (fun x : TypeName * Name * list (ScopedName * expr) =>
                                    (fun y => eq_TypeName (fst (unscope (fst x0))) (fst y)) (fst x)) in SigLookup1.
                            rewrite filter_map in SigLookup1.
                            rewrite <- (program_has_all_cfun_bods_l p) in SigLookup1.

                            pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
                            unfold cfun_sigs_names_unique in Uniq.
                            unfold tmp in H2. change (snd dx) with (snd (fst d_a, snd (fst dx), snd dx)) in H2.
                            rewrite map_nth in H2. clear tmp.
                            generalize SigLookup1. generalize H4. generalize H2. generalize Uniq.
                            generalize dx. generalize d_a. generalize ctx. generalize t0.
                            generalize (length l'). clear - H6'.
                            generalize (skeleton_cfun_sigs_l (program_skeleton p)) at 1 4 6.
                            induction c; intros; [inversion H4|].
                            inversion Uniq; subst. destruct H4; destruct SigLookup1...
                            + subst a. unfold QName in *.
                              match goal with [H2 : eq_TypeName (_ (_ ?n1 _ _)) _ = _ , _ : nth ?n2 _ _ = _ |- _] =>
                                replace n2 with n1 in H0 end.
                              2:{ erewrite cfun_bods_g_map_filter_l.
                               - rewrite map_length.
                                 rewrite <- (map_length (fun x => fst (fst x)) (filter _ (program_cfun_bods_g _))).
                                 rewrite filter_map.
                                 rewrite <- map_length with (f:=fun x => fst (fst (fst x))). rewrite filter_map.
                                 rewrite <- map_map. rewrite (program_has_all_cfun_bods_g p). rewrite map_map...
                               - clear - H6'. rewrite filter_In in H6'. destruct H6'...
                               - clear - H6'. rewrite filter_In in H6'. destruct H6'. unfold gfunsigs_filterfun_l in H0.
                                 destruct x0. destruct s; try discriminate. apply Is_local_local.
                              }
                              rewrite H0 in H2. simpl in H2.
                              rewrite eq_TypeName_refl in H2. discriminate.
                            + rewrite H in H1. apply H1. rewrite <- map_nth. rewrite <- map_nth. simpl.
                              apply (in_map (fun x => fst (fst x))) in H0. simpl in H0.
                              rewrite <- filter_map in H0. rewrite map_length in H0. rewrite map_map...
                            + rewrite H0 in H1. apply H1. simpl.
                              apply (in_map (fun x => fst (fst x))) in H. do 2 rewrite <- map_nth in H.
                              rewrite map_map in H. rewrite <- filter_map. rewrite map_length...
                        }

                        destruct mctxtEq as [m0 [m0' [m0Len mctxtEq]]].
                        destruct snda'Eq as [es_0 [es_0' [es_0Len snda'Eq]]].
                        unfold ctxt.
                        eapply ListTypeDeriv'_split with
                          (cs0:=m0)(cs0':=m0')(es0:=es_0)
                          (ts0:=repeat t0 (length es_0))(ts0':=repeat t0 (length es_0'))...
                        *** unfold ctxt. rewrite es_0Len...
                        *** rewrite es_0Len. rewrite repeat_length...
                        *** unfold ctxt in *. rewrite <- mctxtEq. rewrite <- snda'Eq. rewrite H9.
                            replace (repeat t0 (length es_0) ++ t0 :: repeat t0 (length es_0'))
                              with (repeat t0 (length (snd a')))...
                            apply (f_equal (@length _)) in snda'Eq. generalize snda'Eq.
                            rewrite map_length. generalize (snd a'). generalize es_0. generalize es_0'.
                            generalize e. clear. intros. rewrite app_length in snda'Eq. simpl in snda'Eq.
                            generalize dependent (length l). generalize (length es_0). generalize (length es_0').
                            clear. intros. subst. induction n0... simpl. rewrite IHn0...
Unshelve. all:(try (split; eauto; apply global));eauto.
- destruct x0. destruct s...
- destruct x0. destruct s...
- split; [|exact []]. destruct x0. destruct s...
- split; try exact (fst x0). exact (E_Var 0).
- split; try exact (fst x0). exact (E_Var 0).
- split; try exact (fst x0). exact (E_Var 0).
Grab Existential Variables. all:eauto.
Qed.


Corollary new_gfunbods_l_typecheck: forall p tn,
  Forall (no_matches tn) (map snd (flat_map snd (program_gfun_bods_l p))) ->
  Forall (no_matches tn) (map snd (flat_map snd (program_cfun_bods_l p))) ->
  Forall (no_matches tn) (map snd (flat_map snd (program_cfun_bods_g p))) ->
  gfun_bods_l_typecheck (refunctionalize_to_skeleton p tn) (new_gfun_bods_l p tn).
Proof with eauto.
intros. unfold gfun_bods_l_typecheck.
pose proof (program_gfun_bods_typecheck_l p).
pose proof (program_cfun_bods_typecheck_l p).
pose proof (program_cfun_bods_typecheck_g p).
unfold gfun_bods_l_typecheck in H2.
unfold cfun_bods_l_typecheck in H3.
unfold cfun_bods_g_typecheck in H4.
rewrite Forall_forall in *. intros.
unfold new_gfun_bods_l in H5.
apply in_app_or in H5. rewrite or_comm in H5. destruct H5.
- rewrite in_map_iff in H5. do 2 destruct H5. pose proof H6 as H6'.
  apply H2 in H6. destruct x. inversion H5; subst. simpl.
  do 3 destruct H6. exists x. exists x1. split.
  + unfold lookup_gfun_sig_l. simpl. unfold new_gfunsigs_l.
    unfold lookup_gfun_sig_l in H6. clear - H6.
    unfold lookup_gfun_sig_x in *. rewrite <- find_none_append...
    match goal with [|- ?lhs' = _] => set (lhs:=lhs') end.
    case_eq lhs; intros... exfalso. unfold lhs in *. apply find_some in H.
    apply find_some in H6. clear - H H6. simpl in *.
    destruct H. destruct H6. rewrite in_map_iff in H. do 2 destruct H.
    rewrite filter_In in H3. destruct H3. unfold gfunsigs_mapfun in *.
    destruct x2. destruct p0. destruct s; try discriminate.
    simpl in *. inversion H. subst. rewrite eq_QName_eq in *. simpl in *. subst.
    rewrite eq_TypeName_eq in *. subst. clear - H1 H3.
    pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as InCDts.
    unfold gfun_sigs_in_cdts in InCDts. rewrite Forall_forall in InCDts.
    pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)) as InDts.
    unfold dts_ctors_in_dts in InDts. rewrite Forall_forall in InDts.
    apply InCDts in H1. apply InDts in H3. simpl in *. clear - H1 H3.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
    unfold dts_cdts_disjoint in Disj. unfold not in Disj. eapply Disj.
    split...
  + set (cmtch:=E_CoMatch (fst x0) (index_list 0 x1) (snd x0)).
    assert (cmtch=cmtch)... apply (f_equal (refunctionalize_expr tn)) in H8.
    unfold cmtch in H8 at 1. cbn -[cmtch] in H8.
    replace (map (fun x : expr * TypeName => (refunctionalize_expr tn (fst x), snd x))
      (index_list 0 x1))
    with (index_list 0 x1) in H8.
    2:{ clear. generalize 0. induction x1; intros... simpl. f_equal. apply IHx1. }
    rewrite H8. unfold cmtch.
    apply refunctionalize_expr_preserves_typing...
    intros. inversion H9; subst; try discriminate. inversion H11; subst.
    * clear - H10 H14. generalize H14. clear H14. generalize dependent 0.
      induction x1; intros; [ inversion H14 |]. simpl in H14. destruct H14; subst.
      -- inversion H10; subst; try discriminate. inversion H0.
      -- eapply IHx1...
    * clear - H H11 H6' H14 H10. unfold no_matches in H.
      rewrite in_map_iff in H14. destruct H14. destruct H0.
      eapply H.
      -- rewrite in_map_iff. eexists. rewrite in_flat_map. rewrite and_comm. split...
      -- eauto.
- exists (fst x).
  rewrite in_map_iff in H5. do 2 (destruct H5).
  exists (snd x0). split.
  + unfold lookup_gfun_sig_l. simpl. unfold new_gfunsigs_l.
    rewrite filter_In in H6. destruct H6.
    unfold gfunsigs_filterfun_l in H7.
    case_eq (fst x0); intros.
    * replace (fst x) with (unscope (fst x0)). 2: { inversion H5... }
      apply gfun_sig_lookup_l with (q:=q)...
      destruct x0. simpl in *. rewrite H8 in H7. rewrite H8...
    * destruct x0. simpl in H8. rewrite H8 in H7. discriminate.
  + apply T_CoMatch with (bindings_exprs := map fst (index_list 0 (snd x0)))
      (bindings_types := snd x0)
      (dtorlist := (map (fun x => (global (fst (fst x)), snd (fst x), snd x)) (filter
        (fun x0 => eq_TypeName (fst (fst x)) (fst (fst (fst x0))))
        (skeleton_cfun_sigs_g (program_skeleton p)))) ++
       (map (fun x => (local (fst (fst x)), snd (fst x), snd x)) (filter
        (fun x0 => eq_TypeName (fst (fst x)) (fst (fst (fst x0))))
        (skeleton_cfun_sigs_l (program_skeleton p))))).
   * rewrite (combine_fst_snd (index_list 0 (snd x0))). f_equal.
     -- rewrite map_fst_combine... repeat (rewrite map_length)...
     -- generalize 0. generalize (snd x0). clear. induction l; intros...
        simpl. rewrite IHl...
   * rewrite <- (app_nil_l (snd x0)). apply index_list_typechecks...
   * unfold lookup_dtors. simpl.
     assert (eq_TypeName (fst (fst x)) tn = true) as eqTyp.
     { inversion H5. subst. simpl. rewrite filter_In in H6.
       destruct H6... destruct x0. simpl in *.
       destruct s; try discriminate. rewrite eq_TypeName_eq in *... }
     rewrite eqTyp. f_equal. unfold computeNewCoDatatype.
     rewrite filter_app.
     assert (filter (fun x1 : ScopedName * list TypeName * TypeName =>
         let (y,_) := x1 in let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst x)))
       (skeleton_dtors (program_skeleton p)) = []) as dtorsEq.
     { case_eq (filter (fun x1 : ScopedName * list TypeName * TypeName =>
                let (y, _) := x1 in let (n, _) := y in eq_TypeName (fst (unscope n)) (fst (fst x)))
         (skeleton_dtors (program_skeleton p))); intros... exfalso.
       pose proof (in_eq p0 l). rewrite <- H7 in H8. rewrite filter_In in H8. destruct H8.
       pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)) as DtorInCdt.
       unfold cdts_dtors_in_cdts in DtorInCdt. rewrite Forall_forall in DtorInCdt.
       pose proof (DtorInCdt _ H8). destruct p0. simpl in *.
       rewrite filter_In in H6. destruct H6. destruct p0.
       rewrite eq_TypeName_eq in *. simpl in H10. rewrite H9 in H10.
       pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)) as CtorInDt.
       unfold dts_ctors_in_dts in CtorInDt. rewrite Forall_forall in CtorInDt.
       pose proof (CtorInDt _ H6). rewrite eqTyp in H10.
       unfold gfunsigs_filterfun_l in H11. destruct x0.
       destruct s0; try discriminate. rewrite eq_TypeName_eq in H11.
       simpl in H12. rewrite <- H11 in H12.
       pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
       unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=tn).
       split...
     }
     unfold Destructor in *. rewrite dtorsEq. rewrite app_nil_r.
     rewrite filter_app. f_equal.
     -- set (g:=fun y : QName * list TypeName * TypeName =>
                 (fun x1 => eq_TypeName (fst (unscope (fst (fst x1)))) tn)
                 ((fun x1 => (global (fst (fst x1)), snd (fst x1), snd x1)) y)).
        rewrite filter_ext with (g0:=g)... subst g. rewrite filter_map.
        set (g:=fun y : QName * list TypeName * TypeName =>
                 (fun x1 => eq_TypeName (fst (fst x)) (fst (unscope (fst (fst x1)))))
                 ((fun x1 => (global (fst (fst x1)), snd (fst x1), snd x1)) y)).
        rewrite filter_ext with (g0:=g)... subst g. rewrite filter_map.
        rewrite filter_compose.
        rewrite filter_ext with
          (g:=fun x1 => eq_TypeName (fst (fst x)) (fst (unscope (fst (fst x1)))))...
        intros. rewrite eq_TypeName_eq in eqTyp. rewrite eqTyp.
        destruct a. destruct p0. simpl. rewrite andb_diag. apply eq_TypeName_symm.
     -- set (g:=fun y : QName * list TypeName * TypeName =>
                 (fun x1 => eq_TypeName (fst (unscope (fst (fst x1)))) tn)
                 ((fun x1 => (local (fst (fst x1)), snd (fst x1), snd x1)) y)).
        rewrite filter_ext with (g0:=g)... subst g. rewrite filter_map.
        set (g:=fun y : QName * list TypeName * TypeName =>
                 (fun x1 => eq_TypeName (fst (fst x)) (fst (unscope (fst (fst x1)))))
                 ((fun x1 => (local (fst (fst x1)), snd (fst x1), snd x1)) y)).
        rewrite filter_ext with (g0:=g)... subst g. rewrite filter_map.
        rewrite filter_compose.
        rewrite filter_ext with
          (g:=fun x1 => eq_TypeName (fst (fst x)) (fst (unscope (fst (fst x1)))))...
        intros. rewrite eq_TypeName_eq in eqTyp. rewrite eqTyp.
        destruct a. destruct p0. simpl. rewrite andb_diag. apply eq_TypeName_symm.
   * clear - H5 H6. inversion H5. subst. clear - H6. rewrite Forall_forall. intros.
     destruct x. destruct p0. destruct p1. destruct p0. simpl in H.
     apply (in_map (fun x => (fst (fst x), snd x))) in H. simpl in H.
     rewrite map_fst_f_combine in H.
     apply (in_map (fun x => (fst x, (fun x => fst (fst x)) (snd x)))) in H. simpl in H.
     change (fun x : ScopedName * (ScopedName * list TypeName * TypeName) => (fst x, fst (fst (snd x))))
       with (fun x : ScopedName * (ScopedName * list TypeName * TypeName) =>
             (fst x, (fun x => fst (fst x)) (snd x))) in H.
     rewrite map_snd_f_combine in H.
     repeat (rewrite map_app in H). repeat (rewrite map_map in H).
     simpl in H. rewrite filter_In in H6. destruct H6 as [H6 H6GlobalAux].
     assert (is_local (fst x0)).
     { clear - H6GlobalAux. unfold gfunsigs_filterfun_l in H6GlobalAux.
       destruct x0. simpl. destruct s; try discriminate. apply Is_local_local.
     }
     unfold globalize_aux in H. rewrite map_map in H. simpl in H.
     unfold localize_aux in H. rewrite map_map in H. simpl in H.
     rewrite cfunbods_g_cfunsigs_l in H... rewrite cfunbods_l_cfunsigs_l in H...
     evar (d : ScopedName). apply (In_nth _ _ (d,d)) in H. destruct H as [n [H1 H2]].
     rewrite combine_nth in H2... inversion H2... Unshelve. all:eauto.
   * pose proof H0 as NoMatch_l. pose proof H1 as NoMatch_g.
     clear - H3 H4 H5 H6 NoMatch_g NoMatch_l.
     match goal with [|- _ /// ?ctxts' |||- ?es' ::: ?ts'] =>
       set (ctxts:=ctxts'); set (es:=es'); set (ts:=ts')
     end.
     assert (length ctxts = length es) as Len1.
     { unfold ctxts. unfold es. repeat (rewrite map_length). rewrite app_length.
       destruct x. simpl. inversion H5. subst. rewrite app_length.
       unfold globalize_aux. unfold localize_aux. repeat (rewrite map_map).
       assert (In x0 (skeleton_ctors (program_skeleton p))).
       { rewrite filter_In in H6. destruct H6... }
       assert (is_local (fst x0)).
       { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in H1.
         destruct x0. destruct s; try discriminate. apply Is_local_local.
       }
       pose proof (program_has_all_cfun_bods_g p) as Zip1.
       pose proof (program_has_all_cfun_bods_l p) as Zip2.
       unfold has_all_cfun_bods in *.
       f_equal; repeat (rewrite map_length).
       - erewrite cfun_bods_g_map_filter_l... rewrite map_length.
         rewrite <- map_length with (f:=fun x => fst (fst x)). unfold cfun_bod_named.
         rewrite <- map_length with (f:=fst).
         rewrite <- map_map.
         change (fun x : TypeName * Name * list TypeName * TypeName => ?t1 ?t2 (fst (fst (fst x))))
           with (fun x : TypeName * Name * list TypeName * TypeName => (fun y => t1 t2 (fst (fst y))) (fst x)).
         rewrite filter_map. rewrite map_length.
         erewrite filter_ext; [erewrite filter_ext with (l:=program_cfun_bods_g p) |].
         + rewrite filter_map. rewrite <- Zip1. rewrite <- map_map with (f:=fst).
           rewrite <- (filter_map (map fst _)). rewrite map_length...
         + intros. simpl. match goal with [|- ?lh1 ?lh2 = _] =>
             change (lh1 lh2) with ((fun x => lh1 (fst x)) (fst a)) end...
         + eauto.
       - erewrite cfun_bods_l_map_filter_l... rewrite map_length.
         rewrite <- map_length with (f:=fun x => fst (fst x)). unfold cfun_bod_named.
         rewrite <- map_length with (f:=fst).
         rewrite <- map_map.
         change (fun x : TypeName * Name * list TypeName * TypeName => ?t1 ?t2 (fst (fst (fst x))))
           with (fun x : TypeName * Name * list TypeName * TypeName => (fun y => t1 t2 (fst (fst y))) (fst x)).
         rewrite filter_map. rewrite map_length.
         erewrite filter_ext; [erewrite filter_ext with (l:=program_cfun_bods_l p) |].
         + rewrite filter_map. rewrite <- Zip2. rewrite <- map_map with (f:=fst).
           rewrite <- (filter_map (map fst _)). rewrite map_length...
         + intros. simpl. match goal with [|- ?lh1 ?lh2 = _] =>
             change (lh1 lh2) with ((fun x => lh1 (fst x)) (fst a)) end...
         + eauto.
     }
     assert (length es = length ts) as Len2.
     { unfold ts. unfold es. destruct x. inversion H5; subst. repeat (rewrite map_length).
       rewrite app_length. repeat (rewrite map_length). simpl. rewrite app_length.
       repeat (rewrite map_length). unfold globalize_aux. unfold localize_aux. repeat (rewrite map_length).
       assert (In x0 (skeleton_ctors (program_skeleton p))).
       { rewrite filter_In in H6. destruct H6... }
       assert (is_local (fst x0)).
       { rewrite filter_In in H6. destruct H6. unfold gfunsigs_filterfun_l in H1.
         destruct x0. destruct s; try discriminate. apply Is_local_local.
       }
       erewrite cfun_bods_g_map_filter_l... erewrite cfun_bods_l_map_filter_l...
       repeat (rewrite map_length).
       pose proof (program_has_all_cfun_bods_g p) as Zip1.
       pose proof (program_has_all_cfun_bods_l p) as Zip2.
       unfold has_all_cfun_bods in *.
       rewrite <- map_length with (f:=fun x => fst (fst x)).
       change (fun x1 : TypeName * Name * list TypeName * TypeName =>
         eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
        with (fun x1 : TypeName * Name * list TypeName * TypeName =>
         (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) ((fun x => fst (fst x)) x1)).
       rewrite filter_map. unfold QName in *. rewrite Zip1.
       rewrite <- map_length with (f:=fun x => fst (fst x)).
       change (fun x1 : TypeName * Name * list TypeName * TypeName =>
         eq_TypeName (fst (unscope (fst x0))) (fst (fst (fst x1))))
        with (fun x1 : TypeName * Name * list TypeName * TypeName =>
         (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) ((fun x => fst (fst x)) x1)).
       rewrite filter_map. unfold QName in *. rewrite Zip2.
       do 2 rewrite <- (map_length fst (@filter (TypeName * Name * cfun_bod) _ _)).
       change (fun x : TypeName * Name * cfun_bod =>
         eq_TypeName (fst (unscope (fst x0))) (fst (fst x)))
        with (fun x : TypeName * Name * cfun_bod =>
         (fun x => eq_TypeName (fst (unscope (fst x0))) (fst x)) (fst x)).
       do 2 rewrite <- filter_map...
     }
     assert (exists l l' l'', length l = length l' /\ length l' = length l'' /\
       l ++ ctxts = ctxts /\ l' ++ es = es /\ l'' ++ ts = ts).
     { exists []. exists []. exists []... }
     generalize H. generalize ctxts at 1 3. generalize ts at 1 3. generalize es at 1 3.
     induction es0; intros.
     -- destruct H0 as [l [l' [l'' [Len'1 [Len'2 [lEq [l'Eq l''Eq]]]]]]].
        apply (f_equal (length (A:=_))) in lEq. rewrite Len1 in lEq.
        rewrite <- l'Eq in lEq. rewrite app_nil_r in lEq. rewrite <- Len'1 in lEq.
        destruct ctxts0; [|rewrite app_length in lEq; simpl in lEq; omega].
        rewrite app_nil_r in l'Eq. apply (f_equal (length (A:=_))) in l''Eq.
        rewrite app_length in l''Eq. rewrite <- Len2 in l''Eq.
        rewrite <- Len'2 in l''Eq. rewrite l'Eq in l''Eq.
        destruct ts0; [| simpl in l''Eq; omega].
        apply ListTypeDeriv'_Nil.
     -- destruct H0 as [l [l' [l'' [Len'1 [Len'2 [lEq [l'Eq l''Eq]]]]]]].
        case_eq ctxts0; intros; case_eq ts0; intros; simpl.
        ++ subst. apply (f_equal (length (A:=_))) in l'Eq.
           rewrite app_length in l'Eq. rewrite <- Len1 in l'Eq.
           rewrite <- Len'1 in l'Eq. rewrite <- lEq in l'Eq.
           simpl in l'Eq. rewrite app_nil_r in l'Eq. omega.
        ++ subst. apply (f_equal (length (A:=_))) in l'Eq.
           rewrite app_length in l'Eq. rewrite <- Len1 in l'Eq.
           rewrite <- Len'1 in l'Eq. rewrite <- lEq in l'Eq.
           simpl in l'Eq. rewrite app_nil_r in l'Eq. omega.
        ++ subst. apply (f_equal (length (A:=_))) in l''Eq.
           rewrite app_length in l''Eq. rewrite <- Len2 in l''Eq.
           rewrite <- Len'2 in l''Eq. rewrite <- l'Eq in l''Eq.
           rewrite app_length in l''Eq. simpl in l''Eq. omega.
        ++ apply ListTypeDeriv'_Cons.
           ** unfold es in l'Eq. destruct x. inversion H5; subst l3 q. clear H5.
              simpl in *. rewrite map_app in l'Eq.
              repeat (rewrite map_map in l'Eq). simpl in l'Eq.
              rewrite <- map_app in l'Eq.
              eapply new_gfunbods_l_typecheck_aux with
                (ctxts:=ctxts)(ctxts0:=ctxts0)(es:=es)(es0:=es0)(ts:=ts)(ts0:=ts0)...
           ** apply IHes0. exists (l++[l0]). exists (l'++[a]). exists (l''++[t]).
              split; try split; try (repeat (rewrite app_length); simpl; omega).
              split; try split; try (rewrite <- app_assoc; simpl; subst)...
              Unshelve. all:(split; try exact (fst x0); exact (E_Var 0)).
Qed.


Lemma refunctionalize_expr_no_effect_on_matches : forall tn e,
  collect_match_names (refunctionalize_expr tn e) = collect_match_names e.
Proof with eauto.
intros. induction e using expr_strong_ind; simpl; eauto;
  try (try (rewrite IHe; f_equal);
    induction ls; eauto; simpl; inversion H; subst; rewrite IHls; eauto; rewrite H2)...
- case_eq (eq_TypeName tn (fst (unscope n))); intros; simpl;
    induction ls; eauto; inversion H; subst; simpl; rewrite IHls; eauto; rewrite H3...
- case_eq (eq_TypeName tn (fst (unscope sn))); intros; simpl;
    rewrite IHe; f_equal; induction ls; eauto; simpl; inversion H; subst; rewrite IHls; eauto; rewrite H3...
- rewrite IHe. do 2 f_equal. repeat rewrite concat_app. f_equal.
  + induction es... simpl in *. inversion H0; subst. destruct a. simpl. rewrite H3. f_equal. apply IHes...
  + induction ls... simpl in *. inversion H; subst. destruct a. simpl. rewrite H3. f_equal. apply IHls...
- repeat rewrite concat_app. f_equal.
  + induction es... simpl. inversion H0; subst. destruct a. simpl. rewrite H3. f_equal. apply IHes...
  + induction ls... simpl. inversion H; subst. destruct a. simpl. rewrite H3. f_equal. apply IHls...
- f_equal...
Qed.

Lemma switch_indices_aux_no_effect_on_matches : forall p sn n tn e,
  collect_match_names (switch_indices_aux p sn n tn e) = collect_match_names e.
Proof with eauto.
intros. unfold switch_indices_aux. rewrite refunctionalize_expr_no_effect_on_matches.
unfold switch_indices_cfun. destruct (lookup_cfun_sig_scoped p sn)... cbn.
generalize 0.
induction e using expr_strong_ind; intro n'; simpl in *;
  try solve [induction ls; eauto; inversion H; subst; simpl; f_equal; eauto];
  try solve [f_equal; eauto; induction ls; eauto; inversion H; subst; simpl; f_equal; eauto].
- case_eq (v <? n')... intros. case_eq (v <? n' + n)...
- do 2 f_equal... repeat rewrite concat_app. f_equal.
  induction es... simpl. inversion H0; subst. f_equal...
- f_equal... repeat rewrite concat_app. f_equal.
  induction es... simpl. inversion H0; subst. f_equal...
Qed.

Fact uniqueness_concat_app_switch : forall {A} (l1 l2 l3 : list (list A)),
  Unique.unique (concat (l1 ++ l2 ++ l3)) ->
  Unique.unique (concat (l1 ++ l3 ++ l2)).
Proof with auto.
intros. repeat rewrite concat_app in *. apply Unique.unique_app_switch in H...
Qed.


Definition collect_tuple : Type :=
  { x : (expr -> list QName) * (fun_bods -> cfun_bods -> gfun_bods -> Prop)
  | (forall p : program,
       (snd x) (program_fun_bods p)
         (program_cfun_bods_g p ++ program_cfun_bods_l p)
         (program_gfun_bods_g p ++ program_gfun_bods_l p))
  /\ (forall f c g, (snd x) f c g = Unique.unique
       (concat
          (map (fst x)
            (map snd f ++
             map snd (concat (map snd c)) ++
             map snd (concat (map snd g))))))
  /\ (forall tn e, (fst x) (refunctionalize_expr tn e) = (fst x) e)
  /\ (forall p sn n tn e, (fst x) (switch_indices_aux p sn n tn e) = (fst x) e)
  }.

Lemma program_match_names_unique_cbods_g_gbods_g : forall p (ct : collect_tuple),
  (snd (proj1_sig ct)) (program_fun_bods p) (program_cfun_bods_g p) (program_gfun_bods_g p).
Proof with eauto.
intros. pose proof (proj1 (proj2_sig ct) p). rewrite (proj1 (proj2 (proj2_sig ct))) in *.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
repeat rewrite map_app in H. repeat rewrite flat_map_app in H. rewrite <- app_assoc in H.
match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with ((l1++l2)++l3++(l4++l5)) in H
end.
2:{ repeat (try rewrite <- app_assoc; try rewrite app_assoc)... }
apply Unique.unique_app_switch in H. rewrite app_assoc in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
rewrite app_assoc in H. rewrite <- Unique.uniqueness_app_rewrite in H.
destruct H as [H _]. repeat rewrite <- flat_map_concat_map.
rewrite <- app_assoc in H. repeat rewrite flat_map_app...
Qed.

Lemma program_match_names_unique_cbods_l_gbods_g : forall p (ct : collect_tuple),
  (snd (proj1_sig ct)) (program_fun_bods p) (program_cfun_bods_l p) (program_gfun_bods_g p).
Proof with eauto.
intros. pose proof (proj1 (proj2_sig ct) p). rewrite (proj1 (proj2 (proj2_sig ct))) in *.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
repeat rewrite map_app in H. repeat rewrite flat_map_app in H. rewrite <- app_assoc in H.
match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with (l1++l2++(l3++l4++l5)) in H
end.
2:{ repeat (try rewrite <- app_assoc; try rewrite app_assoc)... }
apply Unique.unique_app_switch in H. rewrite app_assoc in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
rewrite app_assoc in H. rewrite app_assoc in H.
rewrite <- Unique.uniqueness_app_rewrite in H.
destruct H as [H _]. repeat rewrite <- flat_map_concat_map.
rewrite <- app_assoc in H. repeat rewrite flat_map_app...
Qed.

Lemma program_match_names_unique_cbods_g_gbods_l : forall p (ct : collect_tuple),
  (snd (proj1_sig ct)) (program_fun_bods p) (program_cfun_bods_g p) (program_gfun_bods_l p).
Proof with eauto.
intros. pose proof (proj1 (proj2_sig ct) p). rewrite (proj1 (proj2 (proj2_sig ct))) in *.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
repeat rewrite map_app in H. repeat rewrite flat_map_app in H. rewrite <- app_assoc in H.
match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with (l1++l2++(l3++l4)++l5) in H
end.
2:{ repeat (try rewrite <- app_assoc; try rewrite app_assoc)... }
rewrite app_assoc in H. apply Unique.unique_app_switch in H. rewrite app_assoc in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
repeat rewrite <- flat_map_concat_map.
rewrite <- app_assoc in H. repeat rewrite flat_map_app...
Qed.

Lemma program_match_names_unique_cbods_l_gbods_l : forall p (ct : collect_tuple),
  (snd (proj1_sig ct)) (program_fun_bods p) (program_cfun_bods_l p) (program_gfun_bods_l p).
Proof with eauto.
intros. pose proof (proj1 (proj2_sig ct) p). rewrite (proj1 (proj2 (proj2_sig ct))) in *.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
repeat rewrite map_app in H. repeat rewrite flat_map_app in H. rewrite <- app_assoc in H.
match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with (l1++l2++(l3++l4++l5)) in H
end.
2:{ repeat (try rewrite <- app_assoc; try rewrite app_assoc)... }
apply Unique.unique_app_switch in H. do 2 rewrite app_assoc in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
rewrite <- app_assoc in H.
match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4) |- _] =>
  replace (l1++l2++l3++l4) with ((l1++l2)++l3++l4) in H
end.
2:{ repeat (try rewrite <- app_assoc; try rewrite app_assoc)... }
apply Unique.unique_app_switch in H. rewrite app_assoc in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
repeat rewrite <- flat_map_concat_map.
rewrite <- app_assoc in H. repeat rewrite flat_map_app...
Qed.


Lemma new_match_names_unique_cbods_g_gbods_g : forall p tn (ct : collect_tuple)
  (CfunLMUnique1 : Unique.unique
    (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_l p)))))
  (CfunLMUnique2 : Forall
    (fun x => ~ In x (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_l p)))))
    (concat (map (fst (proj1_sig ct))
      (map snd (program_fun_bods p) ++
       map snd (concat (map snd (program_cfun_bods_g p))) ++
       map snd (concat (map snd (program_gfun_bods_g p))))))),
  (snd (proj1_sig ct)) (new_fun_bods p tn) (new_cfun_bods_g p tn) (new_gfun_bods_g p tn).
Proof with eauto.
intros.
pose proof (program_match_names_unique_cbods_g_gbods_g p ct) as Aux.
rewrite (proj1 (proj2 (proj2_sig ct))) in Aux.
pose proof (Unique.uniqueness_app _ _ Aux CfunLMUnique1 CfunLMUnique2).
clear Aux.
clear CfunLMUnique1 CfunLMUnique2.

(*[> Structurally different part (compared with defunc) no. 1 <]*)
rewrite <- flat_map_concat_map in H. rewrite flat_map_app in H. rewrite flat_map_app in H.
rewrite <- app_assoc in H. rewrite <- app_assoc in H.
(*[> Refunc-specific <]*)
rewrite app_assoc in H. apply Unique.unique_app_switch in H.
rewrite <- app_assoc in H.
rewrite app_assoc with (l:=_ _ (_ _ (_ (_ _ (program_cfun_bods_g p))))) in H.
apply Unique.unique_app_switch in H.
(*[> End Refunc-specific <]*)
repeat (rewrite <- flat_map_app in H). rewrite flat_map_concat_map in H.
unfold cfun_bod in *. rewrite <- (flat_map_concat_map snd (program_cfun_bods_g p)) in H.
rewrite <- map_app in H. rewrite <- flat_map_app in H. rewrite flat_map_concat_map in H.

rewrite (proj1 (proj2 (proj2_sig ct))) in *.
unfold new_fun_bods in *. unfold new_cfun_bods_g in *. unfold new_gfun_bods_g in *.
repeat (repeat (rewrite map_app); repeat (rewrite map_map); simpl).
match goal with [|- _ (_ ((map ?f ?l) ++ _ ++ _))] =>
  replace (map f l) with (map (fun x => (fst (proj1_sig ct)) (snd x)) l) end.
2:{ apply map_ext. intros. symmetry. apply (proj1 (proj2 (proj2 (proj2_sig ct)))). }

(*[> Structurally different part no. 2, entirely refunc-specific <]*)
repeat rewrite map_app. apply uniqueness_concat_app_switch.

rewrite concat_map. rewrite map_app. rewrite map_map. erewrite map_ext_in with (l:=filter _ _).
2:{ intros. rewrite map_app. rewrite map_map. simpl. unfold globalize_aux. unfold localize_aux.
  rewrite map_map. simpl. rewrite map_map. simpl. rewrite map_map.
  erewrite map_ext.
  2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
  erewrite map_ext with (l:=filter _ (flat_map _ (program_cfun_bods_l p))).
  2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
  reflexivity.
}
match goal with [|- _ (_ (_ ++ (_ (?l1' ++ ?l2')) ++ ?gbods'))] =>
  set (l1:=l1'); set (l2:=l2'); set (gbods:=gbods') end.
rewrite concat_app with (l2:=l2).


match goal with
  [_ : Unique.unique (_ (_ _ (?fs' ++ ?cfs' ++ map snd (concat (map snd (?gfs_g' ++ ?gfs_l')))))) |- _] =>
    set (fs:=fs') in *; set (cfs:=cfs') in *; set (gfs_g:=gfs_g'); set (gfs_l:=gfs_l') in * end.
assert (Unique.unique (concat (map (fst (proj1_sig ct)) (fs ++ cfs ++ (map snd
    (filter (fun x => match fst x with global _ => eq_TypeName tn (fst (unscope (fst x))) | _ => false end)
      (concat (map snd (gfs_g ++ gfs_l))) ++
    (concat (map snd (filter (fun x => negb (eq_TypeName tn (fst (fst x)))) (gfs_g)))))))))) as H0.
{ repeat rewrite map_app. repeat rewrite concat_app. rewrite app_assoc. rewrite app_assoc.
  apply Unique.uniqueness_app.
  - eapply Unique.uniqueness_sublist; [|apply H]. repeat rewrite map_app. repeat rewrite concat_app.
    rewrite <- app_assoc. repeat (apply Sublist.sublist_app; try apply Sublist.sublist_refl).
    fold gfs_g. unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *.
    generalize (concat (map snd gfs_g) ++ concat (map snd gfs_l)). clear.
    induction l; [constructor|]. simpl. case_eq (fst a); intros.
    + rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app... constructor.
    + case_eq (eq_TypeName tn (fst (unscope (global q)))); intros.
      * simpl. apply Sublist.sublist_app... apply Sublist.sublist_refl.
      * rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app... constructor.
  - eapply Unique.uniqueness_sublist... fold gfs_g.
    repeat (rewrite map_app; rewrite map_app; rewrite concat_app).
    rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app; [constructor|].
    rewrite concat_app. rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app; [constructor|].
    generalize gfs_g. clear. induction gfs_g; [constructor|].
    simpl. unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
    case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
    + simpl. repeat (rewrite map_app; rewrite map_app; rewrite concat_app). apply Sublist.sublist_app...
      apply Sublist.sublist_refl.
    + repeat rewrite map_app. rewrite concat_app. rewrite <- (app_nil_l (concat _)).
      apply Sublist.sublist_app; [constructor|]. rewrite <- map_app. apply IHgfs_g.
  - clear - H. rewrite Forall_forall. intros. apply in_app_or in H0. destruct H0.
    + repeat (rewrite map_app in H; rewrite concat_app in H). rewrite app_assoc in H.
      apply Unique.uniqueness_app_not_in in H. rewrite Forall_forall in H.
      apply H in H0. unfold not. intros. apply H0. fold gfs_g. clear - H1.
      generalize dependent gfs_g. induction gfs_g; intros; [exfalso|]...
      simpl in *. repeat rewrite map_app. repeat rewrite concat_app. rewrite <- app_assoc.
      unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
      case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
      * rewrite H in *. simpl in *. repeat rewrite map_app in H1. rewrite concat_app in H1.
        apply in_or_app. apply in_app_or in H1. destruct H1; [left|]...
        right. rewrite <- concat_app. repeat rewrite <- map_app...
      * rewrite H in *. simpl in *. apply in_or_app. right.
        rewrite <- concat_app. repeat rewrite <- map_app...
    + rewrite filter_app in H0. repeat rewrite map_app in H0. rewrite concat_app in H0.
      apply in_app_or in H0. repeat rewrite map_app in H. repeat rewrite concat_app in H. destruct H0.
      * rewrite app_assoc in H. rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H.
        fold gfs_g in H. generalize H H0.
        match goal with [|- _ (_ ++ _ ++ ?l') -> _] => generalize l' end.
        rewrite <- concat_app. rewrite <- map_app.
        generalize gfs_l. assert (Forall (fun x => In x gfs_g) gfs_g) as Aux.
        { rewrite Forall_forall... }
        generalize Aux. generalize gfs_g at - 1. clear. induction gfs_g0; intros...
        unfold not. intros. simpl in *. rewrite filter_app in H0.
        unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
        case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
        -- rewrite H2 in *. simpl in *. repeat rewrite map_app in H1. rewrite concat_app in H1.
           apply in_app_or in H1. destruct H1.
           ++ inversion Aux; subst. repeat rewrite map_app in H0. rewrite concat_app in H0.
              apply in_app_or in H0. destruct H0.
              ** rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. do 2 destruct H0.
                 rewrite in_map_iff in H0. do 2 destruct H0. rewrite filter_In in H4. destruct H4.
                 case_eq (fst x1); intros; rewrite H8 in H7; try discriminate. simpl in *.
                 assert (Aux2: fst q = fst (fst a)).
                 { eapply cfun_bods_type_names... }
                 rewrite <- Aux2 in H2. rewrite eq_TypeName_eq in *. subst. rewrite eq_TypeName_refl in H2.
                 discriminate.
              ** clear IHgfs_g0 Aux. repeat rewrite map_app in H. rewrite concat_app in H.
                 apply in_split in H1. do 2 destruct H1. rewrite H1 in H.
                 rewrite <- app_assoc in H. rewrite <- app_assoc in H. rewrite <- app_nil_l in H.
                 apply Unique.unique_app_switch in H. inversion H; subst. apply H7.
                 apply in_or_app. left. apply in_or_app. right. clear - H0.
                 rewrite <- flat_map_concat_map in *. apply in_or_app. left. rewrite concat_app. rewrite map_app.
                 rewrite flat_map_app. apply in_or_app. left. rewrite in_flat_map in *.
                 destruct H0. destruct H. exists x0. split... clear - H. rewrite in_map_iff in *.
                 do 2 destruct H. exists x. split... rewrite filter_In in H0. destruct H0...
           ++ inversion Aux; subst. pose proof H6 as H6'. eapply IHgfs_g0 in H6...
              ** instantiate (1:=l). instantiate (1:=gfs_l). clear - H.
                 repeat rewrite map_app in H. rewrite concat_app in H. generalize H. clear H.
                 match goal with [|- _ ((?l'++_) ++ _) -> _] => generalize l' end. intros.
                 rewrite <- map_app in H. induction l0... apply IHl0. inversion H...
              ** match goal with [_ : In x (_ (_ _ (_ _ (?l1 ++ _)))) |- _] => assert (l1 = []) end.
                 2:{ rewrite H3 in H0... }
                 clear - H2 H5. match goal with [|- ?lhs' = _] => set (lhs:=lhs'); case_eq lhs; intros end...
                 pose proof (in_eq p0 l). rewrite <- H in H0. unfold lhs in H0. rewrite filter_In in H0.
                 destruct H0. assert (H': exists q, fst p0 = global q). { destruct (fst p0)... discriminate. }
                 destruct H' as [q H']. assert (fst q = fst (fst a)). { eapply cfun_bods_type_names... }
                 rewrite H' in H1. simpl in *. rewrite H3 in H1. rewrite eq_TypeName_eq in H1. subst.
                 rewrite eq_TypeName_refl in H2. discriminate.
        -- rewrite H2 in *. simpl in *. inversion Aux; subst. pose proof H6 as H6'. eapply IHgfs_g0 in H6...
           ++ instantiate (1:=l). instantiate (1:=gfs_l). clear - H.
              repeat rewrite map_app in H. rewrite concat_app in H. generalize H. clear H.
              match goal with [|- _ ((?l'++_) ++ _) -> _] => generalize l' end. intros.
              rewrite <- map_app in H. induction l0... apply IHl0. inversion H...
           ++ rewrite <- flat_map_concat_map in H0. rewrite map_app in H0. rewrite flat_map_app in H0.
              apply in_app_or in H0. destruct H0; [| rewrite <- flat_map_concat_map]...
              exfalso. rename H into Uniq. clear - Uniq H0 H1 H2 H5 Aux. rewrite <- flat_map_concat_map in H1.
              rewrite in_flat_map in *. destruct H0. destruct H. do 2 destruct H1. rewrite in_map_iff in *.
              do 2 destruct H. do 2 destruct H1. rewrite <- flat_map_concat_map in H6.
              rewrite in_flat_map in H6. rewrite filter_In in H4. do 2 destruct H6. destruct H4.
              rewrite filter_In in H6. destruct H6.
              apply in_split in H4. do 2 destruct H4. rewrite H4 in Uniq. repeat (rewrite map_app in Uniq).
              simpl in Uniq. rewrite H in Uniq. apply in_split in H0. do 2 destruct H0. rewrite H0 in Uniq.
              repeat (rewrite concat_app in Uniq). simpl in Uniq.
              apply in_split in H6. do 2 destruct H6. rewrite H6 in Uniq. apply in_split in H7.
              do 2 destruct H7. repeat (rewrite map_app in Uniq). simpl in Uniq. rewrite H7 in Uniq.
              repeat (rewrite concat_app in Uniq). simpl in Uniq.
              repeat (rewrite map_app in Uniq). simpl in Uniq. rewrite H1 in Uniq.
              apply in_split in H3. do 2 destruct H3. rewrite H3 in Uniq. clear - Uniq.
              rewrite <- app_assoc in Uniq. generalize Uniq. clear Uniq. fold QName in *.
              match goal with [|- _ ((?l' ++ _ ++ _) ++ _ ++ _) -> _] => generalize l' end.
              clear. intros.
              match goal with [_ : Unique.unique ((l0++(x7++x::x8)++?r1)++?r2) |- _] =>
                assert (Unique.unique (x::x8++r1++r2)) end.
              { induction l0; induction x7; inversion Uniq; subst... do 2 rewrite app_nil_l in Uniq.
                clear - Uniq. rewrite <- app_comm_cons in Uniq. rewrite <- app_assoc in Uniq.
                rewrite app_assoc. rewrite app_comm_cons. rewrite <- app_assoc...
              }
              clear - H. inversion H; subst. apply H2. do 2 (apply in_or_app; right).
              repeat rewrite concat_app. do 2 (apply in_or_app; left). apply in_or_app. right.
              apply in_or_app. left. apply in_or_app. right. simpl. rewrite <- app_assoc. apply in_or_app.
              right. left...
      * rewrite app_assoc in H. rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H.
        simpl in H. repeat rewrite map_app in H. rewrite concat_app in H.
        rewrite <- app_assoc in H. apply Unique.uniqueness_app_not_in in H. rewrite Forall_forall in H.
        unfold not. intros. fold gfs_g in H. rewrite <- flat_map_concat_map in H1.
        rewrite in_flat_map in H1. do 2 destruct H1. rewrite in_map_iff in H1.
        do 2 destruct H1. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0.
        do 2 destruct H0. rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
        do 2 destruct H3. rewrite in_map_iff in H0. do 2 destruct H0.
        rewrite filter_In in H6. destruct H6. rewrite filter_In in H3. destruct H3.
        case_eq (fst x4); intros; rewrite H9 in H7; try discriminate.
        eapply H.
        -- rewrite <- flat_map_concat_map. rewrite in_flat_map. eexists. split.
           ++ rewrite in_map_iff. eexists. split... rewrite <- flat_map_concat_map. rewrite in_flat_map.
              eexists. split...
           ++ eauto.
        -- apply in_or_app. left. rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x2. split...
           rewrite in_map_iff. eexists. split...
}
clear H. rename H0 into H.

unfold fs in *. unfold cfs in *. unfold gfs_g in *. unfold gfs_l in *. clear fs cfs gfs_g gfs_l.

eapply unique_unordered; eauto; [apply QName_dec|].
unfold unordered_eq. split.
- intros. split; intros.
  + rewrite map_app in H0. rewrite map_map in H0. rewrite concat_app in H0.
    rewrite concat_app. apply in_app_or in H0. apply in_or_app. destruct H0; [left|]...
    rewrite map_app in H0. rewrite concat_app in H0. apply in_app_or in H0. destruct H0.
    * right. rewrite concat_app. apply in_or_app. left. rewrite concat_app.
      apply in_or_app. right. unfold l2. rewrite map_map. erewrite map_ext.
      2: { intros. rewrite map_map. simpl. match goal with [|- _ ?f _ = _ _] =>
             change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end... }
      rewrite <- map_map. erewrite map_ext.
      2: { intros. erewrite map_ext.
        2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
          change ((fst (proj1_sig ct)) (snd a1)) with ((fun x => (fst (proj1_sig ct)) (snd x)) a1)...
        }
        eauto.
      }
      rewrite <- concat_map. rewrite <- map_map...
    * right. rewrite concat_app. rewrite concat_app.
      assert (In a (concat (concat l1) ++ concat gbods)).
      2:{ apply in_app_or in H1. apply in_or_app. destruct H1; [|right]...
          left. apply in_or_app. left...
      }
      clear - H0. remember gbods. unfold gbods in Heql. rewrite concat_map in Heql.
      rewrite map_map in Heql. rewrite <- filter_map in Heql. rewrite map_map in Heql.
      simpl in Heql. erewrite map_ext in Heql.
      2: { intros. rewrite map_map. simpl. match goal with [|- _ ?f _ = _ _] =>
             change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end... }
      erewrite map_ext in Heql.
      2: { intros. erewrite map_ext.
        2: { intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
             change ((fst (proj1_sig ct)) (snd a1)) with ((fun x => (fst (proj1_sig ct)) (snd x)) a1)...
        }
        match goal with [|- map ?f _ = _] => change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end...
      }
      clear gbods. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0.
      destruct H0 as [x [H0_1 H0_2]]. rewrite in_map_iff in H0_1. destruct H0_1 as [x0 [H0_1 H0_1In]].
      do 2 rewrite <- flat_map_concat_map in H0_1In. apply in_app_or in H0_1In.
      destruct H0_1In.
      -- rewrite filter_In in H. rewrite in_flat_map in H. destruct H as [[x' [x'In1 x'In2]] x0Eq].
         apply in_app_or in x'In1. destruct x'In1.
         ++ case_eq (negb (eq_TypeName tn (fst (fst x')))); intros.
            ** apply in_or_app. right. subst. rewrite <- map_map. rewrite <- concat_map.
               rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x0. split...
               rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x'. split...
               rewrite filter_In. split...
            ** apply in_or_app. left. clear l Heql. unfold l1. clear l1.
               eapply In_concat... rewrite <- flat_map_concat_map. rewrite in_flat_map.
               set (lookup := lookup_ctor_sig (program_skeleton p) (fst x0)).
               assert (exists dtor, lookup = Some dtor).
               { pose proof (program_cfun_bods_typecheck_g p) as Typ. unfold cfun_bods_g_typecheck in Typ.
                 rewrite Forall_forall in Typ. apply Typ in H. clear Typ. destruct H as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as Len.
                 rewrite Nat.eqb_eq in Len. repeat rewrite map_length in Len. symmetry in Len.
                 pose proof (combine_in x'In2 Len). destruct H. unfold lookup.
                 unfold lookup_ctors in H11. unfold cfun_bod in *.
                 case_eq (filter (eq_TypeName (fst (fst x'))) (skeleton_dts (program_skeleton p)));
                   intros; rewrite H1 in H11; try discriminate. inversion H11; subst.
                 match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end; [exists c|]...
                 unfold lookup_ctor_sig in H2. pose proof H as H'. apply in_combine_l in H. rewrite filter_In in H.
                 destruct H. eapply find_none in H2... apply in_combine_switch in H'... rewrite Forall_forall in H12.
                 apply H12 in H'. destruct x0. destruct x. subst. simpl in *.
                 rewrite eq_ScopedName_refl in H2. discriminate.
               }
               unfold dtor in *. destruct H1 as [dtor dtorEq]. exists dtor. split.
               --- unfold lookup in *. unfold lookup_ctor_sig in dtorEq. apply find_some in dtorEq.
                   rewrite filter_In. destruct dtorEq. split... unfold gfunsigs_filterfun_g.
                   destruct dtor. rewrite eq_ScopedName_eq in H2. simpl in H2.
                   subst. destruct x0. simpl in *. destruct s...
               --- apply in_or_app. left. rewrite in_map_iff. exists (fst x', x0). simpl. rewrite H0_1. split...
                   rewrite filter_In. split.
                   +++ rewrite in_flat_map. exists x'. split... rewrite in_map_iff. exists x0. split...
                   +++ unfold gfunbods_filterfun_g. destruct x'. simpl. destruct q. destruct x0. simpl in *.
                       destruct s... rewrite negb_false_iff in H0. rewrite eq_TypeName_eq in H0. subst.
                       rewrite eq_TypeName_eq in x0Eq. simpl in x0Eq. subst.
                       unfold lookup in *. unfold lookup_ctor_sig in dtorEq. apply find_some in dtorEq.
                       destruct dtorEq. unfold eq_ScopedName in H1. destruct dtor. simpl in *.
                       destruct s; try discriminate. rewrite eq_QName_eq in H1. subst. simpl.
                       rewrite eq_TypeName_refl. rewrite eq_QName_refl...
         ++ apply in_or_app. left. clear l Heql. unfold l1. simpl. erewrite map_ext.
            2: { intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
              match goal with [|- map ?f (filter (_ (_ (_ a0))) ?m) = _] =>
                change (map f (filter (_ (_ (_ a0))) m)) with ((fun y => map f ((fun x =>
                  (filter (gfunbods_filterfun_g (unscope (fst x))) m)) y)) a0) end...
            }
            rewrite <- map_map. rewrite <- concat_map. rewrite <- flat_map_concat_map.
            rewrite in_flat_map. exists (fst x', x0). subst. split...
            rewrite <- flat_map_concat_map. rewrite in_flat_map.
            set (lookup := lookup_ctor_sig (program_skeleton p) (fst x0)).
            assert (exists dtor, lookup = Some dtor).
            { pose proof (program_cfun_bods_typecheck_l p) as Typ. unfold cfun_bods_l_typecheck in Typ.
              rewrite Forall_forall in Typ. apply Typ in H. clear Typ. destruct H as [qn [args [t [_ Typ]]]].
              inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H12) as Len.
              rewrite Nat.eqb_eq in Len. repeat rewrite map_length in Len. symmetry in Len.
              pose proof (combine_in x'In2 Len). destruct H. unfold lookup.
              unfold lookup_ctors in H10. unfold cfun_bod in *.
              case_eq (filter (eq_TypeName (fst (fst x'))) (skeleton_dts (program_skeleton p)));
                intros; rewrite H0 in H10; try discriminate. inversion H10; subst.
              match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end; [exists c|]...
              unfold lookup_ctor_sig in H1. pose proof H as H'. apply in_combine_l in H. rewrite filter_In in H.
              destruct H. eapply find_none in H1... apply in_combine_switch in H'... rewrite Forall_forall in H11.
              apply H11 in H'. destruct x0. destruct x. subst. simpl in *.
              rewrite eq_ScopedName_refl in H1. discriminate.
            }
            unfold dtor in *. destruct H0 as [dtor dtorEq]. exists dtor. split.
            ** rewrite filter_In. unfold lookup in *. unfold lookup_ctor_sig in dtorEq.
               apply find_some in dtorEq. destruct dtorEq. split...
               unfold gfunsigs_filterfun_g. destruct dtor.
               rewrite eq_ScopedName_eq in H1. simpl in H1. subst. destruct x0. simpl in *.
               destruct s...
            ** rewrite filter_In. rewrite in_flat_map. unfold gfunbods_filterfun_g. destruct x'.
               destruct q. simpl. destruct x0. simpl in x0Eq. destruct s; try discriminate.
               split.
               --- exists (t,n,c). split; [apply in_or_app; right|]... simpl in *. apply in_map...
               --- unfold lookup in *. unfold lookup_ctor_sig in dtorEq.
                   apply find_some in dtorEq. destruct dtorEq. rewrite eq_ScopedName_eq in H1.
                   simpl in H1. rewrite <- H1. simpl. rewrite eq_QName_refl. simpl in x'In2.
                   clear - H x'In2. rewrite andb_true_r. rewrite eq_TypeName_eq. symmetry.
                   change t with (fst (fst (t,n,c))). eapply cfun_bods_l_type_names...
      -- apply in_or_app. right. subst. rewrite <- map_map. rewrite <- concat_map.
         rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x0. split...
         rewrite <- flat_map_concat_map...
  + clear H. rewrite concat_app in H0. apply in_app_or in H0. rewrite map_app. rewrite map_app.
    rewrite concat_app. rewrite concat_app. apply in_or_app. rewrite map_map at 1.
    destruct H0; [left|]... right. rewrite concat_app in H. apply in_app_or in H. destruct H.
    * rewrite concat_app in H. apply in_app_or in H. apply in_or_app. destruct H.
      -- right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
         unfold l1 in H. clear l1 l2 gbods. erewrite map_ext in H.
         2: { intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
              match goal with [|- map ?f (filter (_ (_ (_ a0))) ?m) = _] =>
                change (map f (filter (_ (_ (_ a0))) m)) with ((fun y => map f ((fun x =>
                  (filter (gfunbods_filterfun_g (unscope (fst x))) m)) y)) a0) end...
         }
         rewrite <- map_map in H. rewrite <- concat_map in H. rewrite <- flat_map_concat_map in H.
         rewrite in_flat_map in H. do 2 destruct H. simpl in *. exists (snd (snd x)). split...
         apply in_map. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
         do 2 destruct H. apply in_or_app. left. rewrite filter_In. rewrite filter_In in H1.
         destruct H1. split.
         ++ rewrite <- flat_map_concat_map. rewrite in_flat_map. unfold cfun_bod in *.
            rewrite in_flat_map in H1. do 2 destruct H1. exists x1. split... rewrite in_map_iff in H3.
            do 2 destruct H3. subst...
         ++ rewrite in_flat_map in H1. do 2 destruct H1. rewrite in_map_iff in H3. do 2 destruct H3.
            subst. simpl. unfold gfunbods_filterfun_g in H2. destruct x1. destruct q. simpl in *.
            destruct x2. simpl. destruct s... rewrite filter_In in H. destruct H.
            unfold gfunsigs_filterfun_g in H3. destruct x0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in H3. subst. simpl in *. apply andb_prop in H2. destruct H2.
            unfold eq_QName in H3. destruct q0. destruct q. simpl in *. apply andb_prop in H3. destruct H3...
      -- left. unfold l2 in *. clear - H. unfold gfun_bod in *. rewrite <- concat_map in H.
         rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H. do 2 destruct H.
         rewrite in_flat_map. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
         do 2 destruct H. rewrite in_map_iff in H1. do 2 destruct H1. exists (snd x1).
         split.
         ++ apply in_map. destruct x1. simpl in *. rewrite <- flat_map_concat_map. rewrite in_flat_map.
            exists x0. split...
         ++ destruct x. simpl in *. inversion H1; subst. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0...
    * clear - H. apply in_or_app. right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
      unfold gbods in H. clear gbods. rewrite <- flat_map_concat_map. rewrite <- flat_map_concat_map in H.
      rewrite in_flat_map in H. do 2 destruct H. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
      do 2 destruct H. rewrite filter_In in H. rewrite in_map_iff in H. do 3 destruct H.
      destruct x0. inversion H; subst. simpl in *. destruct x. simpl in *. rewrite in_map_iff in H1.
      do 2 destruct H1. inversion H1; subst. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0.
      exists (snd x). split...
      apply in_map. apply in_or_app. right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
      exists x1. split... rewrite filter_In. split...
- rewrite <- flat_map_concat_map. unfold l1. unfold l2. unfold gbods. clear.
  rewrite concat_app. rewrite <- (flat_map_concat_map _ (program_fun_bods p)).
  rewrite app_length. rewrite flat_map_app. rewrite app_length. f_equal.
  + rewrite flat_map_concat_map. rewrite map_map. rewrite flat_map_concat_map...
  + rewrite concat_app. rewrite app_length. rewrite concat_app. rewrite app_length.
    rewrite <- plus_assoc. rewrite plus_comm. rewrite flat_map_app. rewrite app_length.
    rewrite <- plus_assoc. f_equal.
    * unfold gfun_bod. rewrite <- concat_map. rewrite <- map_map with (f:=snd).
      rewrite length_concat. rewrite flat_map_concat_map. rewrite length_concat.
      f_equal. repeat (rewrite map_map). rewrite concat_map. rewrite concat_map.
      repeat (rewrite map_map). unfold cfun_bod.
      match goal with [|- _ = _ (_ ?f' _)] => erewrite map_ext with (f:=f') end.
      2:{ intros. rewrite map_map. simpl. erewrite map_ext.
          2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
          reflexivity.
      }
      reflexivity.
    * rewrite map_app. rewrite flat_map_app. rewrite app_length. rewrite plus_comm. f_equal.
      -- unfold cfun_bod. rewrite flat_map_concat_map. rewrite length_concat. rewrite length_concat.
         f_equal. repeat (rewrite map_map). rewrite concat_map. rewrite concat_map.
         repeat (rewrite map_map). unfold cfun_bod. generalize (program_cfun_bods_g p). induction c...
         simpl in *. case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
         ++ unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite H.
            simpl. rewrite IHc. clear IHc. rewrite map_map. simpl. erewrite map_ext with (f:=fun x : ScopedName * expr =>
              length ((fst (proj1_sig ct)) (refunctionalize_expr tn (snd x)))).
            2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            reflexivity.
         ++ unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite H...
      -- simpl. erewrite map_ext with (A:=(ScopedName * list TypeName)%type).
         2:{ intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app. reflexivity. }
         rewrite <- map_map with (g:=map (fun a0 : QName * (ScopedName * expr) => (fst (proj1_sig ct)) (snd (snd a0)))).
         rewrite <- concat_map. change (fun a0 : QName * (ScopedName * expr) => (fst (proj1_sig ct)) (snd (snd a0)))
           with (fun a0 : QName * (ScopedName * expr) => (fst (proj1_sig ct)) ((fun x => (snd (snd x))) a0)).
         rewrite <- map_map with (g:=fst (proj1_sig ct)). do 2 rewrite <- flat_map_concat_map.

         match goal with [|- _ (_ _ (_ _ ?lhs)) = _] => replace lhs with
           (filter (fun x => if in_dec ScopedName_dec (fst x)
               (map fst (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))))
             then true else false) lhs) end.
         2:{ assert (Forall (fun x => In x (program_cfun_bods_g p ++ program_cfun_bods_l p))
               (program_cfun_bods_g p ++ program_cfun_bods_l p)). { rewrite Forall_forall... }
           generalize H. clear H. generalize (program_cfun_bods_g p ++ program_cfun_bods_l p) at - 1. induction l...
           intros. inversion H; subst. simpl. repeat rewrite filter_app. rewrite IHl... f_equal.
           clear IHl H. assert (Forall (fun x => In x (snd a)) (snd a)). { rewrite Forall_forall... }
           generalize H. clear H. generalize (snd a) at - 1. induction c...
           intros. rewrite filter_compose. inversion H; subst. simpl. case_eq (fst a0); intros.
           - rewrite andb_false_r. rewrite filter_compose in IHc...
           - case_eq (eq_TypeName tn (fst (unscope (global q)))); intros;
               [|rewrite andb_false_r; rewrite filter_compose in IHc]...
             match goal with [|- (if (if ?c then _ else _) && _ then _ else _) = _] =>
               assert (exists l, c = left l) end.
             { clear IHc. match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end...
               rename H6 into Contra.
               apply in_app_or in H2. destruct H2;
                 [ pose proof (program_cfun_bods_typecheck_g p) as Typ
                 | pose proof (program_cfun_bods_typecheck_l p) as Typ].
               - unfold cfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
                 apply Typ in H2. clear Typ. destruct H2 as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. unfold lookup_ctors in H16. fold cfun_bod in H16.
                 case_eq (filter (eq_TypeName (fst (fst a)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H2 in H16; try discriminate.
                 inversion H16; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H18).
                 repeat rewrite map_length in H6. rewrite Nat.eqb_eq in H6. symmetry in H6.
                 pose proof (combine_in H4 H6). destruct H7. apply in_combine_switch in H7...
                 rewrite Forall_forall in H17. pose proof H7 as H7'. apply H17 in H7. destruct a0. destruct x.
                 subst. apply in_combine_r in H7'. rewrite filter_In in H7'. destruct H7'. simpl in H0. subst.
                 assert (gfunsigs_filterfun_g tn (global q, l1) = true).
                 { unfold gfunsigs_filterfun_g. rewrite eq_TypeName_eq in H1. subst. rewrite eq_TypeName_refl... }
                 pose proof (conj H7 H0) as Aux. rewrite <- filter_In in Aux.
                 apply (in_map fst) in Aux. simpl in Aux.
                 clear - Aux Contra. exfalso. apply n...
               - unfold cfun_bods_l_typecheck in Typ. rewrite Forall_forall in Typ.
                 apply Typ in H2. clear Typ. destruct H2 as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. unfold lookup_ctors in H16. fold cfun_bod in H16.
                 case_eq (filter (eq_TypeName (fst (fst a)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H2 in H16; try discriminate.
                 inversion H16; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H18).
                 repeat rewrite map_length in H6. rewrite Nat.eqb_eq in H6. symmetry in H6.
                 pose proof (combine_in H4 H6). destruct H7. apply in_combine_switch in H7...
                 rewrite Forall_forall in H17. pose proof H7 as H7'. apply H17 in H7. destruct a0. destruct x.
                 subst. apply in_combine_r in H7'. rewrite filter_In in H7'. destruct H7'. simpl in H0. subst.
                 assert (gfunsigs_filterfun_g tn (global q, l1) = true).
                 { unfold gfunsigs_filterfun_g. rewrite eq_TypeName_eq in H1. subst. rewrite eq_TypeName_refl... }
                 pose proof (conj H7 H0) as Aux. rewrite <- filter_In in Aux.
                 apply (in_map fst) in Aux. simpl in Aux.
                 clear - Aux Contra. exfalso. apply n...
             }
             destruct H6. rewrite H6. simpl. f_equal. rewrite filter_compose in IHc...
         }
         assert (Filter: Forall (fun x => gfunsigs_filterfun_g tn x = true)
           (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p)))).
         { rewrite Forall_forall. intros x H. rewrite filter_In in H. destruct H... }
         generalize Filter. clear Filter.
         assert (Subl : Sublist.sublist (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p)))
           (skeleton_ctors (program_skeleton p))).
         { apply Sublist.sublist_filter. }
         generalize Subl. clear Subl.
         generalize (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))). induction l; intros.
         ++ simpl. match goal with [|- _ (_ _ (_ _ (filter _ ?l))) = _] => induction l end...
         ++ simpl in *. rewrite map_app. do 2 rewrite flat_map_app. rewrite app_length. rewrite <- IHl.
            2:{ eapply Sublist.sublist_trans... constructor. apply Sublist.sublist_refl. }
            2:{ inversion Filter... }
            clear IHl.
            assert (H: exists l0, l0 ++ (program_cfun_bods_g p ++ program_cfun_bods_l p) =
              (program_cfun_bods_g p ++ program_cfun_bods_l p)).
            { exists []... }
            generalize H. clear H.
            change (list (prod ScopedName expr)) with cfun_bod.
            change (prod QName cfun_bod) with cfun_bod_named.
            rewrite <- flat_map_app.
            generalize (program_cfun_bods_g p ++ program_cfun_bods_l p) at - 2.
            induction l0; intros...
            assert (H0: (exists l1 : list cfun_bod_named,
              l1 ++ l0 = program_cfun_bods_g p ++ program_cfun_bods_l p)).
            { clear - H. destruct H. exists (x++[a0]). rewrite <- app_assoc... }
            rename H into InBods. apply IHl0 in H0. clear IHl0. simpl.
            rewrite filter_app with (P:=gfunbods_filterfun_g (unscope (fst a))).
            rewrite map_app. rewrite flat_map_app. rewrite app_length.
            rewrite filter_app. rewrite filter_app. rewrite filter_app.
            rewrite map_app. rewrite map_app. rewrite flat_map_app. rewrite flat_map_app.
            rewrite app_length. rewrite app_length.
            match goal with [|- _ = ?n1 + ?n2 + (?n3 + ?n4)] => replace (n1 + n2 + (n3 + n4)) with
              ((n1 + n3) + (n2 + n4)) end; try omega.
            rewrite <- H0. clear H0. f_equal.
            rewrite <- app_length. rewrite <- flat_map_app.
            assert (H: exists a, fst a = fst a0 /\ snd a = snd a0 /\
              exists a' a0, a0 ++ snd a = a' /\ In (fst a, a') (program_cfun_bods_g p ++ program_cfun_bods_l p)).
            { exists a0. split... split... destruct InBods. rewrite <- H. exists (snd a0). exists []. split...
              apply in_or_app. right. left... destruct a0...
            }
            generalize H. generalize (snd a0). induction c; intros...
            assert (Aux: exists a, fst a = fst a0 /\ snd a = c /\
              exists a' a0, a0 ++ snd a = a' /\  In (fst a, a') (program_cfun_bods_g p ++ program_cfun_bods_l p)).
            { clear - H0. destruct H0. destruct H. destruct H0. exists (fst x, c). split... split...
              do 3 destruct H1. simpl. exists x0. rewrite <- H1. exists (x1++[a1]). rewrite H0. rewrite <- app_assoc. split...
              rewrite <- H0. rewrite H1...
            }
            simpl. case_eq (fst a1); intros.
            ** destruct a0. destruct q0. simpl. destruct a1. simpl in H1. subst s...
            ** destruct a0. destruct q0. simpl. destruct a1. simpl in H1. subst s.
               case_eq (eq_TypeName tn (fst q)); intros.
               --- cbn. case_eq (ScopedName_dec (fst a) (global q)); intros.
                   +++ cbn. rewrite app_length. rewrite IHc... clear IHc.
                       case_eq (eq_TypeName t (fst (unscope (fst a))) &&
                         eq_QName (unscope (fst a)) q); intros.
                       *** cbn. rewrite app_length. f_equal.
                           assert (Aux2: exists r, in_dec ScopedName_dec (global q) (map fst l) = right r).
                           { pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
                             unfold cdts_dtor_names_unique in Uniq. eapply Sublist.sublist_map in Subl.
                             pose proof (Unique.uniqueness_sublist _ _ Subl Uniq) as Done.
                             simpl in Done. inversion Done; subst. rewrite e0 in H6.
                             case_eq (in_dec ScopedName_dec (global q) (map fst l)); intros.
                             - exfalso. apply H6...
                             - exists n0...
                           }
                           destruct Aux2 as [r Aux2]. rewrite Aux2...
                       *** rewrite e0 in H3. simpl in H3. rewrite eq_QName_refl in H3.
                           rewrite andb_false_iff in H3. destruct H3; try discriminate.
                           destruct H0 as [aH [H_1 [H_2 [aH_3 [a'H_3 [H_3_1 H_3_2]]]]]].
                           simpl in *. subst. destruct aH. simpl in *. destruct q0. inversion H_1; subst.
                           clear - H1 H3 H_3_2. destruct q. simpl in *. rewrite eq_TypeName_eq in H1. subst.
                           assert (t = t0). 2:{ subst. rewrite eq_TypeName_refl in H3. discriminate. }
                           clear H3. pose proof (program_cfun_bods_typecheck_g p) as Typ_g.
                           pose proof (program_cfun_bods_typecheck_l p) as Typ_l.
                           unfold cfun_bods_g_typecheck in Typ_g. unfold cfun_bods_l_typecheck in Typ_l.
                           rewrite Forall_forall in *. apply in_app_or in H_3_2. destruct H_3_2.
                           { apply Typ_g in H. do 4 destruct H. clear - H0. inversion H0; subst.
                             simpl in *.
                             set (el1:=(global (t0,n0),e)). set (el2:=nth (length a'H_3) ctorlist (global (t, n0), x0)).
                             set (el:=(el1,el2)).
                             assert (length (a'H_3 ++ (global (t0, n0), e) :: c) = length ctorlist) as LenAux.
                             { symmetry. apply Nat.eqb_eq. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as H.
                               do 2 rewrite map_length in H...
                             }
                             assert (length a'H_3 < length ctorlist) as Len.
                             { rewrite app_length in LenAux. simpl in LenAux. omega. }
                             assert (In el (combine (a'H_3 ++ (global (t0, n0), e) :: c) ctorlist)).
                             { unfold el. unfold el2. unfold el1. replace (global (t0, n0), e) with
                                 (nth (length a'H_3) (a'H_3 ++ (global (t0, n0), e) :: c) (global (t0, n0), e)).
                               2:{ rewrite app_nth2... rewrite Nat.sub_diag... }
                               rewrite <- combine_nth... rewrite app_nth2... rewrite Nat.sub_diag. apply nth_In.
                               rewrite combine_length. simpl. rewrite LenAux. rewrite Nat.min_id...
                             }
                             rewrite Forall_forall in H12. apply H12 in H. unfold el in H.
                             unfold lookup_ctors in H11.
                             case_eq (filter (eq_TypeName t) (skeleton_dts (program_skeleton p))); intros;
                               rewrite H1 in H11; try discriminate.
                             inversion H11; subst. unfold el1 in H.
                             remember el2 as el2'. destruct el2'. destruct s; try discriminate.
                             destruct q. inversion H; subst. unfold el2 in Heqel2'.
                             pose proof (nth_In _ (global (t, n1), x0)  Len) as H2. rewrite <- Heqel2' in H2.
                             rewrite filter_In in H2. destruct H2 as [_ H2]. rewrite eq_TypeName_eq in H2. simpl in *...
                           }
                           { apply Typ_l in H. do 4 destruct H. clear - H0. inversion H0; subst.
                             simpl in *.
                             set (el1:=(global (t0,n0),e)). set (el2:=nth (length a'H_3) ctorlist (global (t, n0), x0)).
                             set (el:=(el1,el2)).
                             assert (length (a'H_3 ++ (global (t0, n0), e) :: c) = length ctorlist) as LenAux.
                             { symmetry. apply Nat.eqb_eq. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as H.
                               do 2 rewrite map_length in H...
                             }
                             assert (length a'H_3 < length ctorlist) as Len.
                             { rewrite app_length in LenAux. simpl in LenAux. omega. }
                             assert (In el (combine (a'H_3 ++ (global (t0, n0), e) :: c) ctorlist)).
                             { unfold el. unfold el2. unfold el1. replace (global (t0, n0), e) with
                                 (nth (length a'H_3) (a'H_3 ++ (global (t0, n0), e) :: c) (global (t0, n0), e)).
                               2:{ rewrite app_nth2... rewrite Nat.sub_diag... }
                               rewrite <- combine_nth... rewrite app_nth2... rewrite Nat.sub_diag. apply nth_In.
                               rewrite combine_length. simpl. rewrite LenAux. rewrite Nat.min_id...
                             }
                             rewrite Forall_forall in H12. apply H12 in H. unfold el in H.
                             unfold lookup_ctors in H11.
                             case_eq (filter (eq_TypeName t) (skeleton_dts (program_skeleton p))); intros;
                               rewrite H1 in H11; try discriminate.
                             inversion H11; subst. unfold el1 in H.
                             remember el2 as el2'. destruct el2'. destruct s; try discriminate.
                             destruct q. inversion H; subst. unfold el2 in Heqel2'.
                             pose proof (nth_In _ (global (t, n1), x0)  Len) as H2. rewrite <- Heqel2' in H2.
                             rewrite filter_In in H2. destruct H2 as [_ H2]. rewrite eq_TypeName_eq in H2. simpl in *...
                           }
                   +++ assert (qEq: eq_QName (unscope (fst a)) q = false).
                       { case_eq (eq_QName (unscope (fst a)) q); intros... rewrite eq_QName_eq in *.
                         subst. exfalso. apply n0. inversion Filter; subst. unfold gfunsigs_filterfun_g in H2.
                         destruct a. destruct s; try discriminate...
                       }
                       rewrite qEq. rewrite andb_false_r.
                       case_eq (in_dec ScopedName_dec (global q) (map fst l)); intros...
                       cbn. rewrite app_length. rewrite flat_map_app. rewrite app_length. cbn.
                       rewrite app_length. apply IHc in Aux. rewrite flat_map_app in Aux.
                       rewrite app_length in Aux. simpl in *. omega.
               --- rewrite IHc... case_eq (eq_QName (unscope (fst a)) q); intros.
                   +++ rewrite eq_QName_eq in H2. subst. inversion Filter; subst.
                       unfold gfunsigs_filterfun_g in H4. destruct a. destruct s; try discriminate.
                       simpl in H1. rewrite H1 in H4. discriminate.
                   +++ rewrite andb_false_r...
Qed.

(* TODO Move to UtilsNamesUnique.v *)
Lemma cfun_bods_l_type_names_l : forall p a x1 q,
  In x1 (snd a) ->
  In a (program_cfun_bods_l p) ->
  fst x1 = local q ->
  fst q = fst (fst a).
Proof with eauto.
intros. pose proof (program_cfun_bods_typecheck_l p) as Typ.
unfold cfun_bods_l_typecheck in Typ. rewrite Forall_forall in Typ.
apply Typ in H0. clear Typ. destruct H0 as [qn [args [t [SigLookup Typ]]]].
inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H14) as Len.
clear - Len H H1 H12 H13. unfold lookup_ctors in H12. unfold QName in *.
case_eq (filter (eq_TypeName (fst (fst a))) (skeleton_dts (program_skeleton p))); intros;
  rewrite H0 in H12; try discriminate.
inversion H12; subst. clear H12 H0. do 2 rewrite map_length in Len.
rewrite Nat.eqb_eq in Len. symmetry in Len. pose proof (combine_in H Len) as H'.
destruct H' as [y H']. apply in_combine_switch in H'...
rewrite Forall_forall in H13. assert (fst (unscope (fst y)) = fst (fst a)) as Eq.
{ apply in_combine_r in H'. rewrite filter_In in H'. destruct H'. destruct y.
  simpl in *. apply eq_TypeName_eq...
}
apply H13 in H'. destruct x1. destruct y. subst. simpl in *. subst...
Qed.

Lemma new_match_names_unique_cbods_g_gbods_l : forall p tn (ct : collect_tuple)
  (CfunLMUnique1 : Unique.unique
    (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_l p)))))
  (CfunLMUnique2 : Forall
    (fun x => ~ In x (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_l p)))))
    (concat (map (fst (proj1_sig ct))
      (map snd (program_fun_bods p) ++
       map snd (concat (map snd (program_cfun_bods_g p))) ++
       map snd (concat (map snd (program_gfun_bods_l p))))))),
  (snd (proj1_sig ct)) (new_fun_bods p tn) (new_cfun_bods_g p tn) (new_gfun_bods_l p tn).
Proof with eauto.
intros.
pose proof (program_match_names_unique_cbods_g_gbods_l p ct) as Aux.
rewrite (proj1 (proj2 (proj2_sig ct))) in Aux.
pose proof (Unique.uniqueness_app _ _ Aux CfunLMUnique1 CfunLMUnique2).
clear Aux.
clear CfunLMUnique1 CfunLMUnique2.

(*[> Structurally different part (compared with defunc) no. 1 <]*)
rewrite <- flat_map_concat_map in H. rewrite flat_map_app in H. rewrite flat_map_app in H.
rewrite <- app_assoc in H. rewrite <- app_assoc in H.
(*[> Refunc-specific <]*)
rewrite app_assoc in H. apply Unique.unique_app_switch in H.
rewrite <- app_assoc in H.
rewrite app_assoc with (l:=_ _ (_ _ (_ (_ _ (program_cfun_bods_g p))))) in H.
apply Unique.unique_app_switch in H.
(*[> End Refunc-specific <]*)
repeat (rewrite <- flat_map_app in H). rewrite flat_map_concat_map in H.
unfold cfun_bod in *. rewrite <- (flat_map_concat_map snd (program_cfun_bods_g p)) in H.
rewrite <- map_app in H. rewrite <- flat_map_app in H. rewrite flat_map_concat_map in H.

rewrite (proj1 (proj2 (proj2_sig ct))) in *.
unfold new_fun_bods in *. unfold new_cfun_bods_g in *. unfold new_gfun_bods_l in *.
repeat (repeat (rewrite map_app); repeat (rewrite map_map); simpl).
match goal with [|- _ (_ ((map ?f ?l) ++ _ ++ _))] =>
  replace (map f l) with (map (fun x => (fst (proj1_sig ct)) (snd x)) l) end.
2:{ apply map_ext. intros. symmetry. apply (proj1 (proj2 (proj2 (proj2_sig ct)))). }

(*[> Structurally different part no. 2, entirely refunc-specific <]*)
repeat rewrite map_app. apply uniqueness_concat_app_switch.

rewrite concat_map. rewrite map_app. rewrite map_map. erewrite map_ext_in with (l:=filter _ _).
2:{ intros. rewrite map_app. rewrite map_map. simpl. unfold globalize_aux. unfold localize_aux.
  rewrite map_map. simpl. rewrite map_map. simpl. rewrite map_map.
  erewrite map_ext.
  2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
  erewrite map_ext with (l:=filter _ (flat_map _ (program_cfun_bods_l p))).
  2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
  reflexivity.
}
match goal with [|- _ (_ (_ ++ (_ (?l1' ++ ?l2')) ++ ?gbods'))] =>
  set (l1:=l1'); set (l2:=l2'); set (gbods:=gbods') end.
rewrite concat_app with (l2:=l2).


match goal with
  [_ : Unique.unique (_ (_ _ (?fs' ++ ?cfs' ++ map snd (concat (map snd (?gfs_g' ++ ?gfs_l')))))) |- _] =>
    set (fs:=fs') in *; set (cfs:=cfs') in *; set (gfs_g:=gfs_g'); set (gfs_l:=gfs_l') in * end.
assert (Unique.unique (concat (map (fst (proj1_sig ct)) (fs ++ cfs ++ (map snd
    (filter (fun x => match fst x with local _ => eq_TypeName tn (fst (unscope (fst x))) | _ => false end)
      (concat (map snd (gfs_g ++ gfs_l))) ++
    (concat (map snd (filter (fun x => negb (eq_TypeName tn (fst (fst x)))) (gfs_g)))))))))) as H0.
{ repeat rewrite map_app. repeat rewrite concat_app. rewrite app_assoc. rewrite app_assoc.
  apply Unique.uniqueness_app.
  - eapply Unique.uniqueness_sublist; [|apply H]. repeat rewrite map_app. repeat rewrite concat_app.
    rewrite <- app_assoc. repeat (apply Sublist.sublist_app; try apply Sublist.sublist_refl).
    fold gfs_g. unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *.
    generalize (concat (map snd gfs_g) ++ concat (map snd gfs_l)). clear.
    induction l; [constructor|]. simpl. case_eq (fst a); intros.
    + case_eq (eq_TypeName tn (fst (unscope (local q)))); intros.
      * simpl. apply Sublist.sublist_app... apply Sublist.sublist_refl.
      * rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app... constructor.
    + rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app... constructor.
  - eapply Unique.uniqueness_sublist... fold gfs_g.
    repeat (rewrite map_app; rewrite map_app; rewrite concat_app).
    rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app; [constructor|].
    rewrite concat_app. rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app; [constructor|].
    generalize gfs_g. clear. induction gfs_g; [constructor|].
    simpl. unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
    case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
    + simpl. repeat (rewrite map_app; rewrite map_app; rewrite concat_app). apply Sublist.sublist_app...
      apply Sublist.sublist_refl.
    + repeat rewrite map_app. rewrite concat_app. rewrite <- (app_nil_l (concat _)).
      apply Sublist.sublist_app; [constructor|]. rewrite <- map_app. apply IHgfs_g.
  - clear - H. rewrite Forall_forall. intros. apply in_app_or in H0. destruct H0.
    + repeat (rewrite map_app in H; rewrite concat_app in H). rewrite app_assoc in H.
      apply Unique.uniqueness_app_not_in in H. rewrite Forall_forall in H.
      apply H in H0. unfold not. intros. apply H0. fold gfs_g. clear - H1.
      generalize dependent gfs_g. induction gfs_g; intros; [exfalso|]...
      simpl in *. repeat rewrite map_app. repeat rewrite concat_app. rewrite <- app_assoc.
      unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
      case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
      * rewrite H in *. simpl in *. repeat rewrite map_app in H1. rewrite concat_app in H1.
        apply in_or_app. apply in_app_or in H1. destruct H1; [left|]...
        right. rewrite <- concat_app. repeat rewrite <- map_app...
      * rewrite H in *. simpl in *. apply in_or_app. right.
        rewrite <- concat_app. repeat rewrite <- map_app...
    + rewrite filter_app in H0. repeat rewrite map_app in H0. rewrite concat_app in H0.
      apply in_app_or in H0. repeat rewrite map_app in H. repeat rewrite concat_app in H. destruct H0.
      * rewrite app_assoc in H. rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H.
        fold gfs_g in H. generalize H H0.
        match goal with [|- _ (_ ++ _ ++ ?l') -> _] => generalize l' end.
        rewrite <- concat_app. rewrite <- map_app.
        generalize gfs_l. assert (Forall (fun x => In x gfs_g) gfs_g) as Aux.
        { rewrite Forall_forall... }
        generalize Aux. generalize gfs_g at - 1. clear. induction gfs_g0; intros...
        unfold not. intros. simpl in *. rewrite filter_app in H0.
        unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
        case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
        -- rewrite H2 in *. simpl in *. repeat rewrite map_app in H1. rewrite concat_app in H1.
           apply in_app_or in H1. destruct H1.
           ++ inversion Aux; subst. repeat rewrite map_app in H0. rewrite concat_app in H0.
              apply in_app_or in H0. destruct H0.
              ** rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. do 2 destruct H0.
                 rewrite in_map_iff in H0. do 2 destruct H0. rewrite filter_In in H4. destruct H4.
                 case_eq (fst x1); intros; rewrite H8 in H7; try discriminate. simpl in *.
                 assert (Aux2: fst q = fst (fst a)).
                 { eapply cfun_bods_type_names_l... }
                 rewrite <- Aux2 in H2. rewrite eq_TypeName_eq in *. subst. rewrite eq_TypeName_refl in H2.
                 discriminate.
              ** clear IHgfs_g0 Aux. repeat rewrite map_app in H. rewrite concat_app in H.
                 apply in_split in H1. do 2 destruct H1. rewrite H1 in H.
                 rewrite <- app_assoc in H. rewrite <- app_assoc in H. rewrite <- app_nil_l in H.
                 apply Unique.unique_app_switch in H. inversion H; subst. apply H7.
                 apply in_or_app. left. apply in_or_app. right. clear - H0.
                 rewrite <- flat_map_concat_map in *. apply in_or_app. left. rewrite concat_app. rewrite map_app.
                 rewrite flat_map_app. apply in_or_app. left. rewrite in_flat_map in *.
                 destruct H0. destruct H. exists x0. split... clear - H. rewrite in_map_iff in *.
                 do 2 destruct H. exists x. split... rewrite filter_In in H0. destruct H0...
           ++ inversion Aux; subst. pose proof H6 as H6'. eapply IHgfs_g0 in H6...
              ** instantiate (1:=l). instantiate (1:=gfs_l). clear - H.
                 repeat rewrite map_app in H. rewrite concat_app in H. generalize H. clear H.
                 match goal with [|- _ ((?l'++_) ++ _) -> _] => generalize l' end. intros.
                 rewrite <- map_app in H. induction l0... apply IHl0. inversion H...
              ** match goal with [_ : In x (_ (_ _ (_ _ (?l1 ++ _)))) |- _] => assert (l1 = []) end.
                 2:{ rewrite H3 in H0... }
                 clear - H2 H5. match goal with [|- ?lhs' = _] => set (lhs:=lhs'); case_eq lhs; intros end...
                 pose proof (in_eq p0 l). rewrite <- H in H0. unfold lhs in H0. rewrite filter_In in H0.
                 destruct H0. assert (H': exists q, fst p0 = local q). { destruct (fst p0)... discriminate. }
                 destruct H' as [q H']. assert (fst q = fst (fst a)). { eapply cfun_bods_type_names_l... }
                 rewrite H' in H1. simpl in *. rewrite H3 in H1. rewrite eq_TypeName_eq in H1. subst.
                 rewrite eq_TypeName_refl in H2. discriminate.
        -- rewrite H2 in *. simpl in *. inversion Aux; subst. pose proof H6 as H6'. eapply IHgfs_g0 in H6...
           ++ instantiate (1:=l). instantiate (1:=gfs_l). clear - H.
              repeat rewrite map_app in H. rewrite concat_app in H. generalize H. clear H.
              match goal with [|- _ ((?l'++_) ++ _) -> _] => generalize l' end. intros.
              rewrite <- map_app in H. induction l0... apply IHl0. inversion H...
           ++ rewrite <- flat_map_concat_map in H0. rewrite map_app in H0. rewrite flat_map_app in H0.
              apply in_app_or in H0. destruct H0; [| rewrite <- flat_map_concat_map]...
              exfalso. rename H into Uniq. clear - Uniq H0 H1 H2 H5 Aux. rewrite <- flat_map_concat_map in H1.
              rewrite in_flat_map in *. destruct H0. destruct H. do 2 destruct H1. rewrite in_map_iff in *.
              do 2 destruct H. do 2 destruct H1. rewrite <- flat_map_concat_map in H6.
              rewrite in_flat_map in H6. rewrite filter_In in H4. do 2 destruct H6. destruct H4.
              rewrite filter_In in H6. destruct H6.
              apply in_split in H4. do 2 destruct H4. rewrite H4 in Uniq. repeat (rewrite map_app in Uniq).
              simpl in Uniq. rewrite H in Uniq. apply in_split in H0. do 2 destruct H0. rewrite H0 in Uniq.
              repeat (rewrite concat_app in Uniq). simpl in Uniq.
              apply in_split in H6. do 2 destruct H6. rewrite H6 in Uniq. apply in_split in H7.
              do 2 destruct H7. repeat (rewrite map_app in Uniq). simpl in Uniq. rewrite H7 in Uniq.
              repeat (rewrite concat_app in Uniq). simpl in Uniq.
              repeat (rewrite map_app in Uniq). simpl in Uniq. rewrite H1 in Uniq.
              apply in_split in H3. do 2 destruct H3. rewrite H3 in Uniq. clear - Uniq.
              rewrite <- app_assoc in Uniq. generalize Uniq. clear Uniq. fold QName in *.
              match goal with [|- _ ((?l' ++ _ ++ _) ++ _ ++ _) -> _] => generalize l' end.
              clear. intros.
              match goal with [_ : Unique.unique ((l0++(x7++x::x8)++?r1)++?r2) |- _] =>
                assert (Unique.unique (x::x8++r1++r2)) end.
              { induction l0; induction x7; inversion Uniq; subst... do 2 rewrite app_nil_l in Uniq.
                clear - Uniq. rewrite <- app_comm_cons in Uniq. rewrite <- app_assoc in Uniq.
                rewrite app_assoc. rewrite app_comm_cons. rewrite <- app_assoc...
              }
              clear - H. inversion H; subst. apply H2. do 2 (apply in_or_app; right).
              repeat rewrite concat_app. do 2 (apply in_or_app; left). apply in_or_app. right.
              apply in_or_app. left. apply in_or_app. right. simpl. rewrite <- app_assoc. apply in_or_app.
              right. left...
      * rewrite app_assoc in H. rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H.
        simpl in H. repeat rewrite map_app in H. rewrite concat_app in H.
        rewrite <- app_assoc in H. apply Unique.uniqueness_app_not_in in H. rewrite Forall_forall in H.
        unfold not. intros. fold gfs_g in H. rewrite <- flat_map_concat_map in H1.
        rewrite in_flat_map in H1. do 2 destruct H1. rewrite in_map_iff in H1.
        do 2 destruct H1. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0.
        do 2 destruct H0. rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
        do 2 destruct H3. rewrite in_map_iff in H0. do 2 destruct H0.
        rewrite filter_In in H6. destruct H6. rewrite filter_In in H3. destruct H3.
        case_eq (fst x4); intros; rewrite H9 in H7; try discriminate.
        eapply H.
        -- rewrite <- flat_map_concat_map. rewrite in_flat_map. eexists. split.
           ++ rewrite in_map_iff. eexists. split... rewrite <- flat_map_concat_map. rewrite in_flat_map.
              eexists. split...
           ++ eauto.
        -- apply in_or_app. left. rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x2. split...
           rewrite in_map_iff. eexists. split...
}
clear H. rename H0 into H.

unfold fs in *. unfold cfs in *. unfold gfs_g in *. unfold gfs_l in *. clear fs cfs gfs_g gfs_l.

eapply unique_unordered; eauto; [apply QName_dec|].
unfold unordered_eq. split.
- intros. split; intros.
  + rewrite map_app in H0. rewrite map_map in H0. rewrite concat_app in H0.
    rewrite concat_app. apply in_app_or in H0. apply in_or_app. destruct H0; [left|]...
    rewrite map_app in H0. rewrite concat_app in H0. apply in_app_or in H0. destruct H0.
    * right. rewrite concat_app. apply in_or_app. left. rewrite concat_app.
      apply in_or_app. right. unfold l2. rewrite map_map. erewrite map_ext.
      2: { intros. rewrite map_map. simpl. match goal with [|- _ ?f _ = _ _] =>
             change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end... }
      rewrite <- map_map. erewrite map_ext.
      2: { intros. erewrite map_ext.
        2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
          change ((fst (proj1_sig ct)) (snd a1)) with ((fun x => (fst (proj1_sig ct)) (snd x)) a1)...
        }
        eauto.
      }
      rewrite <- concat_map. rewrite <- map_map...
    * right. rewrite concat_app. rewrite concat_app.
      assert (In a (concat (concat l1) ++ concat gbods)).
      2:{ apply in_app_or in H1. apply in_or_app. destruct H1; [|right]...
          left. apply in_or_app. left...
      }
      clear - H0. remember gbods. unfold gbods in Heql. rewrite concat_map in Heql.
      rewrite map_map in Heql. rewrite <- filter_map in Heql. rewrite map_map in Heql.
      simpl in Heql. erewrite map_ext in Heql.
      2: { intros. rewrite map_map. simpl. match goal with [|- _ ?f _ = _ _] =>
             change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end... }
      erewrite map_ext in Heql.
      2: { intros. erewrite map_ext.
        2: { intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
             change ((fst (proj1_sig ct)) (snd a1)) with ((fun x => (fst (proj1_sig ct)) (snd x)) a1)...
        }
        match goal with [|- map ?f _ = _] => change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end...
      }
      clear gbods. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0.
      destruct H0 as [x [H0_1 H0_2]]. rewrite in_map_iff in H0_1. destruct H0_1 as [x0 [H0_1 H0_1In]].
      do 2 rewrite <- flat_map_concat_map in H0_1In. apply in_app_or in H0_1In.
      destruct H0_1In.
      -- rewrite filter_In in H. rewrite in_flat_map in H. destruct H as [[x' [x'In1 x'In2]] x0Eq].
         apply in_app_or in x'In1. destruct x'In1.
         ++ case_eq (negb (eq_TypeName tn (fst (fst x')))); intros.
            ** apply in_or_app. right. subst. rewrite <- map_map. rewrite <- concat_map.
               rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x0. split...
               rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x'. split...
               rewrite filter_In. split...
            ** apply in_or_app. left. clear l Heql. unfold l1. clear l1.
               eapply In_concat... rewrite <- flat_map_concat_map. rewrite in_flat_map.
               set (lookup := lookup_ctor_sig (program_skeleton p) (fst x0)).
               assert (exists dtor, lookup = Some dtor).
               { pose proof (program_cfun_bods_typecheck_g p) as Typ. unfold cfun_bods_g_typecheck in Typ.
                 rewrite Forall_forall in Typ. apply Typ in H. clear Typ. destruct H as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as Len.
                 rewrite Nat.eqb_eq in Len. repeat rewrite map_length in Len. symmetry in Len.
                 pose proof (combine_in x'In2 Len). destruct H. unfold lookup.
                 unfold lookup_ctors in H11. unfold cfun_bod in *.
                 case_eq (filter (eq_TypeName (fst (fst x'))) (skeleton_dts (program_skeleton p)));
                   intros; rewrite H1 in H11; try discriminate. inversion H11; subst.
                 match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end; [exists c|]...
                 unfold lookup_ctor_sig in H2. pose proof H as H'. apply in_combine_l in H. rewrite filter_In in H.
                 destruct H. eapply find_none in H2... apply in_combine_switch in H'... rewrite Forall_forall in H12.
                 apply H12 in H'. destruct x0. destruct x. subst. simpl in *.
                 rewrite eq_ScopedName_refl in H2. discriminate.
               }
               unfold dtor in *. destruct H1 as [dtor dtorEq]. exists dtor. split.
               --- unfold lookup in *. unfold lookup_ctor_sig in dtorEq. apply find_some in dtorEq.
                   rewrite filter_In. destruct dtorEq. split... unfold gfunsigs_filterfun_l.
                   destruct dtor. rewrite eq_ScopedName_eq in H2. simpl in H2.
                   subst. destruct x0. simpl in *. destruct s...
               --- apply in_or_app. left. rewrite in_map_iff. exists (fst x', x0). simpl. rewrite H0_1. split...
                   rewrite filter_In. split.
                   +++ rewrite in_flat_map. exists x'. split... rewrite in_map_iff. exists x0. split...
                   +++ unfold gfunbods_filterfun_g. destruct x'. simpl. destruct q. destruct x0. simpl in *.
                       destruct s... rewrite negb_false_iff in H0. rewrite eq_TypeName_eq in H0. subst.
                       rewrite eq_TypeName_eq in x0Eq. simpl in x0Eq. subst.
                       unfold lookup in *. unfold lookup_ctor_sig in dtorEq. apply find_some in dtorEq.
                       destruct dtorEq. unfold eq_ScopedName in H1. destruct dtor. simpl in *.
                       destruct s; try discriminate. rewrite eq_QName_eq in H1. subst. simpl.
                       rewrite eq_TypeName_refl. rewrite eq_QName_refl...
         ++ apply in_or_app. left. clear l Heql. unfold l1. simpl. erewrite map_ext.
            2: { intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
              match goal with [|- map ?f (filter (_ (_ (_ a0))) ?m) = _] =>
                change (map f (filter (_ (_ (_ a0))) m)) with ((fun y => map f ((fun x =>
                  (filter (gfunbods_filterfun_l (unscope (fst x))) m)) y)) a0) end...
            }
            rewrite <- map_map. rewrite <- concat_map. rewrite <- flat_map_concat_map.
            rewrite in_flat_map. exists (fst x', x0). subst. split...
            rewrite <- flat_map_concat_map. rewrite in_flat_map.
            set (lookup := lookup_ctor_sig (program_skeleton p) (fst x0)).
            assert (exists dtor, lookup = Some dtor).
            { pose proof (program_cfun_bods_typecheck_l p) as Typ. unfold cfun_bods_l_typecheck in Typ.
              rewrite Forall_forall in Typ. apply Typ in H. clear Typ. destruct H as [qn [args [t [_ Typ]]]].
              inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H12) as Len.
              rewrite Nat.eqb_eq in Len. repeat rewrite map_length in Len. symmetry in Len.
              pose proof (combine_in x'In2 Len). destruct H. unfold lookup.
              unfold lookup_ctors in H10. unfold cfun_bod in *.
              case_eq (filter (eq_TypeName (fst (fst x'))) (skeleton_dts (program_skeleton p)));
                intros; rewrite H0 in H10; try discriminate. inversion H10; subst.
              match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end; [exists c|]...
              unfold lookup_ctor_sig in H1. pose proof H as H'. apply in_combine_l in H. rewrite filter_In in H.
              destruct H. eapply find_none in H1... apply in_combine_switch in H'... rewrite Forall_forall in H11.
              apply H11 in H'. destruct x0. destruct x. subst. simpl in *.
              rewrite eq_ScopedName_refl in H1. discriminate.
            }
            unfold dtor in *. destruct H0 as [dtor dtorEq]. exists dtor. split.
            ** rewrite filter_In. unfold lookup in *. unfold lookup_ctor_sig in dtorEq.
               apply find_some in dtorEq. destruct dtorEq. split...
               unfold gfunsigs_filterfun_g. destruct dtor.
               rewrite eq_ScopedName_eq in H1. simpl in H1. subst. destruct x0. simpl in *.
               destruct s...
            ** rewrite filter_In. rewrite in_flat_map. unfold gfunbods_filterfun_g. destruct x'.
               destruct q. simpl. destruct x0. simpl in x0Eq. destruct s; try discriminate.
               split.
               --- exists (t,n,c). split; [apply in_or_app; right|]... simpl in *. apply in_map...
               --- unfold lookup in *. unfold lookup_ctor_sig in dtorEq.
                   apply find_some in dtorEq. destruct dtorEq. rewrite eq_ScopedName_eq in H1.
                   simpl in H1. rewrite <- H1. simpl. rewrite eq_QName_refl. simpl in x'In2.
                   clear - H x'In2. rewrite andb_true_r. rewrite eq_TypeName_eq. symmetry.
                   change t with (fst (fst (t,n,c))). eapply cfun_bods_l_type_names_l...
      -- apply in_or_app. right. subst. rewrite <- map_map. rewrite <- concat_map.
         rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x0. split...
         rewrite <- flat_map_concat_map...
  + clear H. rewrite concat_app in H0. apply in_app_or in H0. rewrite map_app. rewrite map_app.
    rewrite concat_app. rewrite concat_app. apply in_or_app. rewrite map_map at 1.
    destruct H0; [left|]... right. rewrite concat_app in H. apply in_app_or in H. destruct H.
    * rewrite concat_app in H. apply in_app_or in H. apply in_or_app. destruct H.
      -- right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
         unfold l1 in H. clear l1 l2 gbods. erewrite map_ext in H.
         2: { intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
              match goal with [|- map ?f (filter (_ (_ (_ a0))) ?m) = _] =>
                change (map f (filter (_ (_ (_ a0))) m)) with ((fun y => map f ((fun x =>
                  (filter (gfunbods_filterfun_l (unscope (fst x))) m)) y)) a0) end...
         }
         rewrite <- map_map in H. rewrite <- concat_map in H. rewrite <- flat_map_concat_map in H.
         rewrite in_flat_map in H. do 2 destruct H. simpl in *. exists (snd (snd x)). split...
         apply in_map. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
         do 2 destruct H. apply in_or_app. left. rewrite filter_In. rewrite filter_In in H1.
         destruct H1. split.
         ++ rewrite <- flat_map_concat_map. rewrite in_flat_map. unfold cfun_bod in *.
            rewrite in_flat_map in H1. do 2 destruct H1. exists x1. split... rewrite in_map_iff in H3.
            do 2 destruct H3. subst...
         ++ rewrite in_flat_map in H1. do 2 destruct H1. rewrite in_map_iff in H3. do 2 destruct H3.
            subst. simpl. unfold gfunbods_filterfun_g in H2. destruct x1. destruct q. simpl in *.
            destruct x2. simpl. destruct s... rewrite filter_In in H. destruct H.
            unfold gfunsigs_filterfun_l in H3. destruct x0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in H3. subst. simpl in *. apply andb_prop in H2. destruct H2.
            unfold eq_QName in H3. destruct q0. destruct q. simpl in *. apply andb_prop in H3. destruct H3...
      -- left. unfold l2 in *. clear - H. unfold gfun_bod in *. rewrite <- concat_map in H.
         rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H. do 2 destruct H.
         rewrite in_flat_map. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
         do 2 destruct H. rewrite in_map_iff in H1. do 2 destruct H1. exists (snd x1).
         split.
         ++ apply in_map. destruct x1. simpl in *. rewrite <- flat_map_concat_map. rewrite in_flat_map.
            exists x0. split...
         ++ destruct x. simpl in *. inversion H1; subst. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0...
    * clear - H. apply in_or_app. right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
      unfold gbods in H. clear gbods. rewrite <- flat_map_concat_map. rewrite <- flat_map_concat_map in H.
      rewrite in_flat_map in H. do 2 destruct H. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
      do 2 destruct H. rewrite filter_In in H. rewrite in_map_iff in H. do 3 destruct H.
      destruct x0. inversion H; subst. simpl in *. destruct x. simpl in *. rewrite in_map_iff in H1.
      do 2 destruct H1. inversion H1; subst. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0.
      exists (snd x). split...
      apply in_map. apply in_or_app. right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
      exists x1. split... rewrite filter_In. split...
- rewrite <- flat_map_concat_map. unfold l1. unfold l2. unfold gbods. clear.
  rewrite concat_app. rewrite <- (flat_map_concat_map _ (program_fun_bods p)).
  rewrite app_length. rewrite flat_map_app. rewrite app_length. f_equal.
  + rewrite flat_map_concat_map. rewrite map_map. rewrite flat_map_concat_map...
  + rewrite concat_app. rewrite app_length. rewrite concat_app. rewrite app_length.
    rewrite <- plus_assoc. rewrite plus_comm. rewrite flat_map_app. rewrite app_length.
    rewrite <- plus_assoc. f_equal.
    * unfold gfun_bod. rewrite <- concat_map. rewrite <- map_map with (f:=snd).
      rewrite length_concat. rewrite flat_map_concat_map. rewrite length_concat.
      f_equal. repeat (rewrite map_map). rewrite concat_map. rewrite concat_map.
      repeat (rewrite map_map). unfold cfun_bod.
      match goal with [|- _ = _ (_ ?f' _)] => erewrite map_ext with (f:=f') end.
      2:{ intros. rewrite map_map. simpl. erewrite map_ext.
          2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
          reflexivity.
      }
      reflexivity.
    * rewrite map_app. rewrite flat_map_app. rewrite app_length. rewrite plus_comm. f_equal.
      -- unfold cfun_bod. rewrite flat_map_concat_map. rewrite length_concat. rewrite length_concat.
         f_equal. repeat (rewrite map_map). rewrite concat_map. rewrite concat_map.
         repeat (rewrite map_map). unfold cfun_bod. generalize (program_cfun_bods_g p). induction c...
         simpl in *. case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
         ++ unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite H.
            simpl. rewrite IHc. clear IHc. rewrite map_map. simpl. erewrite map_ext with (f:=fun x : ScopedName * expr =>
              length ((fst (proj1_sig ct)) (refunctionalize_expr tn (snd x)))).
            2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            reflexivity.
         ++ unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite H...
      -- simpl. erewrite map_ext with (A:=(ScopedName * list TypeName)%type).
         2:{ intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app. reflexivity. }
         rewrite <- map_map with (g:=map (fun a0 : QName * (ScopedName * expr) => (fst (proj1_sig ct)) (snd (snd a0)))).
         rewrite <- concat_map. change (fun a0 : QName * (ScopedName * expr) => collect_match_names (snd (snd a0)))
           with (fun a0 : QName * (ScopedName * expr) => collect_match_names ((fun x => (snd (snd x))) a0)).
         rewrite <- map_map with (g:=fst (proj1_sig ct)). do 2 rewrite <- flat_map_concat_map.

         match goal with [|- _ (_ _ (_ _ ?lhs)) = _] => replace lhs with
           (filter (fun x => if in_dec ScopedName_dec (fst x)
               (map fst (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))))
             then true else false) lhs) end.
         2:{ assert (Forall (fun x => In x (program_cfun_bods_g p ++ program_cfun_bods_l p))
               (program_cfun_bods_g p ++ program_cfun_bods_l p)). { rewrite Forall_forall... }
           generalize H. clear H. generalize (program_cfun_bods_g p ++ program_cfun_bods_l p) at - 1. induction l...
           intros. inversion H; subst. simpl. repeat rewrite filter_app. rewrite IHl... f_equal.
           clear IHl H. assert (Forall (fun x => In x (snd a)) (snd a)). { rewrite Forall_forall... }
           generalize H. clear H. generalize (snd a) at - 1. induction c...
           intros. rewrite filter_compose. inversion H; subst. simpl. case_eq (fst a0); intros.
           2:{ rewrite andb_false_r. rewrite filter_compose in IHc... }
           - case_eq (eq_TypeName tn (fst (unscope (local q)))); intros;
               [|rewrite andb_false_r; rewrite filter_compose in IHc]...
             match goal with [|- (if (if ?c then _ else _) && _ then _ else _) = _] =>
               assert (exists l, c = left l) end.
             { clear IHc. match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end...
               rename H6 into Contra.
               apply in_app_or in H2. destruct H2;
                 [ pose proof (program_cfun_bods_typecheck_g p) as Typ
                 | pose proof (program_cfun_bods_typecheck_l p) as Typ].
               - unfold cfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
                 apply Typ in H2. clear Typ. destruct H2 as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. unfold lookup_ctors in H16. fold cfun_bod in H16.
                 case_eq (filter (eq_TypeName (fst (fst a)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H2 in H16; try discriminate.
                 inversion H16; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H18).
                 repeat rewrite map_length in H6. rewrite Nat.eqb_eq in H6. symmetry in H6.
                 pose proof (combine_in H4 H6). destruct H7. apply in_combine_switch in H7...
                 rewrite Forall_forall in H17. pose proof H7 as H7'. apply H17 in H7. destruct a0. destruct x.
                 subst. apply in_combine_r in H7'. rewrite filter_In in H7'. destruct H7'. simpl in H0. subst.
                 assert (gfunsigs_filterfun_l tn (local q, l1) = true).
                 { unfold gfunsigs_filterfun_l. rewrite eq_TypeName_eq in H1. subst. rewrite eq_TypeName_refl... }
                 pose proof (conj H7 H0) as Aux. rewrite <- filter_In in Aux.
                 apply (in_map fst) in Aux. simpl in Aux.
                 clear - Aux Contra. exfalso. apply n...
               - unfold cfun_bods_l_typecheck in Typ. rewrite Forall_forall in Typ.
                 apply Typ in H2. clear Typ. destruct H2 as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. unfold lookup_ctors in H16. fold cfun_bod in H16.
                 case_eq (filter (eq_TypeName (fst (fst a)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H2 in H16; try discriminate.
                 inversion H16; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H18).
                 repeat rewrite map_length in H6. rewrite Nat.eqb_eq in H6. symmetry in H6.
                 pose proof (combine_in H4 H6). destruct H7. apply in_combine_switch in H7...
                 rewrite Forall_forall in H17. pose proof H7 as H7'. apply H17 in H7. destruct a0. destruct x.
                 subst. apply in_combine_r in H7'. rewrite filter_In in H7'. destruct H7'. simpl in H0. subst.
                 assert (gfunsigs_filterfun_l tn (local q, l1) = true).
                 { unfold gfunsigs_filterfun_l. rewrite eq_TypeName_eq in H1. subst. rewrite eq_TypeName_refl... }
                 pose proof (conj H7 H0) as Aux. rewrite <- filter_In in Aux.
                 apply (in_map fst) in Aux. simpl in Aux.
                 clear - Aux Contra. exfalso. apply n...
             }
             destruct H6. rewrite H6. simpl. f_equal. rewrite filter_compose in IHc...
         }
         assert (Filter: Forall (fun x => gfunsigs_filterfun_l tn x = true)
           (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p)))).
         { rewrite Forall_forall. intros x H. rewrite filter_In in H. destruct H... }
         generalize Filter. clear Filter.
         assert (Subl : Sublist.sublist (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p)))
           (skeleton_ctors (program_skeleton p))).
         { apply Sublist.sublist_filter. }
         generalize Subl. clear Subl.
         generalize (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))). induction l; intros.
         ++ simpl. match goal with [|- _ (_ _ (_ _ (filter _ ?l))) = _] => induction l end...
         ++ simpl in *. rewrite map_app. do 2 rewrite flat_map_app. rewrite app_length. rewrite <- IHl.
            2:{ eapply Sublist.sublist_trans... constructor. apply Sublist.sublist_refl. }
            2:{ inversion Filter... }
            clear IHl.
            assert (H: exists l0, l0 ++ (program_cfun_bods_g p ++ program_cfun_bods_l p) =
              (program_cfun_bods_g p ++ program_cfun_bods_l p)).
            { exists []... }
            generalize H. clear H.
            change (list (prod ScopedName expr)) with cfun_bod.
            change (prod QName cfun_bod) with cfun_bod_named.
            rewrite <- flat_map_app.
            generalize (program_cfun_bods_g p ++ program_cfun_bods_l p) at - 2.
            induction l0; intros...
            assert (H0: (exists l1 : list cfun_bod_named,
              l1 ++ l0 = program_cfun_bods_g p ++ program_cfun_bods_l p)).
            { clear - H. destruct H. exists (x++[a0]). rewrite <- app_assoc... }
            rename H into InBods. apply IHl0 in H0. clear IHl0. simpl.
            rewrite filter_app with (P:=gfunbods_filterfun_l (unscope (fst a))).
            rewrite map_app. rewrite flat_map_app. rewrite app_length.
            rewrite filter_app. rewrite filter_app. rewrite filter_app.
            rewrite map_app. rewrite map_app. rewrite flat_map_app. rewrite flat_map_app.
            rewrite app_length. rewrite app_length.
            match goal with [|- _ = ?n1 + ?n2 + (?n3 + ?n4)] => replace (n1 + n2 + (n3 + n4)) with
              ((n1 + n3) + (n2 + n4)) end; try omega.
            rewrite <- H0. clear H0. f_equal.
            rewrite <- app_length. rewrite <- flat_map_app.
            assert (H: exists a, fst a = fst a0 /\ snd a = snd a0 /\
              exists a' a0, a0 ++ snd a = a' /\ In (fst a, a') (program_cfun_bods_g p ++ program_cfun_bods_l p)).
            { exists a0. split... split... destruct InBods. rewrite <- H. exists (snd a0). exists []. split...
              apply in_or_app. right. left... destruct a0...
            }
            generalize H. generalize (snd a0). induction c; intros...
            assert (Aux: exists a, fst a = fst a0 /\ snd a = c /\
              exists a' a0, a0 ++ snd a = a' /\  In (fst a, a') (program_cfun_bods_g p ++ program_cfun_bods_l p)).
            { clear - H0. destruct H0. destruct H. destruct H0. exists (fst x, c). split... split...
              do 3 destruct H1. simpl. exists x0. rewrite <- H1. exists (x1++[a1]). rewrite H0. rewrite <- app_assoc. split...
              rewrite <- H0. rewrite H1...
            }
            simpl. case_eq (fst a1); intros.
            2:{ destruct a0. destruct q0. simpl. destruct a1. simpl in H1. subst s... }
            ** destruct a0. destruct q0. simpl. destruct a1. simpl in H1. subst s.
               case_eq (eq_TypeName tn (fst q)); intros.
               --- cbn. case_eq (ScopedName_dec (fst a) (local q)); intros.
                   +++ cbn. rewrite app_length. rewrite IHc... clear IHc.
                       case_eq (eq_TypeName t (fst (unscope (fst a))) &&
                         eq_QName (unscope (fst a)) q); intros.
                       *** cbn. rewrite app_length. f_equal.
                           assert (Aux2: exists r, in_dec ScopedName_dec (local q) (map fst l) = right r).
                           { pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
                             unfold dts_ctor_names_unique in Uniq. eapply Sublist.sublist_map in Subl.
                             pose proof (Unique.uniqueness_sublist _ _ Subl Uniq) as Done.
                             simpl in Done. inversion Done; subst. rewrite e0 in H6.
                             case_eq (in_dec ScopedName_dec (local q) (map fst l)); intros.
                             - exfalso. apply H6...
                             - exists n0...
                           }
                           destruct Aux2 as [r Aux2]. rewrite Aux2...
                       *** rewrite e0 in H3. simpl in H3. rewrite eq_QName_refl in H3.
                           rewrite andb_false_iff in H3. destruct H3; try discriminate.
                           destruct H0 as [aH [H_1 [H_2 [aH_3 [a'H_3 [H_3_1 H_3_2]]]]]].
                           simpl in *. subst. destruct aH. simpl in *. destruct q0. inversion H_1; subst.
                           clear - H1 H3 H_3_2. destruct q. simpl in *. rewrite eq_TypeName_eq in H1. subst.
                           assert (t = t0). 2:{ subst. rewrite eq_TypeName_refl in H3. discriminate. }
                           clear H3. pose proof (program_cfun_bods_typecheck_g p) as Typ_g.
                           pose proof (program_cfun_bods_typecheck_l p) as Typ_l.
                           unfold cfun_bods_g_typecheck in Typ_g. unfold cfun_bods_l_typecheck in Typ_l.
                           rewrite Forall_forall in *. apply in_app_or in H_3_2. destruct H_3_2.
                           { apply Typ_g in H. do 4 destruct H. clear - H0. inversion H0; subst.
                             simpl in *.
                             set (el1:=(local (t0,n0),e)). set (el2:=nth (length a'H_3) ctorlist (local (t, n0), x0)).
                             set (el:=(el1,el2)).
                             assert (length (a'H_3 ++ (local (t0, n0), e) :: c) = length ctorlist) as LenAux.
                             { symmetry. apply Nat.eqb_eq. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as H.
                               do 2 rewrite map_length in H...
                             }
                             assert (length a'H_3 < length ctorlist) as Len.
                             { rewrite app_length in LenAux. simpl in LenAux. omega. }
                             assert (In el (combine (a'H_3 ++ (local (t0, n0), e) :: c) ctorlist)).
                             { unfold el. unfold el2. unfold el1. replace (local (t0, n0), e) with
                                 (nth (length a'H_3) (a'H_3 ++ (local (t0, n0), e) :: c) (local (t0, n0), e)).
                               2:{ rewrite app_nth2... rewrite Nat.sub_diag... }
                               rewrite <- combine_nth... rewrite app_nth2... rewrite Nat.sub_diag. apply nth_In.
                               rewrite combine_length. simpl. rewrite LenAux. rewrite Nat.min_id...
                             }
                             rewrite Forall_forall in H12. apply H12 in H. unfold el in H.
                             unfold lookup_ctors in H11.
                             case_eq (filter (eq_TypeName t) (skeleton_dts (program_skeleton p))); intros;
                               rewrite H1 in H11; try discriminate.
                             inversion H11; subst. unfold el1 in H.
                             remember el2 as el2'. destruct el2'. destruct s; try discriminate.
                             destruct q. inversion H; subst. unfold el2 in Heqel2'.
                             pose proof (nth_In _ (local (t, n1), x0)  Len) as H2. rewrite <- Heqel2' in H2.
                             rewrite filter_In in H2. destruct H2 as [_ H2]. rewrite eq_TypeName_eq in H2. simpl in *...
                           }
                           { apply Typ_l in H. do 4 destruct H. clear - H0. inversion H0; subst.
                             simpl in *.
                             set (el1:=(local (t0,n0),e)). set (el2:=nth (length a'H_3) ctorlist (local (t, n0), x0)).
                             set (el:=(el1,el2)).
                             assert (length (a'H_3 ++ (local (t0, n0), e) :: c) = length ctorlist) as LenAux.
                             { symmetry. apply Nat.eqb_eq. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as H.
                               do 2 rewrite map_length in H...
                             }
                             assert (length a'H_3 < length ctorlist) as Len.
                             { rewrite app_length in LenAux. simpl in LenAux. omega. }
                             assert (In el (combine (a'H_3 ++ (local (t0, n0), e) :: c) ctorlist)).
                             { unfold el. unfold el2. unfold el1. replace (local (t0, n0), e) with
                                 (nth (length a'H_3) (a'H_3 ++ (local (t0, n0), e) :: c) (local (t0, n0), e)).
                               2:{ rewrite app_nth2... rewrite Nat.sub_diag... }
                               rewrite <- combine_nth... rewrite app_nth2... rewrite Nat.sub_diag. apply nth_In.
                               rewrite combine_length. simpl. rewrite LenAux. rewrite Nat.min_id...
                             }
                             rewrite Forall_forall in H12. apply H12 in H. unfold el in H.
                             unfold lookup_ctors in H11.
                             case_eq (filter (eq_TypeName t) (skeleton_dts (program_skeleton p))); intros;
                               rewrite H1 in H11; try discriminate.
                             inversion H11; subst. unfold el1 in H.
                             remember el2 as el2'. destruct el2'. destruct s; try discriminate.
                             destruct q. inversion H; subst. unfold el2 in Heqel2'.
                             pose proof (nth_In _ (local (t, n1), x0)  Len) as H2. rewrite <- Heqel2' in H2.
                             rewrite filter_In in H2. destruct H2 as [_ H2]. rewrite eq_TypeName_eq in H2. simpl in *...
                           }
                   +++ assert (qEq: eq_QName (unscope (fst a)) q = false).
                       { case_eq (eq_QName (unscope (fst a)) q); intros... rewrite eq_QName_eq in *.
                         subst. exfalso. apply n0. inversion Filter; subst. unfold gfunsigs_filterfun_g in H2.
                         destruct a. destruct s; try discriminate...
                       }
                       rewrite qEq. rewrite andb_false_r.
                       case_eq (in_dec ScopedName_dec (local q) (map fst l)); intros...
                       cbn. rewrite app_length. rewrite flat_map_app. rewrite app_length. cbn.
                       rewrite app_length. apply IHc in Aux. rewrite flat_map_app in Aux.
                       rewrite app_length in Aux. simpl in *. omega.
               --- rewrite IHc... case_eq (eq_QName (unscope (fst a)) q); intros.
                   +++ rewrite eq_QName_eq in H2. subst. inversion Filter; subst.
                       unfold gfunsigs_filterfun_l in H4. destruct a. destruct s; try discriminate.
                       simpl in H1. rewrite H1 in H4. discriminate.
                   +++ rewrite andb_false_r...
Qed.


Lemma new_match_names_unique_cbods_l_gbods_g : forall p tn (ct : collect_tuple)
  (CfunLMUnique1 : Unique.unique
    (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_g p)))))
  (CfunLMUnique2 : Forall
    (fun x => ~ In x (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_g p)))))
    (concat (map (fst (proj1_sig ct))
      (map snd (program_fun_bods p) ++
       map snd (concat (map snd (program_cfun_bods_l p))) ++
       map snd (concat (map snd (program_gfun_bods_g p))))))),
  (snd (proj1_sig ct)) (new_fun_bods p tn) (new_cfun_bods_l p tn) (new_gfun_bods_g p tn).
Proof with eauto.
intros.
pose proof (program_match_names_unique_cbods_l_gbods_g p ct) as Aux.
rewrite (proj1 (proj2 (proj2_sig ct))) in Aux.
pose proof (Unique.uniqueness_app _ _ Aux CfunLMUnique1 CfunLMUnique2).
clear Aux.
clear CfunLMUnique1 CfunLMUnique2.

(*[> Structurally different part (compared with defunc) no. 1 <]*)
rewrite <- flat_map_concat_map in H. rewrite flat_map_app in H. rewrite flat_map_app in H.
rewrite <- app_assoc in H. rewrite <- app_assoc in H.
(*[> Refunc-specific <]*)
rewrite app_assoc in H. apply Unique.unique_app_switch in H.
rewrite <- app_assoc in H.
rewrite app_assoc with (l:=_ _ (_ _ (_ (_ _ (program_cfun_bods_l p))))) in H.
apply Unique.unique_app_switch in H.
(*[> End Refunc-specific <]*)
repeat (rewrite <- flat_map_app in H). rewrite flat_map_concat_map in H.
unfold cfun_bod in *. rewrite <- (flat_map_concat_map snd (program_cfun_bods_l p)) in H.
rewrite <- map_app in H. rewrite <- flat_map_app in H. rewrite flat_map_concat_map in H.

rewrite (proj1 (proj2 (proj2_sig ct))) in *.
unfold new_fun_bods in *. unfold new_cfun_bods_l in *. unfold new_gfun_bods_g in *.
repeat (repeat (rewrite map_app); repeat (rewrite map_map); simpl).
match goal with [|- _ (_ ((map ?f ?l) ++ _ ++ _))] =>
  replace (map f l) with (map (fun x => (fst (proj1_sig ct)) (snd x)) l) end.
2:{ apply map_ext. intros. symmetry. apply (proj1 (proj2 (proj2 (proj2_sig ct)))). }

(*[> Structurally different part no. 2, entirely refunc-specific <]*)
repeat rewrite map_app. apply uniqueness_concat_app_switch.

rewrite concat_map. rewrite map_app. rewrite map_map. erewrite map_ext_in with (l:=filter _ _).
2:{ intros. rewrite map_app. rewrite map_map. simpl. unfold globalize_aux. unfold localize_aux.
  rewrite map_map. simpl. rewrite map_map. simpl. rewrite map_map.
  erewrite map_ext.
  2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
  erewrite map_ext with (l:=filter _ (flat_map _ (program_cfun_bods_l p))).
  2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
  reflexivity.
}
match goal with [|- _ (_ (_ ++ (_ (?l1' ++ ?l2')) ++ ?gbods'))] =>
  set (l1:=l1'); set (l2:=l2'); set (gbods:=gbods') end.
rewrite concat_app with (l2:=l2).

match goal with
  [_ : Unique.unique (_ (_ _ (?fs' ++ ?cfs' ++ map snd (concat (map snd (?gfs_g' ++ ?gfs_l')))))) |- _] =>
    set (fs:=fs') in *; set (cfs:=cfs') in *; set (gfs_g:=gfs_g'); set (gfs_l:=gfs_l') in * end.
assert (Unique.unique (concat (map (fst (proj1_sig ct)) (fs ++ cfs ++ (map snd
    (filter (fun x => match fst x with global _ => eq_TypeName tn (fst (unscope (fst x))) | _ => false end)
      (concat (map snd (gfs_g ++ gfs_l))) ++
    (concat (map snd (filter (fun x => negb (eq_TypeName tn (fst (fst x)))) (gfs_g)))))))))) as H0.
{ repeat rewrite map_app. repeat rewrite concat_app. rewrite app_assoc. rewrite app_assoc.
  apply Unique.uniqueness_app.
  - eapply Unique.uniqueness_sublist; [|apply H]. repeat rewrite map_app. repeat rewrite concat_app.
    rewrite <- app_assoc. repeat (apply Sublist.sublist_app; try apply Sublist.sublist_refl).
    fold gfs_g. unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *.
    generalize (concat (map snd gfs_g) ++ concat (map snd gfs_l)). clear.
    induction l; [constructor|]. simpl. case_eq (fst a); intros.
    + rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app... constructor.
    + case_eq (eq_TypeName tn (fst (unscope (global q)))); intros.
      * simpl. apply Sublist.sublist_app... apply Sublist.sublist_refl.
      * rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app... constructor.
  - eapply Unique.uniqueness_sublist... fold gfs_g.
    repeat (rewrite map_app; rewrite map_app; rewrite concat_app).
    rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app; [constructor|].
    rewrite concat_app. rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app; [constructor|].
    generalize gfs_g. clear. induction gfs_g; [constructor|].
    simpl. unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
    case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
    + simpl. repeat (rewrite map_app; rewrite map_app; rewrite concat_app). apply Sublist.sublist_app...
      apply Sublist.sublist_refl.
    + repeat rewrite map_app. rewrite concat_app. rewrite <- (app_nil_l (concat _)).
      apply Sublist.sublist_app; [constructor|]. rewrite <- map_app. apply IHgfs_g.
  - clear - H. rewrite Forall_forall. intros. apply in_app_or in H0. destruct H0.
    + repeat (rewrite map_app in H; rewrite concat_app in H). rewrite app_assoc in H.
      apply Unique.uniqueness_app_not_in in H. rewrite Forall_forall in H.
      apply H in H0. unfold not. intros. apply H0. fold gfs_g. clear - H1.
      generalize dependent gfs_g. induction gfs_g; intros; [exfalso|]...
      simpl in *. repeat rewrite map_app. repeat rewrite concat_app. rewrite <- app_assoc.
      unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
      case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
      * rewrite H in *. simpl in *. repeat rewrite map_app in H1. rewrite concat_app in H1.
        apply in_or_app. apply in_app_or in H1. destruct H1; [left|]...
        right. rewrite <- concat_app. repeat rewrite <- map_app...
      * rewrite H in *. simpl in *. apply in_or_app. right.
        rewrite <- concat_app. repeat rewrite <- map_app...
    + rewrite filter_app in H0. repeat rewrite map_app in H0. rewrite concat_app in H0.
      apply in_app_or in H0. repeat rewrite map_app in H. repeat rewrite concat_app in H. destruct H0.
      * rewrite app_assoc in H. rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H.
        fold gfs_g in H. generalize H H0.
        match goal with [|- _ (_ ++ _ ++ ?l') -> _] => generalize l' end.
        rewrite <- concat_app. rewrite <- map_app.
        generalize gfs_l. assert (Forall (fun x => In x gfs_g) gfs_g) as Aux.
        { rewrite Forall_forall... }
        generalize Aux. generalize gfs_g at - 1. clear. induction gfs_g0; intros...
        unfold not. intros. simpl in *. rewrite filter_app in H0.
        unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
        case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
        -- rewrite H2 in *. simpl in *. repeat rewrite map_app in H1. rewrite concat_app in H1.
           apply in_app_or in H1. destruct H1.
           ++ inversion Aux; subst. repeat rewrite map_app in H0. rewrite concat_app in H0.
              apply in_app_or in H0. destruct H0.
              ** rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. do 2 destruct H0.
                 rewrite in_map_iff in H0. do 2 destruct H0. rewrite filter_In in H4. destruct H4.
                 case_eq (fst x1); intros; rewrite H8 in H7; try discriminate. simpl in *.
                 assert (Aux2: fst q = fst (fst a)).
                 { eapply cfun_bods_l_type_names... }
                 rewrite <- Aux2 in H2. rewrite eq_TypeName_eq in *. subst. rewrite eq_TypeName_refl in H2.
                 discriminate.
              ** clear IHgfs_g0 Aux. repeat rewrite map_app in H. rewrite concat_app in H.
                 apply in_split in H1. do 2 destruct H1. rewrite H1 in H.
                 rewrite <- app_assoc in H. rewrite <- app_assoc in H. rewrite <- app_nil_l in H.
                 apply Unique.unique_app_switch in H. inversion H; subst. apply H7.
                 apply in_or_app. left. apply in_or_app. right. clear - H0.
                 rewrite <- flat_map_concat_map in *. apply in_or_app. left. rewrite concat_app. rewrite map_app.
                 rewrite flat_map_app. apply in_or_app. left. rewrite in_flat_map in *.
                 destruct H0. destruct H. exists x0. split... clear - H. rewrite in_map_iff in *.
                 do 2 destruct H. exists x. split... rewrite filter_In in H0. destruct H0...
           ++ inversion Aux; subst. pose proof H6 as H6'. eapply IHgfs_g0 in H6...
              ** instantiate (1:=l). instantiate (1:=gfs_l). clear - H.
                 repeat rewrite map_app in H. rewrite concat_app in H. generalize H. clear H.
                 match goal with [|- _ ((?l'++_) ++ _) -> _] => generalize l' end. intros.
                 rewrite <- map_app in H. induction l0... apply IHl0. inversion H...
              ** match goal with [_ : In x (_ (_ _ (_ _ (?l1 ++ _)))) |- _] => assert (l1 = []) end.
                 2:{ rewrite H3 in H0... }
                 clear - H2 H5. match goal with [|- ?lhs' = _] => set (lhs:=lhs'); case_eq lhs; intros end...
                 pose proof (in_eq p0 l). rewrite <- H in H0. unfold lhs in H0. rewrite filter_In in H0.
                 destruct H0. assert (H': exists q, fst p0 = global q). { destruct (fst p0)... discriminate. }
                 destruct H' as [q H']. assert (fst q = fst (fst a)). { eapply cfun_bods_l_type_names... }
                 rewrite H' in H1. simpl in *. rewrite H3 in H1. rewrite eq_TypeName_eq in H1. subst.
                 rewrite eq_TypeName_refl in H2. discriminate.
        -- rewrite H2 in *. simpl in *. inversion Aux; subst. pose proof H6 as H6'. eapply IHgfs_g0 in H6...
           ++ instantiate (1:=l). instantiate (1:=gfs_l). clear - H.
              repeat rewrite map_app in H. rewrite concat_app in H. generalize H. clear H.
              match goal with [|- _ ((?l'++_) ++ _) -> _] => generalize l' end. intros.
              rewrite <- map_app in H. induction l0... apply IHl0. inversion H...
           ++ rewrite <- flat_map_concat_map in H0. rewrite map_app in H0. rewrite flat_map_app in H0.
              apply in_app_or in H0. destruct H0; [| rewrite <- flat_map_concat_map]...
              exfalso. rename H into Uniq. clear - Uniq H0 H1 H2 H5 Aux. rewrite <- flat_map_concat_map in H1.
              rewrite in_flat_map in *. destruct H0. destruct H. do 2 destruct H1. rewrite in_map_iff in *.
              do 2 destruct H. do 2 destruct H1. rewrite <- flat_map_concat_map in H6.
              rewrite in_flat_map in H6. rewrite filter_In in H4. do 2 destruct H6. destruct H4.
              rewrite filter_In in H6. destruct H6.
              apply in_split in H4. do 2 destruct H4. rewrite H4 in Uniq. repeat (rewrite map_app in Uniq).
              simpl in Uniq. rewrite H in Uniq. apply in_split in H0. do 2 destruct H0. rewrite H0 in Uniq.
              repeat (rewrite concat_app in Uniq). simpl in Uniq.
              apply in_split in H6. do 2 destruct H6. rewrite H6 in Uniq. apply in_split in H7.
              do 2 destruct H7. repeat (rewrite map_app in Uniq). simpl in Uniq. rewrite H7 in Uniq.
              repeat (rewrite concat_app in Uniq). simpl in Uniq.
              repeat (rewrite map_app in Uniq). simpl in Uniq. rewrite H1 in Uniq.
              apply in_split in H3. do 2 destruct H3. rewrite H3 in Uniq. clear - Uniq.
              rewrite <- app_assoc in Uniq. generalize Uniq. clear Uniq. fold QName in *.
              match goal with [|- _ ((?l' ++ _ ++ _) ++ _ ++ _) -> _] => generalize l' end.
              clear. intros.
              match goal with [_ : Unique.unique ((l0++(x7++x::x8)++?r1)++?r2) |- _] =>
                assert (Unique.unique (x::x8++r1++r2)) end.
              { induction l0; induction x7; inversion Uniq; subst... do 2 rewrite app_nil_l in Uniq.
                clear - Uniq. rewrite <- app_comm_cons in Uniq. rewrite <- app_assoc in Uniq.
                rewrite app_assoc. rewrite app_comm_cons. rewrite <- app_assoc...
              }
              clear - H. inversion H; subst. apply H2. do 2 (apply in_or_app; right).
              repeat rewrite concat_app. do 2 (apply in_or_app; left). apply in_or_app. right.
              apply in_or_app. left. apply in_or_app. right. simpl. rewrite <- app_assoc. apply in_or_app.
              right. left...
      * rewrite app_assoc in H. rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H.
        simpl in H. repeat rewrite map_app in H. rewrite concat_app in H.
        rewrite <- app_assoc in H. apply Unique.uniqueness_app_not_in in H. rewrite Forall_forall in H.
        unfold not. intros. fold gfs_g in H. rewrite <- flat_map_concat_map in H1.
        rewrite in_flat_map in H1. do 2 destruct H1. rewrite in_map_iff in H1.
        do 2 destruct H1. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0.
        do 2 destruct H0. rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
        do 2 destruct H3. rewrite in_map_iff in H0. do 2 destruct H0.
        rewrite filter_In in H6. destruct H6. rewrite filter_In in H3. destruct H3.
        case_eq (fst x4); intros; rewrite H9 in H7; try discriminate.
        eapply H.
        -- rewrite <- flat_map_concat_map. rewrite in_flat_map. eexists. split.
           ++ rewrite in_map_iff. eexists. split... rewrite <- flat_map_concat_map. rewrite in_flat_map.
              eexists. split...
           ++ eauto.
        -- apply in_or_app. left. rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x2. split...
           rewrite in_map_iff. eexists. split...
}
clear H. rename H0 into H.

unfold fs in *. unfold cfs in *. unfold gfs_g in *. unfold gfs_l in *. clear fs cfs gfs_g gfs_l.

eapply unique_unordered; eauto; [apply QName_dec|].
unfold unordered_eq. split.
- intros. split; intros.
  + rewrite map_app in H0. rewrite map_map in H0. rewrite concat_app in H0.
    rewrite concat_app. apply in_app_or in H0. apply in_or_app. destruct H0; [left|]...
    rewrite map_app in H0. rewrite concat_app in H0. apply in_app_or in H0. destruct H0.
    * right. rewrite concat_app. apply in_or_app. left. rewrite concat_app.
      apply in_or_app. right. unfold l2. rewrite map_map. erewrite map_ext.
      2: { intros. rewrite map_map. simpl. match goal with [|- _ ?f _ = _ _] =>
             change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end... }
      rewrite <- map_map. erewrite map_ext.
      2: { intros. erewrite map_ext.
        2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
          change ((fst (proj1_sig ct)) (snd a1)) with ((fun x => (fst (proj1_sig ct)) (snd x)) a1)...
        }
        eauto.
      }
      rewrite <- concat_map. rewrite <- map_map...
    * right. rewrite concat_app. rewrite concat_app.
      assert (In a (concat (concat l1) ++ concat gbods)).
      2:{ apply in_app_or in H1. apply in_or_app. destruct H1; [|right]...
          left. apply in_or_app. left...
      }
      clear - H0. remember gbods. unfold gbods in Heql. rewrite concat_map in Heql.
      rewrite map_map in Heql. rewrite <- filter_map in Heql. rewrite map_map in Heql.
      simpl in Heql. erewrite map_ext in Heql.
      2: { intros. rewrite map_map. simpl. match goal with [|- _ ?f _ = _ _] =>
             change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end... }
      erewrite map_ext in Heql.
      2: { intros. erewrite map_ext.
        2: { intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
             change ((fst (proj1_sig ct)) (snd a1)) with ((fun x => (fst (proj1_sig ct)) (snd x)) a1)...
        }
        match goal with [|- map ?f _ = _] => change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end...
      }
      clear gbods. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0.
      destruct H0 as [x [H0_1 H0_2]]. rewrite in_map_iff in H0_1. destruct H0_1 as [x0 [H0_1 H0_1In]].
      do 2 rewrite <- flat_map_concat_map in H0_1In. apply in_app_or in H0_1In.
      destruct H0_1In.
      -- rewrite filter_In in H. rewrite in_flat_map in H. destruct H as [[x' [x'In1 x'In2]] x0Eq].
         apply in_app_or in x'In1. destruct x'In1.
         ++ case_eq (negb (eq_TypeName tn (fst (fst x')))); intros.
            ** apply in_or_app. right. subst. rewrite <- map_map. rewrite <- concat_map.
               rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x0. split...
               rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x'. split...
               rewrite filter_In. split...
            ** apply in_or_app. left. clear l Heql. unfold l1. clear l1.
               eapply In_concat... rewrite <- flat_map_concat_map. rewrite in_flat_map.
               set (lookup := lookup_ctor_sig (program_skeleton p) (fst x0)).
               assert (exists dtor, lookup = Some dtor).
               { pose proof (program_cfun_bods_typecheck_l p) as Typ. unfold cfun_bods_l_typecheck in Typ.
                 rewrite Forall_forall in Typ. apply Typ in H. clear Typ. destruct H as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as Len.
                 rewrite Nat.eqb_eq in Len. repeat rewrite map_length in Len. symmetry in Len.
                 pose proof (combine_in x'In2 Len). destruct H. unfold lookup.
                 unfold lookup_ctors in H11. unfold cfun_bod in *.
                 case_eq (filter (eq_TypeName (fst (fst x'))) (skeleton_dts (program_skeleton p)));
                   intros; rewrite H1 in H11; try discriminate. inversion H11; subst.
                 match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end; [exists c|]...
                 unfold lookup_ctor_sig in H2. pose proof H as H'. apply in_combine_l in H. rewrite filter_In in H.
                 destruct H. eapply find_none in H2... apply in_combine_switch in H'... rewrite Forall_forall in H12.
                 apply H12 in H'. destruct x0. destruct x. subst. simpl in *.
                 rewrite eq_ScopedName_refl in H2. discriminate.
               }
               unfold dtor in *. destruct H1 as [dtor dtorEq]. exists dtor. split.
               --- unfold lookup in *. unfold lookup_ctor_sig in dtorEq. apply find_some in dtorEq.
                   rewrite filter_In. destruct dtorEq. split... unfold gfunsigs_filterfun_g.
                   destruct dtor. rewrite eq_ScopedName_eq in H2. simpl in H2.
                   subst. destruct x0. simpl in *. destruct s...
               --- apply in_or_app. right. rewrite in_map_iff. exists (fst x', x0). simpl. rewrite H0_1. split...
                   rewrite filter_In. split.
                   +++ rewrite in_flat_map. exists x'. split... rewrite in_map_iff. exists x0. split...
                   +++ unfold gfunbods_filterfun_g. destruct x'. simpl. destruct q. destruct x0. simpl in *.
                       destruct s... rewrite negb_false_iff in H0. rewrite eq_TypeName_eq in H0. subst.
                       rewrite eq_TypeName_eq in x0Eq. simpl in x0Eq. subst.
                       unfold lookup in *. unfold lookup_ctor_sig in dtorEq. apply find_some in dtorEq.
                       destruct dtorEq. unfold eq_ScopedName in H1. destruct dtor. simpl in *.
                       destruct s; try discriminate. rewrite eq_QName_eq in H1. subst. simpl.
                       rewrite eq_TypeName_refl. rewrite eq_QName_refl...
         ++ apply in_or_app. left. clear l Heql. unfold l1. simpl. erewrite map_ext.
            2: { intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
              match goal with [|- map ?f (filter (_ (_ (_ a0))) ?m) = _] =>
                change (map f (filter (_ (_ (_ a0))) m)) with ((fun y => map f ((fun x =>
                  (filter (gfunbods_filterfun_g (unscope (fst x))) m)) y)) a0) end...
            }
            rewrite <- map_map. rewrite <- concat_map. rewrite <- flat_map_concat_map.
            rewrite in_flat_map. exists (fst x', x0). subst. split...
            rewrite <- flat_map_concat_map. rewrite in_flat_map.
            set (lookup := lookup_ctor_sig (program_skeleton p) (fst x0)).
            assert (exists dtor, lookup = Some dtor).
            { pose proof (program_cfun_bods_typecheck_g p) as Typ. unfold cfun_bods_g_typecheck in Typ.
              rewrite Forall_forall in Typ. apply Typ in H. clear Typ. destruct H as [qn [args [t [_ Typ]]]].
              inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H12) as Len.
              rewrite Nat.eqb_eq in Len. repeat rewrite map_length in Len. symmetry in Len.
              pose proof (combine_in x'In2 Len). destruct H. unfold lookup.
              unfold lookup_ctors in H10. unfold cfun_bod in *.
              case_eq (filter (eq_TypeName (fst (fst x'))) (skeleton_dts (program_skeleton p)));
                intros; rewrite H0 in H10; try discriminate. inversion H10; subst.
              match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end; [exists c|]...
              unfold lookup_ctor_sig in H1. pose proof H as H'. apply in_combine_l in H. rewrite filter_In in H.
              destruct H. eapply find_none in H1... apply in_combine_switch in H'... rewrite Forall_forall in H11.
              apply H11 in H'. destruct x0. destruct x. subst. simpl in *.
              rewrite eq_ScopedName_refl in H1. discriminate.
            }
            unfold dtor in *. destruct H0 as [dtor dtorEq]. exists dtor. split.
            ** rewrite filter_In. unfold lookup in *. unfold lookup_ctor_sig in dtorEq.
               apply find_some in dtorEq. destruct dtorEq. split...
               unfold gfunsigs_filterfun_g. destruct dtor.
               rewrite eq_ScopedName_eq in H1. simpl in H1. subst. destruct x0. simpl in *.
               destruct s...
            ** rewrite filter_In. rewrite in_flat_map. unfold gfunbods_filterfun_g. destruct x'.
               destruct q. simpl. destruct x0. simpl in x0Eq. destruct s; try discriminate.
               split.
               --- exists (t,n,c). split; [apply in_or_app; left|]... simpl in *. apply in_map...
               --- unfold lookup in *. unfold lookup_ctor_sig in dtorEq.
                   apply find_some in dtorEq. destruct dtorEq. rewrite eq_ScopedName_eq in H1.
                   simpl in H1. rewrite <- H1. simpl. rewrite eq_QName_refl. simpl in x'In2.
                   clear - H x'In2. rewrite andb_true_r. rewrite eq_TypeName_eq. symmetry.
                   change t with (fst (fst (t,n,c))). eapply cfun_bods_type_names...
      -- apply in_or_app. right. subst. rewrite <- map_map. rewrite <- concat_map.
         rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x0. split...
         rewrite <- flat_map_concat_map...
  + clear H. rewrite concat_app in H0. apply in_app_or in H0. rewrite map_app. rewrite map_app.
    rewrite concat_app. rewrite concat_app. apply in_or_app. rewrite map_map at 1.
    destruct H0; [left|]... right. rewrite concat_app in H. apply in_app_or in H. destruct H.
    * rewrite concat_app in H. apply in_app_or in H. apply in_or_app. destruct H.
      -- right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
         unfold l1 in H. clear l1 l2 gbods. erewrite map_ext in H.
         2: { intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
              match goal with [|- map ?f (filter (_ (_ (_ a0))) ?m) = _] =>
                change (map f (filter (_ (_ (_ a0))) m)) with ((fun y => map f ((fun x =>
                  (filter (gfunbods_filterfun_g (unscope (fst x))) m)) y)) a0) end...
         }
         rewrite <- map_map in H. rewrite <- concat_map in H. rewrite <- flat_map_concat_map in H.
         rewrite in_flat_map in H. do 2 destruct H. simpl in *. exists (snd (snd x)). split...
         apply in_map. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
         do 2 destruct H. apply in_or_app. left. rewrite filter_In. rewrite filter_In in H1.
         destruct H1. split.
         ++ rewrite <- flat_map_concat_map. rewrite in_flat_map. unfold cfun_bod in *.
            rewrite in_flat_map in H1. do 2 destruct H1. exists x1. split.
            ** rewrite in_app_iff. rewrite or_comm. rewrite <- in_app_iff...
            ** rewrite in_map_iff in H3. do 2 destruct H3. subst...
         ++ rewrite in_flat_map in H1. do 2 destruct H1. rewrite in_map_iff in H3. do 2 destruct H3.
            subst. simpl. unfold gfunbods_filterfun_g in H2. destruct x1. destruct q. simpl in *.
            destruct x2. simpl. destruct s... rewrite filter_In in H. destruct H.
            unfold gfunsigs_filterfun_g in H3. destruct x0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in H3. subst. simpl in *. apply andb_prop in H2. destruct H2.
            unfold eq_QName in H3. destruct q0. destruct q. simpl in *. apply andb_prop in H3. destruct H3...
      -- left. unfold l2 in *. clear - H. unfold gfun_bod in *. rewrite <- concat_map in H.
         rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H. do 2 destruct H.
         rewrite in_flat_map. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
         do 2 destruct H. rewrite in_map_iff in H1. do 2 destruct H1. exists (snd x1).
         split.
         ++ apply in_map. destruct x1. simpl in *. rewrite <- flat_map_concat_map. rewrite in_flat_map.
            exists x0. split...
         ++ destruct x. simpl in *. inversion H1; subst. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0...
    * clear - H. apply in_or_app. right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
      unfold gbods in H. clear gbods. rewrite <- flat_map_concat_map. rewrite <- flat_map_concat_map in H.
      rewrite in_flat_map in H. do 2 destruct H. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
      do 2 destruct H. rewrite filter_In in H. rewrite in_map_iff in H. do 3 destruct H.
      destruct x0. inversion H; subst. simpl in *. destruct x. simpl in *. rewrite in_map_iff in H1.
      do 2 destruct H1. inversion H1; subst. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0.
      exists (snd x). split...
      apply in_map. apply in_or_app. right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
      exists x1. split... rewrite filter_In. split...
- rewrite <- flat_map_concat_map. unfold l1. unfold l2. unfold gbods. clear.
  rewrite concat_app. rewrite <- (flat_map_concat_map _ (program_fun_bods p)).
  rewrite app_length. rewrite flat_map_app. rewrite app_length. f_equal.
  + rewrite flat_map_concat_map. rewrite map_map. rewrite flat_map_concat_map...
  + rewrite concat_app. rewrite app_length. rewrite concat_app. rewrite app_length.
    rewrite <- plus_assoc. rewrite plus_comm. rewrite flat_map_app. rewrite app_length.
    rewrite <- plus_assoc. f_equal.
    * unfold gfun_bod. rewrite <- concat_map. rewrite <- map_map with (f:=snd).
      rewrite length_concat. rewrite flat_map_concat_map. rewrite length_concat.
      f_equal. repeat (rewrite map_map). rewrite concat_map. rewrite concat_map.
      repeat (rewrite map_map). unfold cfun_bod.
      match goal with [|- _ = _ (_ ?f' _)] => erewrite map_ext with (f:=f') end.
      2:{ intros. rewrite map_map. simpl. erewrite map_ext.
          2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
          reflexivity.
      }
      reflexivity.
    * rewrite map_app. rewrite flat_map_app. rewrite app_length. rewrite plus_comm. f_equal.
      -- unfold cfun_bod. rewrite flat_map_concat_map. rewrite length_concat. rewrite length_concat.
         f_equal. repeat (rewrite map_map). rewrite concat_map. rewrite concat_map.
         repeat (rewrite map_map). unfold cfun_bod. generalize (program_cfun_bods_l p). induction c...
         simpl in *. case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
         ++ unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite H.
            simpl. rewrite IHc. clear IHc. rewrite map_map. simpl. erewrite map_ext with (f:=fun x : ScopedName * expr =>
              length ((fst (proj1_sig ct)) (refunctionalize_expr tn (snd x)))).
            2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            reflexivity.
         ++ unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite H...
      -- simpl. erewrite map_ext with (A:=(ScopedName * list TypeName)%type).
         2:{ intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app. reflexivity. }
         rewrite <- map_map with (g:=map (fun a0 : QName * (ScopedName * expr) => (fst (proj1_sig ct)) (snd (snd a0)))).
         rewrite <- concat_map. change (fun a0 : QName * (ScopedName * expr) => (fst (proj1_sig ct)) (snd (snd a0)))
           with (fun a0 : QName * (ScopedName * expr) => (fst (proj1_sig ct)) ((fun x => (snd (snd x))) a0)).
         rewrite <- map_map with (g:=fst (proj1_sig ct)). do 2 rewrite <- flat_map_concat_map.

         match goal with [|- _ (_ _ (_ _ ?lhs)) = _] => replace lhs with
           (filter (fun x => if in_dec ScopedName_dec (fst x)
               (map fst (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))))
             then true else false) lhs) end.
         2:{ assert (Forall (fun x => In x (program_cfun_bods_l p ++ program_cfun_bods_g p))
               (program_cfun_bods_l p ++ program_cfun_bods_g p)). { rewrite Forall_forall... }
           generalize H. clear H. generalize (program_cfun_bods_l p ++ program_cfun_bods_g p) at - 1. induction l...
           intros. inversion H; subst. simpl. repeat rewrite filter_app. rewrite IHl... f_equal.
           clear IHl H. assert (Forall (fun x => In x (snd a)) (snd a)). { rewrite Forall_forall... }
           generalize H. clear H. generalize (snd a) at - 1. induction c...
           intros. rewrite filter_compose. inversion H; subst. simpl. case_eq (fst a0); intros.
           - rewrite andb_false_r. rewrite filter_compose in IHc...
           - case_eq (eq_TypeName tn (fst (unscope (global q)))); intros;
               [|rewrite andb_false_r; rewrite filter_compose in IHc]...
             match goal with [|- (if (if ?c then _ else _) && _ then _ else _) = _] =>
               assert (exists l, c = left l) end.
             { clear IHc. match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end...
               rename H6 into Contra.
               apply in_app_or in H2. destruct H2;
                 [ pose proof (program_cfun_bods_typecheck_l p) as Typ
                 | pose proof (program_cfun_bods_typecheck_g p) as Typ].
               - unfold cfun_bods_l_typecheck in Typ. rewrite Forall_forall in Typ.
                 apply Typ in H2. clear Typ. destruct H2 as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. unfold lookup_ctors in H16. fold cfun_bod in H16.
                 case_eq (filter (eq_TypeName (fst (fst a)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H2 in H16; try discriminate.
                 inversion H16; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H18).
                 repeat rewrite map_length in H6. rewrite Nat.eqb_eq in H6. symmetry in H6.
                 pose proof (combine_in H4 H6). destruct H7. apply in_combine_switch in H7...
                 rewrite Forall_forall in H17. pose proof H7 as H7'. apply H17 in H7. destruct a0. destruct x.
                 subst. apply in_combine_r in H7'. rewrite filter_In in H7'. destruct H7'. simpl in H0. subst.
                 assert (gfunsigs_filterfun_g tn (global q, l1) = true).
                 { unfold gfunsigs_filterfun_g. rewrite eq_TypeName_eq in H1. subst. rewrite eq_TypeName_refl... }
                 pose proof (conj H7 H0) as Aux. rewrite <- filter_In in Aux.
                 apply (in_map fst) in Aux. simpl in Aux.
                 clear - Aux Contra. exfalso. apply n...
               - unfold cfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
                 apply Typ in H2. clear Typ. destruct H2 as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. unfold lookup_ctors in H16. fold cfun_bod in H16.
                 case_eq (filter (eq_TypeName (fst (fst a)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H2 in H16; try discriminate.
                 inversion H16; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H18).
                 repeat rewrite map_length in H6. rewrite Nat.eqb_eq in H6. symmetry in H6.
                 pose proof (combine_in H4 H6). destruct H7. apply in_combine_switch in H7...
                 rewrite Forall_forall in H17. pose proof H7 as H7'. apply H17 in H7. destruct a0. destruct x.
                 subst. apply in_combine_r in H7'. rewrite filter_In in H7'. destruct H7'. simpl in H0. subst.
                 assert (gfunsigs_filterfun_g tn (global q, l1) = true).
                 { unfold gfunsigs_filterfun_g. rewrite eq_TypeName_eq in H1. subst. rewrite eq_TypeName_refl... }
                 pose proof (conj H7 H0) as Aux. rewrite <- filter_In in Aux.
                 apply (in_map fst) in Aux. simpl in Aux.
                 clear - Aux Contra. exfalso. apply n...
             }
             destruct H6. rewrite H6. simpl. f_equal. rewrite filter_compose in IHc...
         }
         assert (Filter: Forall (fun x => gfunsigs_filterfun_g tn x = true)
           (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p)))).
         { rewrite Forall_forall. intros x H. rewrite filter_In in H. destruct H... }
         generalize Filter. clear Filter.
         assert (Subl : Sublist.sublist (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p)))
           (skeleton_ctors (program_skeleton p))).
         { apply Sublist.sublist_filter. }
         generalize Subl. clear Subl.
         generalize (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))). induction l; intros.
         ++ simpl. match goal with [|- _ (_ _ (_ _ (filter _ ?l))) = _] => induction l end...
         ++ simpl in *. rewrite map_app. do 2 rewrite flat_map_app. rewrite app_length. rewrite <- IHl.
            2:{ eapply Sublist.sublist_trans... constructor. apply Sublist.sublist_refl. }
            2:{ inversion Filter... }
            clear IHl.
            (**)
            evar (nres : nat).
            match goal with [|- _ = ?n + _] => replace n with nres end.
            2:{ symmetry. rewrite flat_map_app. rewrite filter_app. rewrite map_app. rewrite flat_map_app.
              rewrite app_length. rewrite Nat.add_comm. rewrite <- app_length. rewrite <- flat_map_app.
              rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app. unfold nres. reflexivity.
            }
            unfold nres. clear nres.
            (**)
            assert (H: exists l0, l0 ++ (program_cfun_bods_l p ++ program_cfun_bods_g p) =
              (program_cfun_bods_l p ++ program_cfun_bods_g p)).
            { exists []... }
            generalize H. clear H.
            change (list (prod ScopedName expr)) with cfun_bod.
            change (prod QName cfun_bod) with cfun_bod_named.
            rewrite <- flat_map_app.
            generalize (program_cfun_bods_l p ++ program_cfun_bods_g p) at - 2.
            induction l0; intros...
            assert (H0: (exists l1 : list cfun_bod_named,
              l1 ++ l0 = program_cfun_bods_l p ++ program_cfun_bods_g p)).
            { clear - H. destruct H. exists (x++[a0]). rewrite <- app_assoc... }
            rename H into InBods. apply IHl0 in H0. clear IHl0. simpl.
            rewrite filter_app with (P:=gfunbods_filterfun_g (unscope (fst a))).
            rewrite map_app. rewrite flat_map_app. rewrite app_length.
            rewrite filter_app. rewrite filter_app. rewrite filter_app.
            rewrite map_app. rewrite map_app. rewrite flat_map_app. rewrite flat_map_app.
            rewrite app_length. rewrite app_length.
            match goal with [|- _ = ?n1 + ?n2 + (?n3 + ?n4)] => replace (n1 + n2 + (n3 + n4)) with
              ((n1 + n3) + (n2 + n4)) end; try omega.
            rewrite <- H0. clear H0. f_equal.
            rewrite <- app_length. rewrite <- flat_map_app.
            assert (H: exists a, fst a = fst a0 /\ snd a = snd a0 /\
              exists a' a0, a0 ++ snd a = a' /\ In (fst a, a') (program_cfun_bods_l p ++ program_cfun_bods_g p)).
            { exists a0. split... split... destruct InBods. rewrite <- H. exists (snd a0). exists []. split...
              apply in_or_app. right. left... destruct a0...
            }
            generalize H. generalize (snd a0). induction c; intros...
            assert (Aux: exists a, fst a = fst a0 /\ snd a = c /\
              exists a' a0, a0 ++ snd a = a' /\  In (fst a, a') (program_cfun_bods_l p ++ program_cfun_bods_g p)).
            { clear - H0. destruct H0. destruct H. destruct H0. exists (fst x, c). split... split...
              do 3 destruct H1. simpl. exists x0. rewrite <- H1. exists (x1++[a1]). rewrite H0. rewrite <- app_assoc. split...
              rewrite <- H0. rewrite H1...
            }
            simpl. case_eq (fst a1); intros.
            ** destruct a0. destruct q0. simpl. destruct a1. simpl in H1. subst s...
            ** destruct a0. destruct q0. simpl. destruct a1. simpl in H1. subst s.
               case_eq (eq_TypeName tn (fst q)); intros.
               --- cbn. case_eq (ScopedName_dec (fst a) (global q)); intros.
                   +++ cbn. rewrite app_length. rewrite IHc... clear IHc.
                       case_eq (eq_TypeName t (fst (unscope (fst a))) &&
                         eq_QName (unscope (fst a)) q); intros.
                       *** cbn. rewrite app_length. f_equal.
                           assert (Aux2: exists r, in_dec ScopedName_dec (global q) (map fst l) = right r).
                           { pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
                             unfold dts_ctor_names_unique in Uniq. eapply Sublist.sublist_map in Subl.
                             pose proof (Unique.uniqueness_sublist _ _ Subl Uniq) as Done.
                             simpl in Done. inversion Done; subst. rewrite e0 in H6.
                             case_eq (in_dec ScopedName_dec (global q) (map fst l)); intros.
                             - exfalso. apply H6...
                             - exists n0...
                           }
                           destruct Aux2 as [r Aux2]. rewrite Aux2...
                       *** rewrite e0 in H3. simpl in H3. rewrite eq_QName_refl in H3.
                           rewrite andb_false_iff in H3. destruct H3; try discriminate.
                           destruct H0 as [aH [H_1 [H_2 [aH_3 [a'H_3 [H_3_1 H_3_2]]]]]].
                           simpl in *. subst. destruct aH. simpl in *. destruct q0. inversion H_1; subst.
                           clear - H1 H3 H_3_2. destruct q. simpl in *. rewrite eq_TypeName_eq in H1. subst.
                           assert (t = t0). 2:{ subst. rewrite eq_TypeName_refl in H3. discriminate. }
                           clear H3. pose proof (program_cfun_bods_typecheck_g p) as Typ_g.
                           pose proof (program_cfun_bods_typecheck_l p) as Typ_l.
                           unfold cfun_bods_g_typecheck in Typ_g. unfold cfun_bods_l_typecheck in Typ_l.
                           rewrite Forall_forall in *. apply in_app_or in H_3_2. destruct H_3_2.
                           { apply Typ_l in H. do 4 destruct H. clear - H0. inversion H0; subst.
                             simpl in *.
                             set (el1:=(global (t0,n0),e)). set (el2:=nth (length a'H_3) ctorlist (global (t, n0), x0)).
                             set (el:=(el1,el2)).
                             assert (length (a'H_3 ++ (global (t0, n0), e) :: c) = length ctorlist) as LenAux.
                             { symmetry. apply Nat.eqb_eq. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as H.
                               do 2 rewrite map_length in H...
                             }
                             assert (length a'H_3 < length ctorlist) as Len.
                             { rewrite app_length in LenAux. simpl in LenAux. omega. }
                             assert (In el (combine (a'H_3 ++ (global (t0, n0), e) :: c) ctorlist)).
                             { unfold el. unfold el2. unfold el1. replace (global (t0, n0), e) with
                                 (nth (length a'H_3) (a'H_3 ++ (global (t0, n0), e) :: c) (global (t0, n0), e)).
                               2:{ rewrite app_nth2... rewrite Nat.sub_diag... }
                               rewrite <- combine_nth... rewrite app_nth2... rewrite Nat.sub_diag. apply nth_In.
                               rewrite combine_length. simpl. rewrite LenAux. rewrite Nat.min_id...
                             }
                             rewrite Forall_forall in H12. apply H12 in H. unfold el in H.
                             unfold lookup_ctors in H11.
                             case_eq (filter (eq_TypeName t) (skeleton_dts (program_skeleton p))); intros;
                               rewrite H1 in H11; try discriminate.
                             inversion H11; subst. unfold el1 in H.
                             remember el2 as el2'. destruct el2'. destruct s; try discriminate.
                             destruct q. inversion H; subst. unfold el2 in Heqel2'.
                             pose proof (nth_In _ (global (t, n1), x0)  Len) as H2. rewrite <- Heqel2' in H2.
                             rewrite filter_In in H2. destruct H2 as [_ H2]. rewrite eq_TypeName_eq in H2. simpl in *...
                           }
                           { apply Typ_g in H. do 4 destruct H. clear - H0. inversion H0; subst.
                             simpl in *.
                             set (el1:=(global (t0,n0),e)). set (el2:=nth (length a'H_3) ctorlist (global (t, n0), x0)).
                             set (el:=(el1,el2)).
                             assert (length (a'H_3 ++ (global (t0, n0), e) :: c) = length ctorlist) as LenAux.
                             { symmetry. apply Nat.eqb_eq. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as H.
                               do 2 rewrite map_length in H...
                             }
                             assert (length a'H_3 < length ctorlist) as Len.
                             { rewrite app_length in LenAux. simpl in LenAux. omega. }
                             assert (In el (combine (a'H_3 ++ (global (t0, n0), e) :: c) ctorlist)).
                             { unfold el. unfold el2. unfold el1. replace (global (t0, n0), e) with
                                 (nth (length a'H_3) (a'H_3 ++ (global (t0, n0), e) :: c) (global (t0, n0), e)).
                               2:{ rewrite app_nth2... rewrite Nat.sub_diag... }
                               rewrite <- combine_nth... rewrite app_nth2... rewrite Nat.sub_diag. apply nth_In.
                               rewrite combine_length. simpl. rewrite LenAux. rewrite Nat.min_id...
                             }
                             rewrite Forall_forall in H12. apply H12 in H. unfold el in H.
                             unfold lookup_ctors in H11.
                             case_eq (filter (eq_TypeName t) (skeleton_dts (program_skeleton p))); intros;
                               rewrite H1 in H11; try discriminate.
                             inversion H11; subst. unfold el1 in H.
                             remember el2 as el2'. destruct el2'. destruct s; try discriminate.
                             destruct q. inversion H; subst. unfold el2 in Heqel2'.
                             pose proof (nth_In _ (global (t, n1), x0)  Len) as H2. rewrite <- Heqel2' in H2.
                             rewrite filter_In in H2. destruct H2 as [_ H2]. rewrite eq_TypeName_eq in H2. simpl in *...
                           }
                   +++ assert (qEq: eq_QName (unscope (fst a)) q = false).
                       { case_eq (eq_QName (unscope (fst a)) q); intros... rewrite eq_QName_eq in *.
                         subst. exfalso. apply n0. inversion Filter; subst. unfold gfunsigs_filterfun_g in H2.
                         destruct a. destruct s; try discriminate...
                       }
                       rewrite qEq. rewrite andb_false_r.
                       case_eq (in_dec ScopedName_dec (global q) (map fst l)); intros...
                       cbn. rewrite app_length. rewrite flat_map_app. rewrite app_length. cbn.
                       rewrite app_length. apply IHc in Aux. rewrite flat_map_app in Aux.
                       rewrite app_length in Aux. simpl in *. omega.
               --- rewrite IHc... case_eq (eq_QName (unscope (fst a)) q); intros.
                   +++ rewrite eq_QName_eq in H2. subst. inversion Filter; subst.
                       unfold gfunsigs_filterfun_g in H4. destruct a. destruct s; try discriminate.
                       simpl in H1. rewrite H1 in H4. discriminate.
                   +++ rewrite andb_false_r...
Qed.

Lemma new_match_names_unique_cbods_l_gbods_l : forall p tn (ct : collect_tuple)
  (CfunLMUnique1 : Unique.unique
    (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_g p)))))
  (CfunLMUnique2 : Forall
    (fun x => ~ In x (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_g p)))))
    (concat (map (fst (proj1_sig ct))
      (map snd (program_fun_bods p) ++
       map snd (concat (map snd (program_cfun_bods_l p))) ++
       map snd (concat (map snd (program_gfun_bods_l p))))))),
  (snd (proj1_sig ct)) (new_fun_bods p tn) (new_cfun_bods_l p tn) (new_gfun_bods_l p tn).
Proof with eauto.
intros.
pose proof (program_match_names_unique_cbods_l_gbods_l p ct) as Aux.
rewrite (proj1 (proj2 (proj2_sig ct))) in Aux.
pose proof (Unique.uniqueness_app _ _ Aux CfunLMUnique1 CfunLMUnique2).
clear Aux.
clear CfunLMUnique1 CfunLMUnique2.

(*[> Structurally different part (compared with defunc) no. 1 <]*)
rewrite <- flat_map_concat_map in H. rewrite flat_map_app in H. rewrite flat_map_app in H.
rewrite <- app_assoc in H. rewrite <- app_assoc in H.
(*[> Refunc-specific <]*)
rewrite app_assoc in H. apply Unique.unique_app_switch in H.
rewrite <- app_assoc in H.
rewrite app_assoc with (l:=_ _ (_ _ (_ (_ _ (program_cfun_bods_l p))))) in H.
apply Unique.unique_app_switch in H.
(*[> End Refunc-specific <]*)
repeat (rewrite <- flat_map_app in H). rewrite flat_map_concat_map in H.
unfold cfun_bod in *. rewrite <- (flat_map_concat_map snd (program_cfun_bods_l p)) in H.
rewrite <- map_app in H. rewrite <- flat_map_app in H. rewrite flat_map_concat_map in H.

rewrite (proj1 (proj2 (proj2_sig ct))) in *.
unfold new_fun_bods in *. unfold new_cfun_bods_l in *. unfold new_gfun_bods_l in *.
repeat (repeat (rewrite map_app); repeat (rewrite map_map); simpl).
match goal with [|- _ (_ ((map ?f ?l) ++ _ ++ _))] =>
  replace (map f l) with (map (fun x => (fst (proj1_sig ct)) (snd x)) l) end.
2:{ apply map_ext. intros. symmetry. apply (proj1 (proj2 (proj2 (proj2_sig ct)))). }

(*[> Structurally different part no. 2, entirely refunc-specific <]*)
repeat rewrite map_app. apply uniqueness_concat_app_switch.

rewrite concat_map. rewrite map_app. rewrite map_map. erewrite map_ext_in with (l:=filter _ _).
2:{ intros. rewrite map_app. rewrite map_map. simpl. unfold globalize_aux. unfold localize_aux.
  rewrite map_map. simpl. rewrite map_map. simpl. rewrite map_map.
  erewrite map_ext.
  2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
  erewrite map_ext with (l:=filter _ (flat_map _ (program_cfun_bods_l p))).
  2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
  reflexivity.
}
match goal with [|- _ (_ (_ ++ (_ (?l1' ++ ?l2')) ++ ?gbods'))] =>
  set (l1:=l1'); set (l2:=l2'); set (gbods:=gbods') end.
rewrite concat_app with (l2:=l2).

match goal with
  [_ : Unique.unique (_ (_ _ (?fs' ++ ?cfs' ++ map snd (concat (map snd (?gfs_g' ++ ?gfs_l')))))) |- _] =>
    set (fs:=fs') in *; set (cfs:=cfs') in *; set (gfs_g:=gfs_g'); set (gfs_l:=gfs_l') in * end.
assert (Unique.unique (concat (map (fst (proj1_sig ct)) (fs ++ cfs ++ (map snd
    (filter (fun x => match fst x with local _ => eq_TypeName tn (fst (unscope (fst x))) | _ => false end)
      (concat (map snd (gfs_g ++ gfs_l))) ++
    (concat (map snd (filter (fun x => negb (eq_TypeName tn (fst (fst x)))) (gfs_g)))))))))) as H0.
{ repeat rewrite map_app. repeat rewrite concat_app. rewrite app_assoc. rewrite app_assoc.
  apply Unique.uniqueness_app.
  - eapply Unique.uniqueness_sublist; [|apply H]. repeat rewrite map_app. repeat rewrite concat_app.
    rewrite <- app_assoc. repeat (apply Sublist.sublist_app; try apply Sublist.sublist_refl).
    fold gfs_g. unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *.
    generalize (concat (map snd gfs_g) ++ concat (map snd gfs_l)). clear.
    induction l; [constructor|]. simpl. case_eq (fst a); intros.
    + case_eq (eq_TypeName tn (fst (unscope (local q)))); intros.
      * simpl. apply Sublist.sublist_app... apply Sublist.sublist_refl.
      * rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app... constructor.
    + rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app... constructor.
  - eapply Unique.uniqueness_sublist... fold gfs_g.
    repeat (rewrite map_app; rewrite map_app; rewrite concat_app).
    rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app; [constructor|].
    rewrite concat_app. rewrite <- (app_nil_l (concat _)). apply Sublist.sublist_app; [constructor|].
    generalize gfs_g. clear. induction gfs_g; [constructor|].
    simpl. unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
    case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
    + simpl. repeat (rewrite map_app; rewrite map_app; rewrite concat_app). apply Sublist.sublist_app...
      apply Sublist.sublist_refl.
    + repeat rewrite map_app. rewrite concat_app. rewrite <- (app_nil_l (concat _)).
      apply Sublist.sublist_app; [constructor|]. rewrite <- map_app. apply IHgfs_g.
  - clear - H. rewrite Forall_forall. intros. apply in_app_or in H0. destruct H0.
    + repeat (rewrite map_app in H; rewrite concat_app in H). rewrite app_assoc in H.
      apply Unique.uniqueness_app_not_in in H. rewrite Forall_forall in H.
      apply H in H0. unfold not. intros. apply H0. fold gfs_g. clear - H1.
      generalize dependent gfs_g. induction gfs_g; intros; [exfalso|]...
      simpl in *. repeat rewrite map_app. repeat rewrite concat_app. rewrite <- app_assoc.
      unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
      case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
      * rewrite H in *. simpl in *. repeat rewrite map_app in H1. rewrite concat_app in H1.
        apply in_or_app. apply in_app_or in H1. destruct H1; [left|]...
        right. rewrite <- concat_app. repeat rewrite <- map_app...
      * rewrite H in *. simpl in *. apply in_or_app. right.
        rewrite <- concat_app. repeat rewrite <- map_app...
    + rewrite filter_app in H0. repeat rewrite map_app in H0. rewrite concat_app in H0.
      apply in_app_or in H0. repeat rewrite map_app in H. repeat rewrite concat_app in H. destruct H0.
      * rewrite app_assoc in H. rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H.
        fold gfs_g in H. generalize H H0.
        match goal with [|- _ (_ ++ _ ++ ?l') -> _] => generalize l' end.
        rewrite <- concat_app. rewrite <- map_app.
        generalize gfs_l. assert (Forall (fun x => In x gfs_g) gfs_g) as Aux.
        { rewrite Forall_forall... }
        generalize Aux. generalize gfs_g at - 1. clear. induction gfs_g0; intros...
        unfold not. intros. simpl in *. rewrite filter_app in H0.
        unfold cfun_bods in *. unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *.
        case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
        -- rewrite H2 in *. simpl in *. repeat rewrite map_app in H1. rewrite concat_app in H1.
           apply in_app_or in H1. destruct H1.
           ++ inversion Aux; subst. repeat rewrite map_app in H0. rewrite concat_app in H0.
              apply in_app_or in H0. destruct H0.
              ** rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0. do 2 destruct H0.
                 rewrite in_map_iff in H0. do 2 destruct H0. rewrite filter_In in H4. destruct H4.
                 case_eq (fst x1); intros; rewrite H8 in H7; try discriminate. simpl in *.
                 assert (Aux2: fst q = fst (fst a)).
                 { eapply cfun_bods_l_type_names_l... }
                 rewrite <- Aux2 in H2. rewrite eq_TypeName_eq in *. subst. rewrite eq_TypeName_refl in H2.
                 discriminate.
              ** clear IHgfs_g0 Aux. repeat rewrite map_app in H. rewrite concat_app in H.
                 apply in_split in H1. do 2 destruct H1. rewrite H1 in H.
                 rewrite <- app_assoc in H. rewrite <- app_assoc in H. rewrite <- app_nil_l in H.
                 apply Unique.unique_app_switch in H. inversion H; subst. apply H7.
                 apply in_or_app. left. apply in_or_app. right. clear - H0.
                 rewrite <- flat_map_concat_map in *. apply in_or_app. left. rewrite concat_app. rewrite map_app.
                 rewrite flat_map_app. apply in_or_app. left. rewrite in_flat_map in *.
                 destruct H0. destruct H. exists x0. split... clear - H. rewrite in_map_iff in *.
                 do 2 destruct H. exists x. split... rewrite filter_In in H0. destruct H0...
           ++ inversion Aux; subst. pose proof H6 as H6'. eapply IHgfs_g0 in H6...
              ** instantiate (1:=l). instantiate (1:=gfs_l). clear - H.
                 repeat rewrite map_app in H. rewrite concat_app in H. generalize H. clear H.
                 match goal with [|- _ ((?l'++_) ++ _) -> _] => generalize l' end. intros.
                 rewrite <- map_app in H. induction l0... apply IHl0. inversion H...
              ** match goal with [_ : In x (_ (_ _ (_ _ (?l1 ++ _)))) |- _] => assert (l1 = []) end.
                 2:{ rewrite H3 in H0... }
                 clear - H2 H5. match goal with [|- ?lhs' = _] => set (lhs:=lhs'); case_eq lhs; intros end...
                 pose proof (in_eq p0 l). rewrite <- H in H0. unfold lhs in H0. rewrite filter_In in H0.
                 destruct H0. assert (H': exists q, fst p0 = local q). { destruct (fst p0)... discriminate. }
                 destruct H' as [q H']. assert (fst q = fst (fst a)). { eapply cfun_bods_l_type_names_l... }
                 rewrite H' in H1. simpl in *. rewrite H3 in H1. rewrite eq_TypeName_eq in H1. subst.
                 rewrite eq_TypeName_refl in H2. discriminate.
        -- rewrite H2 in *. simpl in *. inversion Aux; subst. pose proof H6 as H6'. eapply IHgfs_g0 in H6...
           ++ instantiate (1:=l). instantiate (1:=gfs_l). clear - H.
              repeat rewrite map_app in H. rewrite concat_app in H. generalize H. clear H.
              match goal with [|- _ ((?l'++_) ++ _) -> _] => generalize l' end. intros.
              rewrite <- map_app in H. induction l0... apply IHl0. inversion H...
           ++ rewrite <- flat_map_concat_map in H0. rewrite map_app in H0. rewrite flat_map_app in H0.
              apply in_app_or in H0. destruct H0; [| rewrite <- flat_map_concat_map]...
              exfalso. rename H into Uniq. clear - Uniq H0 H1 H2 H5 Aux. rewrite <- flat_map_concat_map in H1.
              rewrite in_flat_map in *. destruct H0. destruct H. do 2 destruct H1. rewrite in_map_iff in *.
              do 2 destruct H. do 2 destruct H1. rewrite <- flat_map_concat_map in H6.
              rewrite in_flat_map in H6. rewrite filter_In in H4. do 2 destruct H6. destruct H4.
              rewrite filter_In in H6. destruct H6.
              apply in_split in H4. do 2 destruct H4. rewrite H4 in Uniq. repeat (rewrite map_app in Uniq).
              simpl in Uniq. rewrite H in Uniq. apply in_split in H0. do 2 destruct H0. rewrite H0 in Uniq.
              repeat (rewrite concat_app in Uniq). simpl in Uniq.
              apply in_split in H6. do 2 destruct H6. rewrite H6 in Uniq. apply in_split in H7.
              do 2 destruct H7. repeat (rewrite map_app in Uniq). simpl in Uniq. rewrite H7 in Uniq.
              repeat (rewrite concat_app in Uniq). simpl in Uniq.
              repeat (rewrite map_app in Uniq). simpl in Uniq. rewrite H1 in Uniq.
              apply in_split in H3. do 2 destruct H3. rewrite H3 in Uniq. clear - Uniq.
              rewrite <- app_assoc in Uniq. generalize Uniq. clear Uniq. fold QName in *.
              match goal with [|- _ ((?l' ++ _ ++ _) ++ _ ++ _) -> _] => generalize l' end.
              clear. intros.
              match goal with [_ : Unique.unique ((l0++(x7++x::x8)++?r1)++?r2) |- _] =>
                assert (Unique.unique (x::x8++r1++r2)) end.
              { induction l0; induction x7; inversion Uniq; subst... do 2 rewrite app_nil_l in Uniq.
                clear - Uniq. rewrite <- app_comm_cons in Uniq. rewrite <- app_assoc in Uniq.
                rewrite app_assoc. rewrite app_comm_cons. rewrite <- app_assoc...
              }
              clear - H. inversion H; subst. apply H2. do 2 (apply in_or_app; right).
              repeat rewrite concat_app. do 2 (apply in_or_app; left). apply in_or_app. right.
              apply in_or_app. left. apply in_or_app. right. simpl. rewrite <- app_assoc. apply in_or_app.
              right. left...
      * rewrite app_assoc in H. rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H.
        simpl in H. repeat rewrite map_app in H. rewrite concat_app in H.
        rewrite <- app_assoc in H. apply Unique.uniqueness_app_not_in in H. rewrite Forall_forall in H.
        unfold not. intros. fold gfs_g in H. rewrite <- flat_map_concat_map in H1.
        rewrite in_flat_map in H1. do 2 destruct H1. rewrite in_map_iff in H1.
        do 2 destruct H1. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0.
        do 2 destruct H0. rewrite <- flat_map_concat_map in H3. rewrite in_flat_map in H3.
        do 2 destruct H3. rewrite in_map_iff in H0. do 2 destruct H0.
        rewrite filter_In in H6. destruct H6. rewrite filter_In in H3. destruct H3.
        case_eq (fst x4); intros; rewrite H9 in H7; try discriminate.
        eapply H.
        -- rewrite <- flat_map_concat_map. rewrite in_flat_map. eexists. split.
           ++ rewrite in_map_iff. eexists. split... rewrite <- flat_map_concat_map. rewrite in_flat_map.
              eexists. split...
           ++ eauto.
        -- apply in_or_app. left. rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x2. split...
           rewrite in_map_iff. eexists. split...
}
clear H. rename H0 into H.

unfold fs in *. unfold cfs in *. unfold gfs_g in *. unfold gfs_l in *. clear fs cfs gfs_g gfs_l.

eapply unique_unordered; eauto; [apply QName_dec|].
unfold unordered_eq. split.
- intros. split; intros.
  + rewrite map_app in H0. rewrite map_map in H0. rewrite concat_app in H0.
    rewrite concat_app. apply in_app_or in H0. apply in_or_app. destruct H0; [left|]...
    rewrite map_app in H0. rewrite concat_app in H0. apply in_app_or in H0. destruct H0.
    * right. rewrite concat_app. apply in_or_app. left. rewrite concat_app.
      apply in_or_app. right. unfold l2. rewrite map_map. erewrite map_ext.
      2: { intros. rewrite map_map. simpl. match goal with [|- _ ?f _ = _ _] =>
             change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end... }
      rewrite <- map_map. erewrite map_ext.
      2: { intros. erewrite map_ext.
        2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
          change ((fst (proj1_sig ct)) (snd a1)) with ((fun x => (fst (proj1_sig ct)) (snd x)) a1)...
        }
        eauto.
      }
      rewrite <- concat_map. rewrite <- map_map...
    * right. rewrite concat_app. rewrite concat_app.
      assert (In a (concat (concat l1) ++ concat gbods)).
      2:{ apply in_app_or in H1. apply in_or_app. destruct H1; [|right]...
          left. apply in_or_app. left...
      }
      clear - H0. remember gbods. unfold gbods in Heql. rewrite concat_map in Heql.
      rewrite map_map in Heql. rewrite <- filter_map in Heql. rewrite map_map in Heql.
      simpl in Heql. erewrite map_ext in Heql.
      2: { intros. rewrite map_map. simpl. match goal with [|- _ ?f _ = _ _] =>
             change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end... }
      erewrite map_ext in Heql.
      2: { intros. erewrite map_ext.
        2: { intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
             change ((fst (proj1_sig ct)) (snd a1)) with ((fun x => (fst (proj1_sig ct)) (snd x)) a1)...
        }
        match goal with [|- map ?f _ = _] => change (map f (snd a0)) with ((fun x => map f (snd x)) a0) end...
      }
      clear gbods. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in H0.
      destruct H0 as [x [H0_1 H0_2]]. rewrite in_map_iff in H0_1. destruct H0_1 as [x0 [H0_1 H0_1In]].
      do 2 rewrite <- flat_map_concat_map in H0_1In. apply in_app_or in H0_1In.
      destruct H0_1In.
      -- rewrite filter_In in H. rewrite in_flat_map in H. destruct H as [[x' [x'In1 x'In2]] x0Eq].
         apply in_app_or in x'In1. destruct x'In1.
         ++ case_eq (negb (eq_TypeName tn (fst (fst x')))); intros.
            ** apply in_or_app. right. subst. rewrite <- map_map. rewrite <- concat_map.
               rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x0. split...
               rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x'. split...
               rewrite filter_In. split...
            ** apply in_or_app. left. clear l Heql. unfold l1. clear l1.
               eapply In_concat... rewrite <- flat_map_concat_map. rewrite in_flat_map.
               set (lookup := lookup_ctor_sig (program_skeleton p) (fst x0)).
               assert (exists dtor, lookup = Some dtor).
               { pose proof (program_cfun_bods_typecheck_l p) as Typ. unfold cfun_bods_l_typecheck in Typ.
                 rewrite Forall_forall in Typ. apply Typ in H. clear Typ. destruct H as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as Len.
                 rewrite Nat.eqb_eq in Len. repeat rewrite map_length in Len. symmetry in Len.
                 pose proof (combine_in x'In2 Len). destruct H. unfold lookup.
                 unfold lookup_ctors in H11. unfold cfun_bod in *.
                 case_eq (filter (eq_TypeName (fst (fst x'))) (skeleton_dts (program_skeleton p)));
                   intros; rewrite H1 in H11; try discriminate. inversion H11; subst.
                 match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end; [exists c|]...
                 unfold lookup_ctor_sig in H2. pose proof H as H'. apply in_combine_l in H. rewrite filter_In in H.
                 destruct H. eapply find_none in H2... apply in_combine_switch in H'... rewrite Forall_forall in H12.
                 apply H12 in H'. destruct x0. destruct x. subst. simpl in *.
                 rewrite eq_ScopedName_refl in H2. discriminate.
               }
               unfold dtor in *. destruct H1 as [dtor dtorEq]. exists dtor. split.
               --- unfold lookup in *. unfold lookup_ctor_sig in dtorEq. apply find_some in dtorEq.
                   rewrite filter_In. destruct dtorEq. split... unfold gfunsigs_filterfun_g.
                   destruct dtor. rewrite eq_ScopedName_eq in H2. simpl in H2.
                   subst. destruct x0. simpl in *. destruct s...
               --- apply in_or_app. right. rewrite in_map_iff. exists (fst x', x0). simpl. rewrite H0_1. split...
                   rewrite filter_In. split.
                   +++ rewrite in_flat_map. exists x'. split... rewrite in_map_iff. exists x0. split...
                   +++ unfold gfunbods_filterfun_g. destruct x'. simpl. destruct q. destruct x0. simpl in *.
                       destruct s... rewrite negb_false_iff in H0. rewrite eq_TypeName_eq in H0. subst.
                       rewrite eq_TypeName_eq in x0Eq. simpl in x0Eq. subst.
                       unfold lookup in *. unfold lookup_ctor_sig in dtorEq. apply find_some in dtorEq.
                       destruct dtorEq. unfold eq_ScopedName in H1. destruct dtor. simpl in *.
                       destruct s; try discriminate. rewrite eq_QName_eq in H1. subst. simpl.
                       rewrite eq_TypeName_refl. rewrite eq_QName_refl...
         ++ apply in_or_app. left. clear l Heql. unfold l1. simpl. erewrite map_ext.
            2: { intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
              match goal with [|- map ?f (filter (_ (_ (_ a0))) ?m) = _] =>
                change (map f (filter (_ (_ (_ a0))) m)) with ((fun y => map f ((fun x =>
                  (filter (gfunbods_filterfun_l (unscope (fst x))) m)) y)) a0) end...
            }
            rewrite <- map_map. rewrite <- concat_map. rewrite <- flat_map_concat_map.
            rewrite in_flat_map. exists (fst x', x0). subst. split...
            rewrite <- flat_map_concat_map. rewrite in_flat_map.
            set (lookup := lookup_ctor_sig (program_skeleton p) (fst x0)).
            assert (exists dtor, lookup = Some dtor).
            { pose proof (program_cfun_bods_typecheck_g p) as Typ. unfold cfun_bods_g_typecheck in Typ.
              rewrite Forall_forall in Typ. apply Typ in H. clear Typ. destruct H as [qn [args [t [_ Typ]]]].
              inversion Typ; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H12) as Len.
              rewrite Nat.eqb_eq in Len. repeat rewrite map_length in Len. symmetry in Len.
              pose proof (combine_in x'In2 Len). destruct H. unfold lookup.
              unfold lookup_ctors in H10. unfold cfun_bod in *.
              case_eq (filter (eq_TypeName (fst (fst x'))) (skeleton_dts (program_skeleton p)));
                intros; rewrite H0 in H10; try discriminate. inversion H10; subst.
              match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end; [exists c|]...
              unfold lookup_ctor_sig in H1. pose proof H as H'. apply in_combine_l in H. rewrite filter_In in H.
              destruct H. eapply find_none in H1... apply in_combine_switch in H'... rewrite Forall_forall in H11.
              apply H11 in H'. destruct x0. destruct x. subst. simpl in *.
              rewrite eq_ScopedName_refl in H1. discriminate.
            }
            unfold dtor in *. destruct H0 as [dtor dtorEq]. exists dtor. split.
            ** rewrite filter_In. unfold lookup in *. unfold lookup_ctor_sig in dtorEq.
               apply find_some in dtorEq. destruct dtorEq. split...
               unfold gfunsigs_filterfun_g. destruct dtor.
               rewrite eq_ScopedName_eq in H1. simpl in H1. subst. destruct x0. simpl in *.
               destruct s...
            ** rewrite filter_In. rewrite in_flat_map. unfold gfunbods_filterfun_g. destruct x'.
               destruct q. simpl. destruct x0. simpl in x0Eq. destruct s; try discriminate.
               split.
               --- exists (t,n,c). split; [apply in_or_app; left|]... simpl in *. apply in_map...
               --- unfold lookup in *. unfold lookup_ctor_sig in dtorEq.
                   apply find_some in dtorEq. destruct dtorEq. rewrite eq_ScopedName_eq in H1.
                   simpl in H1. rewrite <- H1. simpl. rewrite eq_QName_refl. simpl in x'In2.
                   clear - H x'In2. rewrite andb_true_r. rewrite eq_TypeName_eq. symmetry.
                   change t with (fst (fst (t,n,c))). eapply cfun_bods_type_names_l...
      -- apply in_or_app. right. subst. rewrite <- map_map. rewrite <- concat_map.
         rewrite <- flat_map_concat_map. rewrite in_flat_map. exists x0. split...
         rewrite <- flat_map_concat_map...
  + clear H. rewrite concat_app in H0. apply in_app_or in H0. rewrite map_app. rewrite map_app.
    rewrite concat_app. rewrite concat_app. apply in_or_app. rewrite map_map at 1.
    destruct H0; [left|]... right. rewrite concat_app in H. apply in_app_or in H. destruct H.
    * rewrite concat_app in H. apply in_app_or in H. apply in_or_app. destruct H.
      -- right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
         unfold l1 in H. clear l1 l2 gbods. erewrite map_ext in H.
         2: { intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
              match goal with [|- map ?f (filter (_ (_ (_ a0))) ?m) = _] =>
                change (map f (filter (_ (_ (_ a0))) m)) with ((fun y => map f ((fun x =>
                  (filter (gfunbods_filterfun_l (unscope (fst x))) m)) y)) a0) end...
         }
         rewrite <- map_map in H. rewrite <- concat_map in H. rewrite <- flat_map_concat_map in H.
         rewrite in_flat_map in H. do 2 destruct H. simpl in *. exists (snd (snd x)). split...
         apply in_map. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
         do 2 destruct H. apply in_or_app. left. rewrite filter_In. rewrite filter_In in H1.
         destruct H1. split.
         ++ rewrite <- flat_map_concat_map. rewrite in_flat_map. unfold cfun_bod in *.
            rewrite in_flat_map in H1. do 2 destruct H1. exists x1. split.
            ** rewrite in_app_iff. rewrite or_comm. rewrite <- in_app_iff...
            ** rewrite in_map_iff in H3. do 2 destruct H3. subst...
         ++ rewrite in_flat_map in H1. do 2 destruct H1. rewrite in_map_iff in H3. do 2 destruct H3.
            subst. simpl. unfold gfunbods_filterfun_g in H2. destruct x1. destruct q. simpl in *.
            destruct x2. simpl. destruct s... rewrite filter_In in H. destruct H.
            unfold gfunsigs_filterfun_l in H3. destruct x0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in H3. subst. simpl in *. apply andb_prop in H2. destruct H2.
            unfold eq_QName in H3. destruct q0. destruct q. simpl in *. apply andb_prop in H3. destruct H3...
      -- left. unfold l2 in *. clear - H. unfold gfun_bod in *. rewrite <- concat_map in H.
         rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H. do 2 destruct H.
         rewrite in_flat_map. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
         do 2 destruct H. rewrite in_map_iff in H1. do 2 destruct H1. exists (snd x1).
         split.
         ++ apply in_map. destruct x1. simpl in *. rewrite <- flat_map_concat_map. rewrite in_flat_map.
            exists x0. split...
         ++ destruct x. simpl in *. inversion H1; subst. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0...
    * clear - H. apply in_or_app. right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
      unfold gbods in H. clear gbods. rewrite <- flat_map_concat_map. rewrite <- flat_map_concat_map in H.
      rewrite in_flat_map in H. do 2 destruct H. rewrite <- flat_map_concat_map in H. rewrite in_flat_map in H.
      do 2 destruct H. rewrite filter_In in H. rewrite in_map_iff in H. do 3 destruct H.
      destruct x0. inversion H; subst. simpl in *. destruct x. simpl in *. rewrite in_map_iff in H1.
      do 2 destruct H1. inversion H1; subst. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0.
      exists (snd x). split...
      apply in_map. apply in_or_app. right. rewrite <- flat_map_concat_map. rewrite in_flat_map.
      exists x1. split... rewrite filter_In. split...
- rewrite <- flat_map_concat_map. unfold l1. unfold l2. unfold gbods. clear.
  rewrite concat_app. rewrite <- (flat_map_concat_map _ (program_fun_bods p)).
  rewrite app_length. rewrite flat_map_app. rewrite app_length. f_equal.
  + rewrite flat_map_concat_map. rewrite map_map. rewrite flat_map_concat_map...
  + rewrite concat_app. rewrite app_length. rewrite concat_app. rewrite app_length.
    rewrite <- plus_assoc. rewrite plus_comm. rewrite flat_map_app. rewrite app_length.
    rewrite <- plus_assoc. f_equal.
    * unfold gfun_bod. rewrite <- concat_map. rewrite <- map_map with (f:=snd).
      rewrite length_concat. rewrite flat_map_concat_map. rewrite length_concat.
      f_equal. repeat (rewrite map_map). rewrite concat_map. rewrite concat_map.
      repeat (rewrite map_map). unfold cfun_bod.
      match goal with [|- _ = _ (_ ?f' _)] => erewrite map_ext with (f:=f') end.
      2:{ intros. rewrite map_map. simpl. erewrite map_ext.
          2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
          reflexivity.
      }
      reflexivity.
    * rewrite map_app. rewrite flat_map_app. rewrite app_length. rewrite plus_comm. f_equal.
      -- unfold cfun_bod. rewrite flat_map_concat_map. rewrite length_concat. rewrite length_concat.
         f_equal. repeat (rewrite map_map). rewrite concat_map. rewrite concat_map.
         repeat (rewrite map_map). unfold cfun_bod. generalize (program_cfun_bods_l p). induction c...
         simpl in *. case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
         ++ unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite H.
            simpl. rewrite IHc. clear IHc. rewrite map_map. simpl. erewrite map_ext with (f:=fun x : ScopedName * expr =>
              length ((fst (proj1_sig ct)) (refunctionalize_expr tn (snd x)))).
            2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            reflexivity.
         ++ unfold cfun_bod_named in *. unfold cfun_bod in *. unfold QName in *. rewrite H...
      -- simpl. erewrite map_ext with (A:=(ScopedName * list TypeName)%type).
         2:{ intros. rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app. reflexivity. }
         rewrite <- map_map with (g:=map (fun a0 : QName * (ScopedName * expr) => (fst (proj1_sig ct)) (snd (snd a0)))).
         rewrite <- concat_map. change (fun a0 : QName * (ScopedName * expr) => collect_match_names (snd (snd a0)))
           with (fun a0 : QName * (ScopedName * expr) => collect_match_names ((fun x => (snd (snd x))) a0)).
         rewrite <- map_map with (g:=fst (proj1_sig ct)). do 2 rewrite <- flat_map_concat_map.

         match goal with [|- _ (_ _ (_ _ ?lhs)) = _] => replace lhs with
           (filter (fun x => if in_dec ScopedName_dec (fst x)
               (map fst (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))))
             then true else false) lhs) end.
         2:{ assert (Forall (fun x => In x (program_cfun_bods_l p ++ program_cfun_bods_g p))
               (program_cfun_bods_l p ++ program_cfun_bods_g p)). { rewrite Forall_forall... }
           generalize H. clear H. generalize (program_cfun_bods_l p ++ program_cfun_bods_g p) at - 1. induction l...
           intros. inversion H; subst. simpl. repeat rewrite filter_app. rewrite IHl... f_equal.
           clear IHl H. assert (Forall (fun x => In x (snd a)) (snd a)). { rewrite Forall_forall... }
           generalize H. clear H. generalize (snd a) at - 1. induction c...
           intros. rewrite filter_compose. inversion H; subst. simpl. case_eq (fst a0); intros.
           2:{ rewrite andb_false_r. rewrite filter_compose in IHc... }
           - case_eq (eq_TypeName tn (fst (unscope (local q)))); intros;
               [|rewrite andb_false_r; rewrite filter_compose in IHc]...
             match goal with [|- (if (if ?c then _ else _) && _ then _ else _) = _] =>
               assert (exists l, c = left l) end.
             { clear IHc. match goal with [|- exists _, ?lhs = _] => case_eq lhs; intros end...
               rename H6 into Contra.
               apply in_app_or in H2. destruct H2;
                 [ pose proof (program_cfun_bods_typecheck_l p) as Typ
                 | pose proof (program_cfun_bods_typecheck_g p) as Typ].
               - unfold cfun_bods_l_typecheck in Typ. rewrite Forall_forall in Typ.
                 apply Typ in H2. clear Typ. destruct H2 as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. unfold lookup_ctors in H16. fold cfun_bod in H16.
                 case_eq (filter (eq_TypeName (fst (fst a)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H2 in H16; try discriminate.
                 inversion H16; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H18).
                 repeat rewrite map_length in H6. rewrite Nat.eqb_eq in H6. symmetry in H6.
                 pose proof (combine_in H4 H6). destruct H7. apply in_combine_switch in H7...
                 rewrite Forall_forall in H17. pose proof H7 as H7'. apply H17 in H7. destruct a0. destruct x.
                 subst. apply in_combine_r in H7'. rewrite filter_In in H7'. destruct H7'. simpl in H0. subst.
                 assert (gfunsigs_filterfun_l tn (local q, l1) = true).
                 { unfold gfunsigs_filterfun_l. rewrite eq_TypeName_eq in H1. subst. rewrite eq_TypeName_refl... }
                 pose proof (conj H7 H0) as Aux. rewrite <- filter_In in Aux.
                 apply (in_map fst) in Aux. simpl in Aux.
                 clear - Aux Contra. exfalso. apply n...
               - unfold cfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
                 apply Typ in H2. clear Typ. destruct H2 as [qn [args [t [_ Typ]]]].
                 inversion Typ; subst. unfold lookup_ctors in H16. fold cfun_bod in H16.
                 case_eq (filter (eq_TypeName (fst (fst a)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H2 in H16; try discriminate.
                 inversion H16; subst. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H18).
                 repeat rewrite map_length in H6. rewrite Nat.eqb_eq in H6. symmetry in H6.
                 pose proof (combine_in H4 H6). destruct H7. apply in_combine_switch in H7...
                 rewrite Forall_forall in H17. pose proof H7 as H7'. apply H17 in H7. destruct a0. destruct x.
                 subst. apply in_combine_r in H7'. rewrite filter_In in H7'. destruct H7'. simpl in H0. subst.
                 assert (gfunsigs_filterfun_l tn (local q, l1) = true).
                 { unfold gfunsigs_filterfun_l. rewrite eq_TypeName_eq in H1. subst. rewrite eq_TypeName_refl... }
                 pose proof (conj H7 H0) as Aux. rewrite <- filter_In in Aux.
                 apply (in_map fst) in Aux. simpl in Aux.
                 clear - Aux Contra. exfalso. apply n...
             }
             destruct H6. rewrite H6. simpl. f_equal. rewrite filter_compose in IHc...
         }
         assert (Filter: Forall (fun x => gfunsigs_filterfun_l tn x = true)
           (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p)))).
         { rewrite Forall_forall. intros x H. rewrite filter_In in H. destruct H... }
         generalize Filter. clear Filter.
         assert (Subl : Sublist.sublist (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p)))
           (skeleton_ctors (program_skeleton p))).
         { apply Sublist.sublist_filter. }
         generalize Subl. clear Subl.
         generalize (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))). induction l; intros.
         ++ simpl. match goal with [|- _ (_ _ (_ _ (filter _ ?l))) = _] => induction l end...
         ++ simpl in *. rewrite map_app. do 2 rewrite flat_map_app. rewrite app_length. rewrite <- IHl.
            2:{ eapply Sublist.sublist_trans... constructor. apply Sublist.sublist_refl. }
            2:{ inversion Filter... }
            clear IHl.
            (**)
            evar (nres : nat).
            match goal with [|- _ = ?n + _] => replace n with nres end.
            2:{ symmetry. rewrite flat_map_app. rewrite filter_app. rewrite map_app. rewrite flat_map_app.
              rewrite app_length. rewrite Nat.add_comm. rewrite <- app_length. rewrite <- flat_map_app.
              rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app. unfold nres. reflexivity.
            }
            unfold nres. clear nres.
            (**)
            assert (H: exists l0, l0 ++ (program_cfun_bods_l p ++ program_cfun_bods_g p) =
              (program_cfun_bods_l p ++ program_cfun_bods_g p)).
            { exists []... }
            generalize H. clear H.
            change (list (prod ScopedName expr)) with cfun_bod.
            change (prod QName cfun_bod) with cfun_bod_named.
            rewrite <- flat_map_app.
            generalize (program_cfun_bods_l p ++ program_cfun_bods_g p) at - 2.
            induction l0; intros...
            assert (H0: (exists l1 : list cfun_bod_named,
              l1 ++ l0 = program_cfun_bods_l p ++ program_cfun_bods_g p)).
            { clear - H. destruct H. exists (x++[a0]). rewrite <- app_assoc... }
            rename H into InBods. apply IHl0 in H0. clear IHl0. simpl.
            rewrite filter_app with (P:=gfunbods_filterfun_l (unscope (fst a))).
            rewrite map_app. rewrite flat_map_app. rewrite app_length.
            rewrite filter_app. rewrite filter_app. rewrite filter_app.
            rewrite map_app. rewrite map_app. rewrite flat_map_app. rewrite flat_map_app.
            rewrite app_length. rewrite app_length.
            match goal with [|- _ = ?n1 + ?n2 + (?n3 + ?n4)] => replace (n1 + n2 + (n3 + n4)) with
              ((n1 + n3) + (n2 + n4)) end; try omega.
            rewrite <- H0. clear H0. f_equal.
            rewrite <- app_length. rewrite <- flat_map_app.
            assert (H: exists a, fst a = fst a0 /\ snd a = snd a0 /\
              exists a' a0, a0 ++ snd a = a' /\ In (fst a, a') (program_cfun_bods_l p ++ program_cfun_bods_g p)).
            { exists a0. split... split... destruct InBods. rewrite <- H. exists (snd a0). exists []. split...
              apply in_or_app. right. left... destruct a0...
            }
            generalize H. generalize (snd a0). induction c; intros...
            assert (Aux: exists a, fst a = fst a0 /\ snd a = c /\
              exists a' a0, a0 ++ snd a = a' /\  In (fst a, a') (program_cfun_bods_l p ++ program_cfun_bods_g p)).
            { clear - H0. destruct H0. destruct H. destruct H0. exists (fst x, c). split... split...
              do 3 destruct H1. simpl. exists x0. rewrite <- H1. exists (x1++[a1]). rewrite H0. rewrite <- app_assoc. split...
              rewrite <- H0. rewrite H1...
            }
            simpl. case_eq (fst a1); intros.
            2:{ destruct a0. destruct q0. simpl. destruct a1. simpl in H1. subst s... }
            ** destruct a0. destruct q0. simpl. destruct a1. simpl in H1. subst s.
               case_eq (eq_TypeName tn (fst q)); intros.
               --- cbn. case_eq (ScopedName_dec (fst a) (local q)); intros.
                   +++ cbn. rewrite app_length. rewrite IHc... clear IHc.
                       case_eq (eq_TypeName t (fst (unscope (fst a))) &&
                         eq_QName (unscope (fst a)) q); intros.
                       *** cbn. rewrite app_length. f_equal.
                           assert (Aux2: exists r, in_dec ScopedName_dec (local q) (map fst l) = right r).
                           { pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
                             unfold dts_ctor_names_unique in Uniq. eapply Sublist.sublist_map in Subl.
                             pose proof (Unique.uniqueness_sublist _ _ Subl Uniq) as Done.
                             simpl in Done. inversion Done; subst. rewrite e0 in H6.
                             case_eq (in_dec ScopedName_dec (local q) (map fst l)); intros.
                             - exfalso. apply H6...
                             - exists n0...
                           }
                           destruct Aux2 as [r Aux2]. rewrite Aux2...
                       *** rewrite e0 in H3. simpl in H3. rewrite eq_QName_refl in H3.
                           rewrite andb_false_iff in H3. destruct H3; try discriminate.
                           destruct H0 as [aH [H_1 [H_2 [aH_3 [a'H_3 [H_3_1 H_3_2]]]]]].
                           simpl in *. subst. destruct aH. simpl in *. destruct q0. inversion H_1; subst.
                           clear - H1 H3 H_3_2. destruct q. simpl in *. rewrite eq_TypeName_eq in H1. subst.
                           assert (t = t0). 2:{ subst. rewrite eq_TypeName_refl in H3. discriminate. }
                           clear H3. pose proof (program_cfun_bods_typecheck_g p) as Typ_g.
                           pose proof (program_cfun_bods_typecheck_l p) as Typ_l.
                           unfold cfun_bods_g_typecheck in Typ_g. unfold cfun_bods_l_typecheck in Typ_l.
                           rewrite Forall_forall in *. apply in_app_or in H_3_2. destruct H_3_2.
                           { apply Typ_l in H. do 4 destruct H. clear - H0. inversion H0; subst.
                             simpl in *.
                             set (el1:=(local (t0,n0),e)). set (el2:=nth (length a'H_3) ctorlist (local (t, n0), x0)).
                             set (el:=(el1,el2)).
                             assert (length (a'H_3 ++ (local (t0, n0), e) :: c) = length ctorlist) as LenAux.
                             { symmetry. apply Nat.eqb_eq. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as H.
                               do 2 rewrite map_length in H...
                             }
                             assert (length a'H_3 < length ctorlist) as Len.
                             { rewrite app_length in LenAux. simpl in LenAux. omega. }
                             assert (In el (combine (a'H_3 ++ (local (t0, n0), e) :: c) ctorlist)).
                             { unfold el. unfold el2. unfold el1. replace (local (t0, n0), e) with
                                 (nth (length a'H_3) (a'H_3 ++ (local (t0, n0), e) :: c) (local (t0, n0), e)).
                               2:{ rewrite app_nth2... rewrite Nat.sub_diag... }
                               rewrite <- combine_nth... rewrite app_nth2... rewrite Nat.sub_diag. apply nth_In.
                               rewrite combine_length. simpl. rewrite LenAux. rewrite Nat.min_id...
                             }
                             rewrite Forall_forall in H12. apply H12 in H. unfold el in H.
                             unfold lookup_ctors in H11.
                             case_eq (filter (eq_TypeName t) (skeleton_dts (program_skeleton p))); intros;
                               rewrite H1 in H11; try discriminate.
                             inversion H11; subst. unfold el1 in H.
                             remember el2 as el2'. destruct el2'. destruct s; try discriminate.
                             destruct q. inversion H; subst. unfold el2 in Heqel2'.
                             pose proof (nth_In _ (local (t, n1), x0)  Len) as H2. rewrite <- Heqel2' in H2.
                             rewrite filter_In in H2. destruct H2 as [_ H2]. rewrite eq_TypeName_eq in H2. simpl in *...
                           }
                           { apply Typ_g in H. do 4 destruct H. clear - H0. inversion H0; subst.
                             simpl in *.
                             set (el1:=(local (t0,n0),e)). set (el2:=nth (length a'H_3) ctorlist (local (t, n0), x0)).
                             set (el:=(el1,el2)).
                             assert (length (a'H_3 ++ (local (t0, n0), e) :: c) = length ctorlist) as LenAux.
                             { symmetry. apply Nat.eqb_eq. pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H13) as H.
                               do 2 rewrite map_length in H...
                             }
                             assert (length a'H_3 < length ctorlist) as Len.
                             { rewrite app_length in LenAux. simpl in LenAux. omega. }
                             assert (In el (combine (a'H_3 ++ (local (t0, n0), e) :: c) ctorlist)).
                             { unfold el. unfold el2. unfold el1. replace (local (t0, n0), e) with
                                 (nth (length a'H_3) (a'H_3 ++ (local (t0, n0), e) :: c) (local (t0, n0), e)).
                               2:{ rewrite app_nth2... rewrite Nat.sub_diag... }
                               rewrite <- combine_nth... rewrite app_nth2... rewrite Nat.sub_diag. apply nth_In.
                               rewrite combine_length. simpl. rewrite LenAux. rewrite Nat.min_id...
                             }
                             rewrite Forall_forall in H12. apply H12 in H. unfold el in H.
                             unfold lookup_ctors in H11.
                             case_eq (filter (eq_TypeName t) (skeleton_dts (program_skeleton p))); intros;
                               rewrite H1 in H11; try discriminate.
                             inversion H11; subst. unfold el1 in H.
                             remember el2 as el2'. destruct el2'. destruct s; try discriminate.
                             destruct q. inversion H; subst. unfold el2 in Heqel2'.
                             pose proof (nth_In _ (local (t, n1), x0)  Len) as H2. rewrite <- Heqel2' in H2.
                             rewrite filter_In in H2. destruct H2 as [_ H2]. rewrite eq_TypeName_eq in H2. simpl in *...
                           }
                   +++ assert (qEq: eq_QName (unscope (fst a)) q = false).
                       { case_eq (eq_QName (unscope (fst a)) q); intros... rewrite eq_QName_eq in *.
                         subst. exfalso. apply n0. inversion Filter; subst. unfold gfunsigs_filterfun_g in H2.
                         destruct a. destruct s; try discriminate...
                       }
                       rewrite qEq. rewrite andb_false_r.
                       case_eq (in_dec ScopedName_dec (local q) (map fst l)); intros...
                       cbn. rewrite app_length. rewrite flat_map_app. rewrite app_length. cbn.
                       rewrite app_length. apply IHc in Aux. rewrite flat_map_app in Aux.
                       rewrite app_length in Aux. simpl in *. omega.
               --- rewrite IHc... case_eq (eq_QName (unscope (fst a)) q); intros.
                   +++ rewrite eq_QName_eq in H2. subst. inversion Filter; subst.
                       unfold gfunsigs_filterfun_l in H4. destruct a. destruct s; try discriminate.
                       simpl in H1. rewrite H1 in H4. discriminate.
                   +++ rewrite andb_false_r...
Qed.

Lemma cfun_lm_unique_1 : forall p (ct : collect_tuple), Unique.unique
    (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_l p)))).
Proof with eauto.
intros. pose proof (program_match_names_unique_cbods_l_gbods_g p ct).
rewrite (proj1 (proj2 (proj2_sig ct))) in *.
rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
rewrite <- flat_map_concat_map in H...
Qed.

Lemma cfun_lm_unique_1_g : forall p (ct : collect_tuple), Unique.unique
    (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_g p)))).
Proof with eauto.
intros. pose proof (program_match_names_unique_cbods_g_gbods_g p ct).
rewrite (proj1 (proj2 (proj2_sig ct))) in *.
rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
rewrite <- flat_map_concat_map in H...
Qed.

Lemma cfun_lm_unique_2 : forall p (ct : collect_tuple), Forall
  (fun x => ~ In x (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_l p)))))
  (concat (map (fst (proj1_sig ct))
    (map snd (program_fun_bods p) ++
     map snd (concat (map snd (program_cfun_bods_g p))) ++
     map snd (concat (map snd (program_gfun_bods_g p)))))).
Proof with eauto.
intros. pose proof ((proj1 (proj2_sig ct)) p).
rewrite (proj1 (proj2 (proj2_sig ct))) in *.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
repeat rewrite map_app in H. repeat rewrite flat_map_app in H. do 2 rewrite app_assoc in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
do 2 rewrite <- app_assoc in H.
match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4) |- _] =>
  replace (l1++l2++l3++l4) with ((l1++l2)++l3++l4) in H
end.
2:{ repeat (try rewrite <- app_assoc; try rewrite app_assoc)... }
apply Unique.unique_app_switch in H. rewrite app_assoc in H.

rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [_ H]].
repeat rewrite <- flat_map_concat_map.
repeat rewrite flat_map_app. rewrite <- app_assoc in H...
Qed.

Lemma cfun_lm_unique_2_g : forall p (ct : collect_tuple), Forall
  (fun x => ~ In x (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_g p)))))
  (concat (map (fst (proj1_sig ct))
    (map snd (program_fun_bods p) ++
     map snd (concat (map snd (program_cfun_bods_l p))) ++
     map snd (concat (map snd (program_gfun_bods_g p)))))).
Proof with eauto.
intros. pose proof ((proj1 (proj2_sig ct)) p).
rewrite (proj1 (proj2 (proj2_sig ct))) in *.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
repeat rewrite map_app in H. repeat rewrite flat_map_app in H. rewrite <- app_assoc in H.
match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with (l1++l2++(l3++l4++l5)) in H
end.
2:{ repeat (try rewrite <- app_assoc; try rewrite app_assoc)... }
apply Unique.unique_app_switch in H. do 2 rewrite <- app_assoc in H.

match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with ((l1++l2++l3)++l4++l5) in H
end.
2:{ repeat (try rewrite <- app_assoc)... }
apply Unique.unique_app_switch in H. rewrite app_assoc in H.

rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
rewrite <- Unique.uniqueness_app_rewrite in H.
destruct H as [_ [_ H]]. repeat rewrite <- flat_map_concat_map.
repeat rewrite flat_map_app...
Qed.

Lemma cfun_lm_unique_2_1 : forall p (ct : collect_tuple), Forall
  (fun x => ~ In x (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_l p)))))
  (concat (map (fst (proj1_sig ct))
    (map snd (program_fun_bods p) ++
     map snd (concat (map snd (program_cfun_bods_g p))) ++
     map snd (concat (map snd (program_gfun_bods_l p)))))).
Proof with eauto.
intros. pose proof ((proj1 (proj2_sig ct)) p).
rewrite (proj1 (proj2 (proj2_sig ct))) in *.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
repeat rewrite map_app in H. repeat rewrite flat_map_app in H. rewrite <- app_assoc in H.

match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with ((l1++l2)++(l3++l4)++l5) in H
end.
2:{ repeat (try rewrite <- app_assoc)... }

apply Unique.unique_app_switch in H. do 2 rewrite app_assoc in H.

rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [_ H]].
repeat rewrite <- flat_map_concat_map.
repeat rewrite flat_map_app. rewrite <- app_assoc in H...
Qed.

Lemma cfun_lm_unique_2_1_g : forall p (ct : collect_tuple), Forall
  (fun x => ~ In x (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (program_cfun_bods_g p)))))
  (concat (map (fst (proj1_sig ct))
    (map snd (program_fun_bods p) ++
     map snd (concat (map snd (program_cfun_bods_l p))) ++
     map snd (concat (map snd (program_gfun_bods_l p)))))).
Proof with eauto.
intros. pose proof ((proj1 (proj2_sig ct)) p).
rewrite (proj1 (proj2 (proj2_sig ct))) in *.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
repeat rewrite map_app in H. repeat rewrite flat_map_app in H. rewrite <- app_assoc in H.

match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with (l1++l2++(l3++l4++l5)) in H
end.
2:{ repeat (try rewrite <- app_assoc)... }
apply Unique.unique_app_switch in H. do 2 rewrite <- app_assoc in H.

match goal with [_ : _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5) |- _] =>
  replace (l1++l2++l3++l4++l5) with ((l1++l2)++l3++(l4++l5)) in H
end.
2:{ repeat (try rewrite <- app_assoc)... }
apply Unique.unique_app_switch in H. rewrite app_assoc in H.

rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
rewrite app_assoc in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [_ H]].
repeat rewrite <- flat_map_concat_map.
repeat rewrite flat_map_app. rewrite <- app_assoc in H...
Qed.

Lemma unique_flat_map_disjoint : forall {A B} (l : list A) (f : A -> list B) f1 f2,
  Unique.unique (flat_map f l) ->
  (forall a, In a l -> (f1 a <> f2 a) \/ (f1 a = false /\ f2 a = false)) ->
  Unique.unique (flat_map f (filter f1 l ++ filter f2 l)).
Proof with eauto.
intros. induction l... rewrite flat_map_app. cbn. case_eq (f1 a); intros.
- assert (f2Neq : f2 a = false).
  { case_eq (f2 a); intros... exfalso. pose proof (H0 a (in_eq a l)). rewrite H1 in H3.
    rewrite H2 in H3. destruct H3. { apply H3... } destruct H3. discriminate.
  }
  rewrite f2Neq. cbn. rewrite <- app_assoc. rewrite flat_map_app in IHl. cbn in H.
  rewrite <- Unique.uniqueness_app_rewrite in H. destruct H. destruct H2.
  rewrite <- Forall_forall in H0. inversion H0; subst. rewrite Forall_forall in H7.
  apply Unique.uniqueness_piecewise...
  + rewrite <- Unique.uniqueness_app_rewrite. split...
    pose proof H2 as H2'. apply IHl in H2'... rewrite <- Unique.uniqueness_app_rewrite in H2'.
    destruct H2'. split... destruct H5.
    rewrite Forall_forall in *. intros. unfold not. intros. apply H3 in H9. apply H9.
    rewrite in_flat_map. rewrite in_flat_map in H10. do 2 destruct H10.
    rewrite filter_In in H10. destruct H10. exists x0. split...
  + rewrite <- Unique.uniqueness_app_rewrite. split...
    pose proof H2 as H2'. apply IHl in H2'... rewrite <- Unique.uniqueness_app_rewrite in H2'.
    destruct H2' as [H4 [H5 H8]]. split...
    rewrite Forall_forall in *. intros. unfold not. intros. apply H3 in H9. apply H9.
    rewrite in_flat_map. rewrite in_flat_map in H10. do 2 destruct H10.
    rewrite filter_In in H10. destruct H10. exists x0. split...
- case_eq (f2 a); intros...
  2:{ rewrite <- flat_map_app. cbn in H. rewrite <- Unique.uniqueness_app_rewrite in H.
    destruct H. destruct H3. apply IHl... intros.
    specialize H0 with (a0:=a0). pose proof (in_cons a _ _ H5). apply H0 in H6...
  }
  rename H2 into f2Eq. cbn.
  apply Unique.unique_app_switch.
  rewrite app_assoc. rewrite <- app_nil_l.  apply Unique.unique_app_switch. cbn.
  rewrite flat_map_app in IHl. cbn in H.
  rewrite <- Unique.uniqueness_app_rewrite in H. destruct H. destruct H2.
  rewrite <- Forall_forall in H0. inversion H0; subst. rewrite Forall_forall in H7.
  apply Unique.uniqueness_piecewise...
  + rewrite <- Unique.uniqueness_app_rewrite. split...
    pose proof H2 as H2'. apply IHl in H2'... rewrite <- Unique.uniqueness_app_rewrite in H2'.
    destruct H2'. split... destruct H5.
    rewrite Forall_forall in *. intros. unfold not. intros. apply H3 in H9. apply H9.
    rewrite in_flat_map. rewrite in_flat_map in H10. do 2 destruct H10.
    rewrite filter_In in H10. destruct H10. exists x0. split...
  + rewrite <- Unique.uniqueness_app_rewrite. split...
    pose proof H2 as H2'. apply IHl in H2'... rewrite <- Unique.uniqueness_app_rewrite in H2'.
    destruct H2' as [H4 [H5 H8]]. split...
    rewrite Forall_forall in *. intros. unfold not. intros. apply H3 in H9. apply H9.
    rewrite in_flat_map. rewrite in_flat_map in H10. do 2 destruct H10.
    rewrite filter_In in H10. destruct H10. exists x0. split...
Qed.

Lemma unique_flat_map_filter : forall {A B} (l : list A) (f : A -> list B) f1,
  Unique.unique (flat_map f l) ->
  Unique.unique (flat_map f (filter f1 l )).
Proof with eauto.
intros. induction l... cbn. case_eq (f1 a); intros.
- cbn in *. rewrite <- Unique.uniqueness_app_rewrite in *. destruct H. destruct H1.
  split... split... rewrite Forall_forall in *. intros. unfold not in *. intros.
  eapply H2... rewrite in_flat_map in *. do 2 destruct H4. exists x0. split...
  rewrite filter_In in H4. destruct H4...
- cbn in H. rewrite <- Unique.uniqueness_app_rewrite in H. destruct H. destruct H1...
Qed.

Lemma new_gfun_bods_unique_aux_g : forall p tn (ct : collect_tuple)
(l : list (ScopedName * list TypeName))
(SameGL1 : Forall
            (fun x : ScopedName * list TypeName =>
             match fst x with
             | local _ => true
             | global _ => false
             end = false) l)
(SameTyp1 : Forall
             (fun x : ScopedName * list TypeName =>
              fst (unscope (fst x)) = tn) l)
(Uniq1' : Unique.unique (map fst l))
(Uniq1 : Unique.unique l),
  Unique.unique
  (flat_map (fst (proj1_sig ct))
     (map snd
        (flat_map snd
           (map
              (fun ctor : ScopedName * list TypeName =>
               (unscope (fst ctor),
               map
                 (fun x : ScopedName * (ScopedName * expr) =>
                  (fst x,
                  switch_indices_aux (program_skeleton p) (fst x)
                    (length (snd ctor)) tn (snd (snd x))))
                 (globalize_aux
                    (filter (gfunbods_filterfun_g (unscope (fst ctor)))
                       (flat_map
                          (fun x : QName * list (ScopedName * expr) =>
                           map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                          (program_cfun_bods_g p)))) ++
               map
                 (fun x : ScopedName * (ScopedName * expr) =>
                  (fst x,
                  switch_indices_aux (program_skeleton p) (fst x)
                    (length (snd ctor)) tn (snd (snd x))))
                 (localize_aux
                    (filter (gfunbods_filterfun_g (unscope (fst ctor)))
                       (flat_map
                          (fun x : QName * list (ScopedName * expr) =>
                           map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                          (program_cfun_bods_l p)))))) l)))).
Proof with eauto.
intros.
assert (length l <= length l) as Len... generalize dependent Len.
      generalize dependent l. intro l. generalize (length l) at 2. intro n. generalize dependent l.
      induction n; intros; [ destruct l; cbn in Len; try omega; constructor |].
      destruct l; [constructor |]. cbn in *.
      rewrite map_app. rewrite flat_map_app.
      pose proof IHn as IHn_1. specialize IHn_1 with (l:=l).
      inversion Uniq1; subst. pose proof H2 as H2'.
      apply IHn_1 in H2'; try omega.
      2:{ inversion SameGL1; subst... }
      2:{ inversion SameTyp1; subst... }
      2:{ inversion Uniq1'; subst... }
      clear - H1 H2 H2' IHn Len Uniq1 Uniq1' SameTyp1 SameGL1.
      match goal with [_ : Unique.unique (flat_map ?f ?l') |- _] =>
        set (rhs:=flat_map f l') in * end.
      case_eq rhs; intros.
      { rewrite app_nil_r. rewrite <- map_app. rewrite map_map. cbn.
        rewrite flat_map_concat_map. rewrite map_map.
        erewrite map_ext.
        2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
        rewrite <- map_map. rewrite map_app. unfold globalize_aux. unfold localize_aux.
        repeat rewrite map_map. cbn. rewrite <- map_app. rewrite map_map.
        rewrite <- flat_map_concat_map. rewrite <- filter_app. rewrite <- flat_map_app.
        apply unique_flat_map_filter. clear.
        pose proof ((proj1 (proj2_sig ct)) p).
        rewrite (proj1 (proj2 (proj2_sig ct))) in H.
        rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
        rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
        rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
        rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_concat_map.
        rewrite concat_map. rewrite map_map. erewrite map_ext.
        2:{ intros. rewrite map_map. cbn. reflexivity. }
        rewrite <- map_map. rewrite <- concat_map. rewrite <- map_map.
        repeat rewrite <- flat_map_concat_map...
      }
      case_eq l; intros. { unfold rhs in H. rewrite H0 in H. cbn in H. discriminate. }
      unfold rhs in H. rewrite H0 in H. cbn in H.
      clear - H H0 H1 H2 IHn Len Uniq1 Uniq1' SameTyp1 SameGL1.
      rewrite map_app in H. rewrite flat_map_app in H. rewrite <- H. clear H.
      apply Unique.uniqueness_piecewise.
      -- repeat rewrite <- map_app. repeat rewrite map_map. cbn.
         repeat rewrite flat_map_concat_map. repeat rewrite map_map.
         erewrite map_ext.
         2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
         erewrite map_ext with (l:=globalize_aux
           (filter (gfunbods_filterfun_g (unscope (fst p1))) _) ++ _).
         2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
         repeat rewrite map_app. unfold globalize_aux. unfold localize_aux.
         repeat rewrite map_map. cbn. repeat rewrite <- map_app.
         repeat rewrite <- flat_map_concat_map. rewrite <- flat_map_app.
         repeat rewrite <- filter_app. repeat rewrite <- flat_map_app.
         unfold QName.
         rewrite filter_ext with (g:=fun x =>
           match fst (snd x) with global _ => true | _ => false end &&
           eq_TypeName (fst (fst x)) (fst (unscope (fst p0))) &&
           eq_QName (unscope (fst p0)) (unscope (fst (snd x)))).
         2:{ intros. unfold gfunbods_filterfun_g. destruct a. destruct p2. destruct p3.
           cbn. destruct s; try rewrite andb_false_l...
         }
         repeat rewrite <- filter_compose.
         rewrite filter_ext with (f:=gfunbods_filterfun_g _)(g:=fun x =>
           match fst (snd x) with global _ => true | _ => false end &&
           eq_TypeName (fst (fst x)) (fst (unscope (fst p1))) &&
           eq_QName (unscope (fst p1)) (unscope (fst (snd x)))).
         2:{ intros. unfold gfunbods_filterfun_g. destruct a. destruct q0. destruct p2.
           cbn. destruct s; try rewrite andb_false_l...
         }
         repeat rewrite <- filter_compose.
         replace (fst (unscope (fst p0))) with (fst (unscope (fst p1))).
         2:{ subst l. inversion SameTyp1; subst. inversion H4; subst... }
         repeat rewrite <- filter_app. rewrite filter_filter. rewrite filter_app.
         do 2 rewrite filter_compose.
         apply unique_flat_map_filter.
         apply unique_flat_map_disjoint.
         ++ pose proof ((proj1 (proj2_sig ct)) p).
            rewrite (proj1 (proj2 (proj2_sig ct))) in H.
            rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
            rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
            rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
            rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_concat_map.
            rewrite concat_map. rewrite map_map. erewrite map_ext.
            2:{ intros. rewrite map_map. cbn. reflexivity. }
            rewrite <- map_map. rewrite <- concat_map. rewrite <- map_map.
            repeat rewrite <- flat_map_concat_map...
         ++ clear IHn. intros. unfold gfunbods_filterfun_g. destruct a. cbn.
            subst l. case_eq (fst p3); intros; cbn. { right... }
            case_eq (eq_QName (unscope (fst p0)) q0); intros.
            { case_eq (eq_QName (unscope (fst p1)) q0); intros.
              { exfalso. inversion Uniq1'; subst. apply H7.
                left. rewrite eq_QName_eq in *. inversion SameGL1; subst.
                inversion H10; subst. destruct p0. destruct s; try discriminate.
                destruct p1. destruct s; try discriminate.
                cbn in H4. rewrite H4...
              }
              left. unfold not. intros. discriminate.
            }
            case_eq (eq_QName (unscope (fst p1)) q0); intros.
            { left. unfold not. intros. discriminate. }
            right...
      -- specialize IHn with (l:=p1::l1). cbn in IHn. subst l.
         rewrite map_app in IHn. rewrite flat_map_app in IHn. apply IHn...
         2:{ inversion SameTyp1; subst... }
         2:{ inversion Uniq1'; subst... }
         2:{ cbn in Len. omega. }
         inversion SameGL1; subst...
      -- specialize IHn with (l:=p0::l1). cbn in IHn.
         rewrite map_app in IHn. rewrite flat_map_app in IHn.
         subst l. inversion H2; subst. apply IHn; [| | constructor | constructor |]...
         ++ inversion SameGL1; subst. constructor... inversion H6...
         ++ inversion SameTyp1; subst. constructor... inversion H6...
         ++ inversion Uniq1'; subst.
            unfold not in *. intros. apply H5. right...
         ++ cbn in Uniq1'. inversion Uniq1'; subst. inversion H6...
         ++ inversion Uniq1; subst.
            unfold not in *. intros. apply H5. right...
         ++ cbn in Len. omega.
Qed.

Lemma new_gfun_bods_unique_aux_l : forall p tn
(ct : collect_tuple)
(l : list (ScopedName * list TypeName))
(SameGL2 : Forall
            (fun x : ScopedName * list TypeName =>
             match fst x with
             | global _ => true
             | local _ => false
             end = false) l)
(SameTyp2 : Forall
             (fun x : ScopedName * list TypeName =>
              fst (unscope (fst x)) = tn) l)
(Uniq2' : Unique.unique (map fst l))
(Uniq2 : Unique.unique l),
  Unique.unique
  (flat_map (fst (proj1_sig ct))
     (map snd
        (flat_map snd
           (map
              (fun ctor : ScopedName * list TypeName =>
               (unscope (fst ctor),
               map
                 (fun x : ScopedName * (ScopedName * expr) =>
                  (fst x,
                  switch_indices_aux (program_skeleton p) (fst x)
                    (length (snd ctor)) tn (snd (snd x))))
                 (globalize_aux
                    (filter (gfunbods_filterfun_l (unscope (fst ctor)))
                       (flat_map
                          (fun x : QName * list (ScopedName * expr) =>
                           map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                          (program_cfun_bods_g p)))) ++
               map
                 (fun x : ScopedName * (ScopedName * expr) =>
                  (fst x,
                  switch_indices_aux (program_skeleton p) (fst x)
                    (length (snd ctor)) tn (snd (snd x))))
                 (localize_aux
                    (filter (gfunbods_filterfun_l (unscope (fst ctor)))
                       (flat_map
                          (fun x : QName * list (ScopedName * expr) =>
                           map (fun y : ScopedName * expr => (fst x, y)) (snd x))
                          (program_cfun_bods_l p)))))) l)))).
Proof with eauto.
intros.
assert (length l <= length l) as Len... generalize dependent Len.
         generalize dependent l. intro l. generalize (length l) at 2. intro n. generalize dependent l.
         induction n; intros; [ destruct l; cbn in Len; try omega; constructor |].
         destruct l; [constructor |]. cbn in *.
         rewrite map_app. rewrite flat_map_app.
         pose proof IHn as IHn_1. specialize IHn_1 with (l:=l).
         inversion Uniq2; subst. pose proof H2 as H2'.
         apply IHn_1 in H2'; try omega.
         2:{ inversion SameGL2; subst... }
         2:{ inversion SameTyp2; subst... }
         2:{ inversion Uniq2'; subst... }
         clear - H1 H2 H2' IHn Len Uniq2 Uniq2' SameTyp2 SameGL2.
         match goal with [_ : Unique.unique (flat_map ?f ?l') |- _] =>
           set (rhs:=flat_map f l') in * end.
         case_eq rhs; intros.
         { rewrite app_nil_r. rewrite <- map_app. rewrite map_map. cbn.
           rewrite flat_map_concat_map. rewrite map_map.
           erewrite map_ext.
           2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
           rewrite <- map_map. rewrite map_app. unfold globalize_aux. unfold localize_aux.
           repeat rewrite map_map. cbn. rewrite <- map_app. rewrite map_map.
           rewrite <- flat_map_concat_map. rewrite <- filter_app. rewrite <- flat_map_app.
           apply unique_flat_map_filter. clear.
           pose proof ((proj1 (proj2_sig ct)) p).
           rewrite (proj1 (proj2 (proj2_sig ct))) in H.
           rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
           rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
           rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
           rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_concat_map.
           rewrite concat_map. rewrite map_map. erewrite map_ext.
           2:{ intros. rewrite map_map. cbn. reflexivity. }
           rewrite <- map_map. rewrite <- concat_map. rewrite <- map_map.
           repeat rewrite <- flat_map_concat_map...
        }
        case_eq l; intros. { unfold rhs in H. rewrite H0 in H. cbn in H. discriminate. }
        unfold rhs in H. rewrite H0 in H. cbn in H.
        clear - H H0 H1 H2 IHn Len Uniq2 Uniq2' SameTyp2 SameGL2.
        rewrite map_app in H. rewrite flat_map_app in H. rewrite <- H. clear H.
        apply Unique.uniqueness_piecewise.
        ++ repeat rewrite <- map_app. repeat rewrite map_map. cbn.
           repeat rewrite flat_map_concat_map. repeat rewrite map_map.
           erewrite map_ext.
           2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
           erewrite map_ext with (l:=globalize_aux
             (filter (gfunbods_filterfun_l (unscope (fst p1))) _) ++ _).
           2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
           repeat rewrite map_app. unfold globalize_aux. unfold localize_aux.
           repeat rewrite map_map. cbn. repeat rewrite <- map_app.
           repeat rewrite <- flat_map_concat_map. rewrite <- flat_map_app.
           repeat rewrite <- filter_app. repeat rewrite <- flat_map_app.
           unfold QName.
           rewrite filter_ext with (g:=fun x =>
             match fst (snd x) with local _ => true | _ => false end &&
             eq_TypeName (fst (fst x)) (fst (unscope (fst p0))) &&
             eq_QName (unscope (fst p0)) (unscope (fst (snd x)))).
           2:{ intros. unfold gfunbods_filterfun_l. destruct a. destruct p2. destruct p3.
             cbn. destruct s; try rewrite andb_false_l...
           }
           repeat rewrite <- filter_compose.
           rewrite filter_ext with (f:=gfunbods_filterfun_l _)(g:=fun x =>
             match fst (snd x) with local _ => true | _ => false end &&
             eq_TypeName (fst (fst x)) (fst (unscope (fst p1))) &&
             eq_QName (unscope (fst p1)) (unscope (fst (snd x)))).
           2:{ intros. unfold gfunbods_filterfun_l. destruct a. destruct q0. destruct p2.
             cbn. destruct s; try rewrite andb_false_l...
           }
           repeat rewrite <- filter_compose.
           replace (fst (unscope (fst p0))) with (fst (unscope (fst p1))).
           2:{ subst l. inversion SameTyp2; subst. inversion H4; subst... }
           repeat rewrite <- filter_app. rewrite filter_filter. rewrite filter_app.
           do 2 rewrite filter_compose.
           apply unique_flat_map_filter.
           apply unique_flat_map_disjoint.
           ** pose proof ((proj1 (proj2_sig ct)) p).
              rewrite (proj1 (proj2 (proj2_sig ct))) in H.
              rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
              rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
              rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
              rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_concat_map.
              rewrite concat_map. rewrite map_map. erewrite map_ext.
              2:{ intros. rewrite map_map. cbn. reflexivity. }
              rewrite <- map_map. rewrite <- concat_map. rewrite <- map_map.
              repeat rewrite <- flat_map_concat_map...
           ** clear IHn. intros. unfold gfunbods_filterfun_l. destruct a. cbn.
              subst l. case_eq (fst p3); intros; cbn. 2:{ right... }
              case_eq (eq_QName (unscope (fst p0)) q0); intros.
              { case_eq (eq_QName (unscope (fst p1)) q0); intros.
                { exfalso. inversion Uniq2'; subst. apply H7.
                  left. rewrite eq_QName_eq in *. inversion SameGL2; subst.
                  inversion H10; subst. destruct p0. destruct s; try discriminate.
                  destruct p1. destruct s; try discriminate.
                  cbn in H4. rewrite H4...
                }
                left. unfold not. intros. discriminate.
              }
              case_eq (eq_QName (unscope (fst p1)) q0); intros.
              { left. unfold not. intros. discriminate. }
              right...
        ++ specialize IHn with (l:=p1::l1). cbn in IHn. subst l.
           rewrite map_app in IHn. rewrite flat_map_app in IHn. apply IHn...
           2:{ inversion SameTyp2; subst... }
           2:{ inversion Uniq2'; subst... }
           2:{ cbn in Len. omega. }
           inversion SameGL2; subst...
        ++ specialize IHn with (l:=p0::l1). cbn in IHn.
           rewrite map_app in IHn. rewrite flat_map_app in IHn.
           subst l. inversion H2; subst. apply IHn; [| | constructor | constructor |]...
           ** inversion SameGL2; subst. constructor... inversion H6...
           ** inversion SameTyp2; subst. constructor... inversion H6...
           ** inversion Uniq2'; subst.
              unfold not in *. intros. apply H5. right...
           ** cbn in Uniq2'. inversion Uniq2'; subst. inversion H6...
           ** inversion Uniq2; subst.
              unfold not in *. intros. apply H5. right...
           ** cbn in Len. omega.
Qed.


Lemma new_gfun_bods_unique : forall p tn (ct : collect_tuple), Unique.unique
  (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (new_gfun_bods_g p tn))) ++
   flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (new_gfun_bods_l p tn)))).
Proof with eauto.
intros. unfold new_gfun_bods_g. unfold new_gfun_bods_l.
repeat rewrite flat_map_app. repeat rewrite map_app. repeat rewrite flat_map_app.
rewrite <- app_assoc. apply Unique.unique_app_switch. rewrite <- app_assoc. rewrite app_assoc.
assert (Unique.unique (filter (gfunsigs_filterfun_g tn)
                 (skeleton_ctors (program_skeleton p)))) as Uniq1.
  { pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)).
    unfold cdts_dtor_names_unique in H. apply Unique.uniqueness_map in H.
    apply Unique.filter_unique...
  }
  assert (Unique.unique (filter (gfunsigs_filterfun_l tn)
               (skeleton_ctors (program_skeleton p)))) as Uniq2.
  { pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)).
    unfold cdts_dtor_names_unique in H. apply Unique.uniqueness_map in H.
    apply Unique.filter_unique...
  }
  assert (Unique.unique (map fst (filter (gfunsigs_filterfun_g tn)
               (skeleton_ctors (program_skeleton p))))) as Uniq1'.
  { pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)).
    unfold dts_ctor_names_unique in H. erewrite filter_ext.
    { rewrite filter_map. apply Unique.filter_unique... }
    intros. unfold gfunsigs_filterfun_g. destruct a. cbn. reflexivity.
  }
  assert (Unique.unique (map fst (filter (gfunsigs_filterfun_l tn)
               (skeleton_ctors (program_skeleton p))))) as Uniq2'.
  { pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)).
    unfold dts_ctor_names_unique in H. erewrite filter_ext.
    { rewrite filter_map. apply Unique.filter_unique... }
    intros. unfold gfunsigs_filterfun_l. destruct a. cbn. reflexivity.
  }
  assert (Forall (fun x => fst (unscope (fst x)) = tn)
    (filter (gfunsigs_filterfun_g tn)
      (skeleton_ctors (program_skeleton p)))) as SameTyp1.
  { clear. induction (skeleton_ctors (program_skeleton p)). { cbn. constructor. }
    cbn. case_eq (gfunsigs_filterfun_g tn a); intros... constructor...
    unfold gfunsigs_filterfun_g in H. destruct a. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H...
  }
  assert (Forall (fun x => fst (unscope (fst x)) = tn)
    (filter (gfunsigs_filterfun_l tn)
      (skeleton_ctors (program_skeleton p)))) as SameTyp2.
  { clear. induction (skeleton_ctors (program_skeleton p)). { cbn. constructor. }
    cbn. case_eq (gfunsigs_filterfun_l tn a); intros... constructor...
    unfold gfunsigs_filterfun_l in H. destruct a. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H...
  }
  assert (Forall (fun x => match fst x with local _ => true | _ => false end = false)
    (filter (gfunsigs_filterfun_g tn)
      (skeleton_ctors (program_skeleton p)))) as SameGL1.
  { clear. induction (skeleton_ctors (program_skeleton p)). { cbn. constructor. }
    cbn. case_eq (gfunsigs_filterfun_g tn a); intros... constructor...
    unfold gfunsigs_filterfun_g in H. destruct a. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H...
  }
  assert (Forall (fun x => match fst x with global _ => true | _ => false end = false)
    (filter (gfunsigs_filterfun_l tn)
      (skeleton_ctors (program_skeleton p)))) as SameGL2.
  { clear. induction (skeleton_ctors (program_skeleton p)). { cbn. constructor. }
    cbn. case_eq (gfunsigs_filterfun_l tn a); intros... constructor...
    unfold gfunsigs_filterfun_l in H. destruct a. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H...
  }
apply Unique.uniqueness_piecewise.
- rewrite <- app_assoc. apply Unique.uniqueness_piecewise.
  + generalize dependent Uniq1. generalize dependent Uniq2.
    generalize dependent Uniq1'. generalize dependent Uniq2'.
    generalize dependent SameTyp1. generalize dependent SameTyp2.
    generalize dependent SameGL1. generalize dependent SameGL2.
    generalize ((filter (gfunsigs_filterfun_g tn)
                 (skeleton_ctors (program_skeleton p)))).
    generalize ((filter (gfunsigs_filterfun_l tn)
                 (skeleton_ctors (program_skeleton p)))).
    induction l; intros.
    * cbn. rewrite app_nil_r.
      apply new_gfun_bods_unique_aux_g...
    * cbn. rewrite map_app. rewrite flat_map_app.
      apply Unique.uniqueness_piecewise.
      -- clear - SameGL1 SameTyp1 Uniq1' Uniq1.
         induction l0.
         { cbn. unfold globalize_aux. unfold localize_aux. rewrite <- map_app. rewrite map_map.
           cbn. rewrite map_app. repeat rewrite map_map. rewrite flat_map_concat_map.
           rewrite map_app. repeat rewrite map_map. cbn. erewrite map_ext.
           2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
           erewrite map_ext with (l:=filter _ (_ _ (program_cfun_bods_l _))).
           2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
           rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
           rewrite <- flat_map_concat_map. apply unique_flat_map_filter.
           clear. pose proof ((proj1 (proj2_sig ct)) p).
           rewrite (proj1 (proj2 (proj2_sig ct))) in H.
           rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
           rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
           rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
           rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_concat_map.
           rewrite concat_map. rewrite map_map. erewrite map_ext.
           2:{ intros. rewrite map_map. cbn. reflexivity. }
           rewrite <- map_map. rewrite <- concat_map. rewrite <- map_map.
           repeat rewrite <- flat_map_concat_map...
         }
         cbn. rewrite map_app. rewrite flat_map_app. rewrite <- app_assoc.
         apply Unique.uniqueness_piecewise.
         ++ clear IHl0.
            match goal with
              [|- _ (?lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map ?m l0))))] =>
              replace (lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m l0)))) with
                (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m (a0::l0)))))
            end.
            2:{ cbn. rewrite map_app. rewrite flat_map_app... }
            apply new_gfun_bods_unique_aux_g...
         ++ inversion SameGL1; subst. inversion SameTyp1; subst. inversion Uniq1'; subst.
            inversion Uniq1; subst. apply IHl0...
         ++ clear.
            match goal with [|- _ (_ ++ ?rhs')] => remember rhs' as rhs end.
            cbn in *. unfold globalize_aux in *. unfold localize_aux in *.
            rewrite <- map_app in *. rewrite map_map in *.
            cbn in *. rewrite map_app in *. repeat rewrite map_map in *.
            rewrite flat_map_concat_map in *.
            rewrite map_app in *. repeat rewrite map_map in *. cbn in *. erewrite map_ext in *.
            2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            erewrite map_ext with (l:=filter _ (_ _ (program_cfun_bods_l _))).
            2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            erewrite map_ext with (l:=filter _ (_ _ (program_cfun_bods_l _))) in Heqrhs.
            2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            rewrite <- map_app in *. rewrite <- filter_app in *. rewrite <- flat_map_app in *.
            rewrite <- flat_map_concat_map in *.
            subst rhs. rewrite <- flat_map_app. apply unique_flat_map_disjoint.
            2:{ intros. unfold gfunbods_filterfun_g. unfold gfunbods_filterfun_l.
              destruct a1. destruct q. destruct p0. destruct s.
              - case_eq (eq_TypeName t (fst (unscope (fst a)))); intros...
                case_eq (eq_QName (unscope (fst a)) q); intros...
                left. cbn. unfold not. intros. discriminate.
              - case_eq (eq_TypeName t (fst (unscope (fst a0)))); intros...
                case_eq (eq_QName (unscope (fst a0)) q); intros...
                left. cbn. unfold not. intros. discriminate.
            }
            clear. pose proof ((proj1 (proj2_sig ct)) p).
            rewrite (proj1 (proj2 (proj2_sig ct))) in H.
            rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
            rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
            rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
            rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_concat_map.
            rewrite concat_map. rewrite map_map. erewrite map_ext.
            2:{ intros. rewrite map_map. cbn. reflexivity. }
            rewrite <- map_map. rewrite <- concat_map. rewrite <- map_map.
            repeat rewrite <- flat_map_concat_map...
      -- match goal with
           [|- _ (?lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map ?m l))))] =>
           replace (lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m l)))) with
             (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m (a::l)))))
         end.
         2:{ cbn. rewrite map_app. rewrite flat_map_app... }
         clear IHl. generalize dependent (a::l). intros. clear l. rename l1 into l.
         apply new_gfun_bods_unique_aux_l...
     -- inversion Uniq2; subst. inversion Uniq2'; subst.
        inversion SameTyp2; subst. inversion SameGL2; subst.
        apply IHl...
  + generalize dependent (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))); intros.
    induction l.
    { cbn. clear. pose proof ((proj1 (proj2_sig ct)) p).
      rewrite (proj1 (proj2 (proj2_sig ct))) in H.
      rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
      rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
      rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
      repeat rewrite flat_map_concat_map. repeat rewrite map_map. cbn. rewrite <- map_map with (f:=snd).
      rewrite <- flat_map_concat_map in H. rewrite flat_map_app in H. rewrite map_app in H.
      rewrite flat_map_app in H. rewrite <- Unique.uniqueness_app_rewrite in H.
      destruct H as [_ [H _]]. repeat rewrite flat_map_concat_map in H. rewrite <- map_map with (f:=snd).
      rewrite <- concat_map. repeat rewrite map_map.
      erewrite map_ext.
      { rewrite map_map in H. apply H. }
      intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct))))...
    }
    cbn. rewrite map_app. rewrite flat_map_app. rewrite <- app_assoc.
    apply Unique.uniqueness_piecewise.
    * match goal with
        [|- _ (?lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map ?m l))))] =>
        replace (lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m l)))) with
          (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m (a::l)))))
      end.
      2:{ cbn. rewrite map_app. rewrite flat_map_app... }
      clear IHl. generalize dependent (a::l). intros. clear l. rename l0 into l.
      apply new_gfun_bods_unique_aux_l...
    * inversion Uniq2; subst. inversion Uniq2'; subst.
      inversion SameTyp2; subst. inversion SameGL2; subst.
      apply IHl...
    * clear. pose proof ((proj1 (proj2_sig ct)) p).
      rewrite (proj1 (proj2 (proj2_sig ct))) in H.
      unfold globalize_aux. unfold localize_aux.
      repeat rewrite map_app. repeat rewrite map_map. cbn.
      repeat rewrite flat_map_concat_map. rewrite map_app. repeat rewrite map_map.
      cbn. rewrite <- map_map with (l:=program_gfun_bods_l p). rewrite concat_map.
      repeat rewrite map_map. erewrite map_ext with (l:=program_gfun_bods_l p).
      2:{ intros. rewrite map_map. erewrite map_ext.
        2:{ intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
        reflexivity.
      }
      erewrite map_ext with (l:=filter _ _).
      2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      erewrite map_ext with (l:=filter _ (_ (_ _ (program_cfun_bods_l p)))).
      2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      rewrite <- map_app. rewrite <- filter_app.
      apply Unique.uniqueness_app.
      -- rewrite <- flat_map_concat_map. apply unique_flat_map_filter.
         rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H _].
         rewrite flat_map_app. repeat rewrite flat_map_concat_map.
         repeat rewrite concat_map. repeat rewrite map_map.
         erewrite map_ext. 2:{ intros. rewrite map_map. cbn. reflexivity. }
         erewrite map_ext with (l:=program_cfun_bods_l p).
         2:{ intros. rewrite map_map. cbn. reflexivity. }
         rewrite <- map_map. rewrite <- concat_map.
         rewrite <- map_map with (l:=program_cfun_bods_l p). rewrite <- concat_map.
         rewrite flat_map_concat_map in H. rewrite map_map in H.
         rewrite <- concat_app. rewrite <- map_app. rewrite <- concat_app. rewrite <- map_app...
      -- rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite map_app in H. rewrite concat_app in H. rewrite map_app in H.
         rewrite flat_map_app in H. rewrite <- Unique.uniqueness_app_rewrite in H.
         destruct H as [_ [H _]]. rewrite <- map_map. rewrite <- concat_map.
         rewrite <- map_map. rewrite flat_map_concat_map in H...
      -- rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H. cbn in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [_ H]].
         rewrite Forall_forall in *. intros. unfold not in *. intros. apply H with (x:=x).
         ++ rewrite map_app. rewrite concat_app. rewrite map_app. rewrite flat_map_app.
            apply in_or_app. right. rewrite <- map_map in H1. rewrite <- concat_map in H1.
            rewrite <- map_map in H1. rewrite flat_map_concat_map...
         ++ clear - H0. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in *.
            destruct H0. destruct H. exists (snd (snd x0)). split...
            rewrite filter_In in H. destruct H. rewrite in_map_iff. exists (snd x0).
            split... apply in_app_or in H. destruct H.
            ** rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H.
               do 2 destruct H. rewrite in_flat_map. exists x1.
               apply (in_map snd) in H2. rewrite map_map in H2. cbn in H2. rewrite map_id in H2.
               split... apply in_or_app. left...
            ** rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H.
               do 2 destruct H. rewrite in_flat_map. exists x1.
               apply (in_map snd) in H2. rewrite map_map in H2. cbn in H2. rewrite map_id in H2.
               split... apply in_or_app. right...
  + generalize dependent (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))); intros.
    induction l.
    { cbn. clear. pose proof ((proj1 (proj2_sig ct)) p).
      rewrite (proj1 (proj2 (proj2_sig ct))) in H.
      rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
      rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
      rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
      repeat rewrite flat_map_concat_map. repeat rewrite map_map. cbn. rewrite <- map_map with (f:=snd).
      rewrite <- flat_map_concat_map in H. rewrite flat_map_app in H. rewrite map_app in H.
      rewrite flat_map_app in H. rewrite <- Unique.uniqueness_app_rewrite in H.
      destruct H as [_ [H _]]. repeat rewrite flat_map_concat_map in H. rewrite <- map_map with (f:=snd).
      rewrite <- concat_map. repeat rewrite map_map.
      erewrite map_ext.
      { rewrite map_map in H. apply H. }
      intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct))))...
    }
    cbn. rewrite map_app. rewrite flat_map_app. rewrite <- app_assoc.
    apply Unique.uniqueness_piecewise.
    * match goal with
        [|- _ (?lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map ?m l))))] =>
        replace (lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m l)))) with
          (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m (a::l)))))
      end.
      2:{ cbn. rewrite map_app. rewrite flat_map_app... }
      clear IHl. generalize dependent (a::l). intros. clear l. rename l0 into l.
      apply new_gfun_bods_unique_aux_g...
    * inversion Uniq1; subst. inversion Uniq1'; subst.
      inversion SameTyp1; subst. inversion SameGL1; subst.
      apply IHl...
    * clear. pose proof ((proj1 (proj2_sig ct)) p).
      rewrite (proj1 (proj2 (proj2_sig ct))) in H.
      unfold globalize_aux. unfold localize_aux.
      repeat rewrite map_app. repeat rewrite map_map. cbn.
      repeat rewrite flat_map_concat_map. rewrite map_app. repeat rewrite map_map.
      cbn. rewrite <- map_map with (l:=program_gfun_bods_l p). rewrite concat_map.
      repeat rewrite map_map. erewrite map_ext with (l:=program_gfun_bods_l p).
      2:{ intros. rewrite map_map. erewrite map_ext.
        2:{ intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
        reflexivity.
      }
      erewrite map_ext with (l:=filter _ _).
      2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      erewrite map_ext with (l:=filter _ (_ (_ _ (program_cfun_bods_l p)))).
      2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      rewrite <- map_app. rewrite <- filter_app.
      apply Unique.uniqueness_app.
      -- rewrite <- flat_map_concat_map. apply unique_flat_map_filter.
         rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H [_ _]].
         rewrite flat_map_app. repeat rewrite flat_map_concat_map.
         repeat rewrite concat_map. repeat rewrite map_map.
         erewrite map_ext. 2:{ intros. rewrite map_map. cbn. reflexivity. }
         erewrite map_ext with (l:=program_cfun_bods_l p).
         2:{ intros. rewrite map_map. cbn. reflexivity. }
         rewrite <- map_map. rewrite <- concat_map.
         rewrite <- map_map with (l:=program_cfun_bods_l p). rewrite <- concat_map.
         rewrite flat_map_concat_map in H. rewrite map_map in H.
         rewrite <- concat_app. rewrite <- map_app. rewrite <- concat_app. rewrite <- map_app...
      -- rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite map_app in H. rewrite concat_app in H. rewrite map_app in H.
         rewrite flat_map_app in H. rewrite <- Unique.uniqueness_app_rewrite in H.
         destruct H as [_ [H _]]. rewrite <- map_map. rewrite <- concat_map.
         rewrite <- map_map. rewrite flat_map_concat_map in H...
      -- rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H. cbn in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [_ H]].
         rewrite Forall_forall in *. intros. unfold not in *. intros. apply H with (x:=x).
         ++ rewrite map_app. rewrite concat_app. rewrite map_app. rewrite flat_map_app.
            apply in_or_app. right. rewrite <- map_map in H1. rewrite <- concat_map in H1.
            rewrite <- map_map in H1. rewrite flat_map_concat_map...
         ++ clear - H0. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in *.
            destruct H0. destruct H. exists (snd (snd x0)). split...
            rewrite filter_In in H. destruct H. rewrite in_map_iff. exists (snd x0).
            split... apply in_app_or in H. destruct H.
            ** rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H.
               do 2 destruct H. rewrite in_flat_map. exists x1.
               apply (in_map snd) in H2. rewrite map_map in H2. cbn in H2. rewrite map_id in H2.
               split... apply in_or_app. left...
            ** rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H.
               do 2 destruct H. rewrite in_flat_map. exists x1.
               apply (in_map snd) in H2. rewrite map_map in H2. cbn in H2. rewrite map_id in H2.
               split... apply in_or_app. right...
- repeat rewrite flat_map_concat_map. repeat rewrite map_map. cbn.
  repeat rewrite concat_map. repeat rewrite map_map.
  erewrite map_ext with (l:=program_gfun_bods_l _).
  2:{ intros. rewrite map_map. erewrite map_ext.
    2:{ intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
    reflexivity.
  }
  erewrite map_ext with (l:=program_gfun_bods_g _).
  2:{ intros. rewrite map_map. erewrite map_ext.
    2:{ intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
    reflexivity.
  }
  pose proof ((proj1 (proj2_sig ct)) p).
  rewrite (proj1 (proj2 (proj2_sig ct))) in H.
  do 2 rewrite map_app in H. do 2 rewrite concat_app in H.
  rewrite <- Unique.uniqueness_app_rewrite in H. destruct H. destruct H0. clear - H0.
  rewrite <- Unique.uniqueness_app_rewrite in H0. destruct H0. destruct H0. clear - H0.
  rewrite <- app_nil_l. apply Unique.unique_app_switch. cbn.
  repeat rewrite <- concat_app. rewrite <- map_app.
  rewrite <- map_map. repeat rewrite <- concat_map. rewrite <- map_map...
- rewrite <- app_assoc. apply Unique.uniqueness_piecewise.
  + generalize dependent Uniq1. generalize dependent Uniq2.
    generalize dependent Uniq1'. generalize dependent Uniq2'.
    generalize dependent SameTyp1. generalize dependent SameTyp2.
    generalize dependent SameGL1. generalize dependent SameGL2.
    generalize ((filter (gfunsigs_filterfun_g tn)
                 (skeleton_ctors (program_skeleton p)))).
    generalize ((filter (gfunsigs_filterfun_l tn)
                 (skeleton_ctors (program_skeleton p)))).
    induction l; intros.
    * cbn. rewrite app_nil_r.
      apply new_gfun_bods_unique_aux_g...
    * cbn. rewrite map_app. rewrite flat_map_app.
      apply Unique.uniqueness_piecewise.
      -- clear - SameGL1 SameTyp1 Uniq1' Uniq1.
         induction l0.
         { cbn. unfold globalize_aux. unfold localize_aux. rewrite <- map_app. rewrite map_map.
           cbn. rewrite map_app. repeat rewrite map_map. rewrite flat_map_concat_map.
           rewrite map_app. repeat rewrite map_map. cbn. erewrite map_ext.
           2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
           erewrite map_ext with (l:=filter _ (_ _ (program_cfun_bods_l _))).
           2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
           rewrite <- map_app. rewrite <- filter_app. rewrite <- flat_map_app.
           rewrite <- flat_map_concat_map. apply unique_flat_map_filter.
           clear. pose proof ((proj1 (proj2_sig ct)) p).
           rewrite (proj1 (proj2 (proj2_sig ct))) in H.
           rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
           rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
           rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H [_ _]].
           rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_concat_map.
           rewrite concat_map. rewrite map_map. erewrite map_ext.
           2:{ intros. rewrite map_map. cbn. reflexivity. }
           rewrite <- map_map. rewrite <- concat_map. rewrite <- map_map.
           repeat rewrite <- flat_map_concat_map...
         }
         cbn. rewrite map_app. rewrite flat_map_app. rewrite <- app_assoc.
         apply Unique.uniqueness_piecewise.
         ++ clear IHl0.
            match goal with
              [|- _ (?lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map ?m l0))))] =>
              replace (lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m l0)))) with
                (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m (a0::l0)))))
            end.
            2:{ cbn. rewrite map_app. rewrite flat_map_app... }
            apply new_gfun_bods_unique_aux_g...
         ++ inversion SameGL1; subst. inversion SameTyp1; subst. inversion Uniq1'; subst.
            inversion Uniq1; subst. apply IHl0...
         ++ clear.
            match goal with [|- _ (_ ++ ?rhs')] => remember rhs' as rhs end.
            cbn in *. unfold globalize_aux in *. unfold localize_aux in *.
            rewrite <- map_app in *. rewrite map_map in *.
            cbn in *. rewrite map_app in *. repeat rewrite map_map in *.
            rewrite flat_map_concat_map in *.
            rewrite map_app in *. repeat rewrite map_map in *. cbn in *. erewrite map_ext in *.
            2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            erewrite map_ext with (l:=filter _ (_ _ (program_cfun_bods_l _))).
            2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            erewrite map_ext with (l:=filter _ (_ _ (program_cfun_bods_l _))) in Heqrhs.
            2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
            rewrite <- map_app in *. rewrite <- filter_app in *. rewrite <- flat_map_app in *.
            rewrite <- flat_map_concat_map in *.
            subst rhs. rewrite <- flat_map_app. apply unique_flat_map_disjoint.
            2:{ intros. unfold gfunbods_filterfun_g. unfold gfunbods_filterfun_l.
              destruct a1. destruct q. destruct p0. destruct s.
              - case_eq (eq_TypeName t (fst (unscope (fst a)))); intros...
                case_eq (eq_QName (unscope (fst a)) q); intros...
                left. cbn. unfold not. intros. discriminate.
              - case_eq (eq_TypeName t (fst (unscope (fst a0)))); intros...
                case_eq (eq_QName (unscope (fst a0)) q); intros...
                left. cbn. unfold not. intros. discriminate.
            }
            clear. pose proof ((proj1 (proj2_sig ct)) p).
            rewrite (proj1 (proj2 (proj2_sig ct))) in H.
            rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
            rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
            rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H [_ _]].
            rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_concat_map.
            rewrite concat_map. rewrite map_map. erewrite map_ext.
            2:{ intros. rewrite map_map. cbn. reflexivity. }
            rewrite <- map_map. rewrite <- concat_map. rewrite <- map_map.
            repeat rewrite <- flat_map_concat_map...
      -- match goal with
           [|- _ (?lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map ?m l))))] =>
           replace (lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m l)))) with
             (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m (a::l)))))
         end.
         2:{ cbn. rewrite map_app. rewrite flat_map_app... }
         clear IHl. generalize dependent (a::l). intros. clear l. rename l1 into l.
         apply new_gfun_bods_unique_aux_l...
     -- inversion Uniq2; subst. inversion Uniq2'; subst.
        inversion SameTyp2; subst. inversion SameGL2; subst.
        apply IHl...
  + generalize dependent (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))); intros.
    induction l.
    { cbn. clear. pose proof ((proj1 (proj2_sig ct)) p).
      rewrite (proj1 (proj2 (proj2_sig ct))) in H.
      rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
      rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
      rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
      repeat rewrite flat_map_concat_map. repeat rewrite map_map. cbn. rewrite <- map_map with (f:=snd).
      rewrite <- flat_map_concat_map in H. rewrite flat_map_app in H. rewrite map_app in H.
      rewrite flat_map_app in H. rewrite <- Unique.uniqueness_app_rewrite in H.
      destruct H as [H [_ _]]. repeat rewrite flat_map_concat_map in H. rewrite <- map_map with (f:=snd).
      rewrite <- concat_map. repeat rewrite map_map.
      erewrite map_ext.
      { rewrite map_map in H. apply H. }
      intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct))))...
    }
    cbn. rewrite map_app. rewrite flat_map_app. rewrite <- app_assoc.
    apply Unique.uniqueness_piecewise.
    * match goal with
        [|- _ (?lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map ?m l))))] =>
        replace (lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m l)))) with
          (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m (a::l)))))
      end.
      2:{ cbn. rewrite map_app. rewrite flat_map_app... }
      clear IHl. generalize dependent (a::l). intros. clear l. rename l0 into l.
      apply new_gfun_bods_unique_aux_l...
    * inversion Uniq2; subst. inversion Uniq2'; subst.
      inversion SameTyp2; subst. inversion SameGL2; subst.
      apply IHl...
    * clear. pose proof ((proj1 (proj2_sig ct)) p).
      rewrite (proj1 (proj2 (proj2_sig ct))) in H.
      unfold globalize_aux. unfold localize_aux.
      repeat rewrite map_app. repeat rewrite map_map. cbn.
      repeat rewrite flat_map_concat_map. rewrite map_app. repeat rewrite map_map.
      cbn. rewrite <- map_map with (l:=program_gfun_bods_g p). rewrite concat_map.
      repeat rewrite map_map. erewrite map_ext with (l:=program_gfun_bods_g p).
      2:{ intros. rewrite map_map. erewrite map_ext.
        2:{ intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
        reflexivity.
      }
      erewrite map_ext with (l:=filter _ _).
      2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      erewrite map_ext with (l:=filter _ (_ (_ _ (program_cfun_bods_l p)))).
      2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      rewrite <- map_app. rewrite <- filter_app.
      apply Unique.uniqueness_app.
      -- rewrite <- flat_map_concat_map. apply unique_flat_map_filter.
         rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H [_ _]].
         rewrite flat_map_app. repeat rewrite flat_map_concat_map.
         repeat rewrite concat_map. repeat rewrite map_map.
         erewrite map_ext. 2:{ intros. rewrite map_map. cbn. reflexivity. }
         erewrite map_ext with (l:=program_cfun_bods_l p).
         2:{ intros. rewrite map_map. cbn. reflexivity. }
         rewrite <- map_map. rewrite <- concat_map.
         rewrite <- map_map with (l:=program_cfun_bods_l p). rewrite <- concat_map.
         rewrite flat_map_concat_map in H. rewrite map_map in H.
         rewrite <- concat_app. rewrite <- map_app. rewrite <- concat_app. rewrite <- map_app...
      -- rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite map_app in H. rewrite concat_app in H. rewrite map_app in H.
         rewrite flat_map_app in H. rewrite <- Unique.uniqueness_app_rewrite in H.
         destruct H as [H [_ _]]. rewrite <- map_map. rewrite <- concat_map.
         rewrite <- map_map. rewrite flat_map_concat_map in H...
      -- rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H. cbn in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [_ H]].
         rewrite Forall_forall in *. intros. unfold not in *. intros. apply H with (x:=x).
         ++ rewrite map_app. rewrite concat_app. rewrite map_app. rewrite flat_map_app.
            apply in_or_app. left. rewrite <- map_map in H1. rewrite <- concat_map in H1.
            rewrite <- map_map in H1. rewrite flat_map_concat_map...
         ++ clear - H0. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in *.
            destruct H0. destruct H. exists (snd (snd x0)). split...
            rewrite filter_In in H. destruct H. rewrite in_map_iff. exists (snd x0).
            split... apply in_app_or in H. destruct H.
            ** rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H.
               do 2 destruct H. rewrite in_flat_map. exists x1.
               apply (in_map snd) in H2. rewrite map_map in H2. cbn in H2. rewrite map_id in H2.
               split... apply in_or_app. left...
            ** rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H.
               do 2 destruct H. rewrite in_flat_map. exists x1.
               apply (in_map snd) in H2. rewrite map_map in H2. cbn in H2. rewrite map_id in H2.
               split... apply in_or_app. right...
  + generalize dependent (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))); intros.
    induction l.
    { cbn. clear. pose proof ((proj1 (proj2_sig ct)) p).
      rewrite (proj1 (proj2 (proj2_sig ct))) in H.
      rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
      rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
      rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
      repeat rewrite flat_map_concat_map. repeat rewrite map_map. cbn. rewrite <- map_map with (f:=snd).
      rewrite <- flat_map_concat_map in H. rewrite flat_map_app in H. rewrite map_app in H.
      rewrite flat_map_app in H. rewrite <- Unique.uniqueness_app_rewrite in H.
      destruct H as [H [_ _]]. repeat rewrite flat_map_concat_map in H. rewrite <- map_map with (f:=snd).
      rewrite <- concat_map. repeat rewrite map_map.
      erewrite map_ext.
      { rewrite map_map in H. apply H. }
      intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct))))...
    }
    cbn. rewrite map_app. rewrite flat_map_app. rewrite <- app_assoc.
    apply Unique.uniqueness_piecewise.
    * match goal with
        [|- _ (?lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map ?m l))))] =>
        replace (lhs ++ flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m l)))) with
          (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (map m (a::l)))))
      end.
      2:{ cbn. rewrite map_app. rewrite flat_map_app... }
      clear IHl. generalize dependent (a::l). intros. clear l. rename l0 into l.
      apply new_gfun_bods_unique_aux_g...
    * inversion Uniq1; subst. inversion Uniq1'; subst.
      inversion SameTyp1; subst. inversion SameGL1; subst.
      apply IHl...
    * clear. pose proof ((proj1 (proj2_sig ct)) p).
      rewrite (proj1 (proj2 (proj2_sig ct))) in H.
      unfold globalize_aux. unfold localize_aux.
      repeat rewrite map_app. repeat rewrite map_map. cbn.
      repeat rewrite flat_map_concat_map. rewrite map_app. repeat rewrite map_map.
      cbn. rewrite <- map_map with (l:=program_gfun_bods_g p). rewrite concat_map.
      repeat rewrite map_map. erewrite map_ext with (l:=program_gfun_bods_g p).
      2:{ intros. rewrite map_map. erewrite map_ext.
        2:{ intros. cbn. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
        reflexivity.
      }
      erewrite map_ext with (l:=filter _ _).
      2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      erewrite map_ext with (l:=filter _ (_ (_ _ (program_cfun_bods_l p)))).
      2:{ intros. rewrite (proj2 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      rewrite <- map_app. rewrite <- filter_app.
      apply Unique.uniqueness_app.
      -- rewrite <- flat_map_concat_map. apply unique_flat_map_filter.
         rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H [_ _]].
         rewrite flat_map_app. repeat rewrite flat_map_concat_map.
         repeat rewrite concat_map. repeat rewrite map_map.
         erewrite map_ext. 2:{ intros. rewrite map_map. cbn. reflexivity. }
         erewrite map_ext with (l:=program_cfun_bods_l p).
         2:{ intros. rewrite map_map. cbn. reflexivity. }
         rewrite <- map_map. rewrite <- concat_map.
         rewrite <- map_map with (l:=program_cfun_bods_l p). rewrite <- concat_map.
         rewrite flat_map_concat_map in H. rewrite map_map in H.
         rewrite <- concat_app. rewrite <- map_app. rewrite <- concat_app. rewrite <- map_app...
      -- rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite map_app in H. rewrite concat_app in H. rewrite map_app in H.
         rewrite flat_map_app in H. rewrite <- Unique.uniqueness_app_rewrite in H.
         destruct H as [H [_ _]]. rewrite <- map_map. rewrite <- concat_map.
         rewrite <- map_map. rewrite flat_map_concat_map in H...
      -- rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
         rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H. cbn in H.
         rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [_ H]].
         rewrite Forall_forall in *. intros. unfold not in *. intros. apply H with (x:=x).
         ++ rewrite map_app. rewrite concat_app. rewrite map_app. rewrite flat_map_app.
            apply in_or_app. left. rewrite <- map_map in H1. rewrite <- concat_map in H1.
            rewrite <- map_map in H1. rewrite flat_map_concat_map...
         ++ clear - H0. rewrite <- flat_map_concat_map in H0. rewrite in_flat_map in *.
            destruct H0. destruct H. exists (snd (snd x0)). split...
            rewrite filter_In in H. destruct H. rewrite in_map_iff. exists (snd x0).
            split... apply in_app_or in H. destruct H.
            ** rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H.
               do 2 destruct H. rewrite in_flat_map. exists x1.
               apply (in_map snd) in H2. rewrite map_map in H2. cbn in H2. rewrite map_id in H2.
               split... apply in_or_app. left...
            ** rewrite <- flat_map_concat_map in *. rewrite in_flat_map in H.
               do 2 destruct H. rewrite in_flat_map. exists x1.
               apply (in_map snd) in H2. rewrite map_map in H2. cbn in H2. rewrite map_id in H2.
               split... apply in_or_app. right...
Qed.

Lemma new_cfun_bods_unique : forall p tn (ct : collect_tuple), Unique.unique
  (flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (new_cfun_bods_g p tn))) ++
   flat_map (fst (proj1_sig ct)) (map snd (flat_map snd (new_cfun_bods_l p tn)))).
Proof with eauto.
intros. unfold new_cfun_bods_g. unfold new_cfun_bods_l.
rewrite <- flat_map_app. rewrite <- map_app. rewrite <- flat_map_app. rewrite <- filter_app.
rewrite <- map_app. pose proof ((proj1 (proj2_sig ct)) p).
rewrite (proj1 (proj2 (proj2_sig ct))) in H.
repeat rewrite <- flat_map_concat_map in H. repeat rewrite flat_map_app in H.
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [_ [H _]].
rewrite <- Unique.uniqueness_app_rewrite in H. destruct H as [H [_ _]].
rewrite <- flat_map_app in H. generalize dependent H. unfold cfun_bod.
match goal with [|- _ -> _ (_ _ (_ _ (_ _ (_ _ (_ _ ?l)))))] => generalize l end.
induction l... intros. cbn. cbn in H. rewrite map_app in H.
rewrite flat_map_app in H.
case_eq (negb (eq_TypeName tn (fst (fst a)))); intros.
- cbn. rewrite map_app. rewrite flat_map_app. apply disjoint_app_unique.
  + clear IHl. intros. unfold not. intros.
    rewrite <- Unique.uniqueness_app_rewrite in H. destruct H. destruct H2.
    rewrite Forall_forall in H3. unfold not in H3. apply H3 with (x:=a0).
    * destruct H1. clear - H1. rewrite map_map in H1. cbn in H1.
      rewrite flat_map_concat_map in H1. rewrite map_map in H1. erewrite map_ext in H1.
      2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))). reflexivity. }
      rewrite <- map_map in H1. rewrite flat_map_concat_map...
    * destruct H1. clear - H4. rewrite in_flat_map in H4. destruct H4. destruct H.
      rewrite in_map_iff in H. do 2 destruct H. subst. rewrite in_flat_map in H1.
      destruct H1. destruct H. rewrite filter_In in H. destruct H. rewrite in_map_iff in H.
      do 2 destruct H. destruct x. inversion H; subst. clear H. cbn in H1.
      rewrite in_map_iff in H1. destruct H1. destruct H. subst. cbn in H0.
      rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))) in H0.
      rewrite in_flat_map. eexists. split... apply in_map. rewrite in_flat_map.
      eexists. split...
  + rewrite map_map. cbn. rewrite flat_map_concat_map. rewrite map_map.
    erewrite map_ext. 2:{ intros. rewrite (proj1 (proj2 (proj2 (proj2_sig ct)))).
     reflexivity.
    }
    rewrite <- map_map. rewrite flat_map_concat_map in H.
    rewrite <- Unique.uniqueness_app_rewrite in H. destruct H...
  + apply IHl. rewrite <- Unique.uniqueness_app_rewrite in H. destruct H.
    destruct H1...
- apply IHl. rewrite <- Unique.uniqueness_app_rewrite in H. destruct H. destruct H1...
Qed.


Lemma new_match_names_unique' : forall p tn (ct : collect_tuple),
  (snd (proj1_sig ct)) (new_fun_bods p tn)
    (new_cfun_bods_g p tn ++ new_cfun_bods_l p tn)
    (new_gfun_bods_g p tn ++ new_gfun_bods_l p tn).
Proof with eauto.
intros.
pose proof (new_match_names_unique_cbods_g_gbods_g p tn ct (cfun_lm_unique_1 p ct) (cfun_lm_unique_2 p ct)) as Uniq1.
pose proof (new_match_names_unique_cbods_g_gbods_l p tn ct (cfun_lm_unique_1 p ct) (cfun_lm_unique_2_1 p ct)) as Uniq2.
pose proof (new_match_names_unique_cbods_l_gbods_g p tn ct (cfun_lm_unique_1_g p ct) (cfun_lm_unique_2_g p ct)) as Uniq3.
pose proof (new_match_names_unique_cbods_l_gbods_l p tn ct (cfun_lm_unique_1_g p ct) (cfun_lm_unique_2_1_g p ct)) as Uniq4.
rewrite (proj1 (proj2 (proj2_sig ct))) in *.
rewrite <- flat_map_concat_map. do 2 rewrite flat_map_app.
rewrite <- flat_map_concat_map with (l:=new_cfun_bods_g _ _ ++ _). rewrite flat_map_app.
rewrite map_app with (l:=flat_map _ _). rewrite flat_map_app.
rewrite <- app_assoc.

match goal with [|- _ (?l1 ++ ?l2 ++ ?l3 ++ ?l4)] =>
  replace (l1 ++ l2 ++ l3 ++ l4) with (l1 ++ (l2 ++ l3) ++ l4)
end.
2:{ repeat (rewrite <- app_assoc)...  }
apply Unique.unique_app_switch.
rewrite app_assoc.

apply Unique.uniqueness_piecewise.
- rewrite <- flat_map_concat_map. rewrite flat_map_app. rewrite map_app. rewrite flat_map_app.
  rewrite <- app_assoc. apply Unique.unique_app_switch. rewrite app_assoc.
  apply Unique.uniqueness_piecewise.
  + rewrite <- app_assoc. do 2 rewrite <- flat_map_app.
    repeat rewrite flat_map_concat_map...
  + apply new_gfun_bods_unique.
  + rewrite <- app_assoc. do 2 rewrite <- flat_map_app.
    repeat rewrite flat_map_concat_map...
- apply new_cfun_bods_unique.
- rewrite <- flat_map_concat_map. rewrite flat_map_app. rewrite map_app. rewrite flat_map_app.
  rewrite <- app_assoc. apply Unique.unique_app_switch. rewrite app_assoc.
  apply Unique.uniqueness_piecewise.
  + rewrite <- app_assoc. do 2 rewrite <- flat_map_app.
    repeat rewrite flat_map_concat_map...
  + apply new_gfun_bods_unique.
  + rewrite <- app_assoc. do 2 rewrite <- flat_map_app.
    repeat rewrite flat_map_concat_map...
Qed.


Lemma new_match_names_unique : forall p tn,
  match_names_unique (new_fun_bods p tn)
    (new_cfun_bods_g p tn ++ new_cfun_bods_l p tn)
    (new_gfun_bods_g p tn ++ new_gfun_bods_l p tn).
Proof with eauto.
intros.
assert (
     (forall p : program,
       match_names_unique (program_fun_bods p)
         (program_cfun_bods_g p ++ program_cfun_bods_l p)
         (program_gfun_bods_g p ++ program_gfun_bods_l p))
  /\ (forall f c g, match_names_unique f c g = Unique.unique
       (concat
          (map collect_match_names
            (map snd f ++
             map snd (concat (map snd c)) ++
             map snd (concat (map snd g))))))
  /\ (forall tn e, collect_match_names (refunctionalize_expr tn e) = collect_match_names e)
  /\ (forall p sn n tn e, collect_match_names (switch_indices_aux p sn n tn e) = collect_match_names e)).
{ repeat try split.
  - intros. apply program_match_names_unique.
  - intros. apply refunctionalize_expr_no_effect_on_matches.
  - intros. apply switch_indices_aux_no_effect_on_matches.
}
pose proof (new_match_names_unique' p tn (exist _ (collect_match_names, match_names_unique) H))...
Qed.



Lemma refunctionalize_expr_no_effect_on_comatches : forall tn e,
  collect_comatch_names (refunctionalize_expr tn e) = collect_comatch_names e.
Proof with eauto.
intros. induction e using expr_strong_ind; simpl; eauto;
  try (try (rewrite IHe; f_equal);
    induction ls; eauto; simpl; inversion H; subst; rewrite IHls; eauto; rewrite H2)...
- case_eq (eq_TypeName tn (fst (unscope n))); intros; simpl;
    induction ls; eauto; inversion H; subst; simpl; rewrite IHls; eauto; rewrite H3...
- case_eq (eq_TypeName tn (fst (unscope sn))); intros; simpl;
    rewrite IHe; f_equal; induction ls; eauto; simpl; inversion H; subst; rewrite IHls; eauto; rewrite H3...
- rewrite IHe. do 2 f_equal. repeat rewrite concat_app. f_equal.
  + induction es... simpl in *. inversion H0; subst. destruct a. simpl. rewrite H3. f_equal. apply IHes...
  + induction ls... simpl in *. inversion H; subst. destruct a. simpl. rewrite H3. f_equal. apply IHls...
- repeat rewrite concat_app. do 2 f_equal.
  + induction es... simpl. inversion H0; subst. destruct a. simpl. rewrite H3. f_equal. apply IHes...
  + induction ls... simpl. inversion H; subst. destruct a. simpl. rewrite H3. f_equal. apply IHls...
- f_equal...
Qed.

Lemma switch_indices_aux_no_effect_on_comatches : forall p sn n tn e,
  collect_comatch_names (switch_indices_aux p sn n tn e) = collect_comatch_names e.
Proof with eauto.
intros. unfold switch_indices_aux. rewrite refunctionalize_expr_no_effect_on_comatches.
unfold switch_indices_cfun. destruct (lookup_cfun_sig_scoped p sn)... cbn.
generalize 0.
induction e using expr_strong_ind; intro n'; simpl in *;
  try solve [induction ls; eauto; inversion H; subst; simpl; f_equal; eauto];
  try solve [f_equal; eauto; induction ls; eauto; inversion H; subst; simpl; f_equal; eauto].
- case_eq (v <? n')... intros. case_eq (v <? n' + n)...
- f_equal... repeat rewrite concat_app. f_equal.
  induction es... simpl. inversion H0; subst. f_equal...
- f_equal... repeat rewrite concat_app. f_equal.
  induction es... simpl. inversion H0; subst. f_equal...
Qed.

Lemma new_comatch_names_unique : forall p tn,
  comatch_names_unique (new_fun_bods p tn)
    (new_cfun_bods_g p tn ++ new_cfun_bods_l p tn)
    (new_gfun_bods_g p tn ++ new_gfun_bods_l p tn).
Proof with eauto.
intros.
assert (
     (forall p : program,
       comatch_names_unique (program_fun_bods p)
         (program_cfun_bods_g p ++ program_cfun_bods_l p)
         (program_gfun_bods_g p ++ program_gfun_bods_l p))
  /\ (forall f c g, comatch_names_unique f c g = Unique.unique
       (concat
          (map collect_comatch_names
            (map snd f ++
             map snd (concat (map snd c)) ++
             map snd (concat (map snd g))))))
  /\ (forall tn e, collect_comatch_names (refunctionalize_expr tn e) = collect_comatch_names e)
  /\ (forall p sn n tn e, collect_comatch_names (switch_indices_aux p sn n tn e) = collect_comatch_names e)).
{ repeat try split.
  - intros. apply program_comatch_names_unique.
  - intros. apply refunctionalize_expr_no_effect_on_comatches.
  - intros. apply switch_indices_aux_no_effect_on_comatches.
}
pose proof (new_match_names_unique' p tn (exist _ (collect_comatch_names, comatch_names_unique) H))...
Qed.


(**************************************************************************************************)
(** ** Patch together the new program from the new components and proofs                          *)
(**************************************************************************************************)

Definition refunctionalize_program (p : program) (tn : TypeName)
  (NoMFun : Forall (no_matches tn) (map snd (program_fun_bods p)))
  (NoMCfunG : Forall (no_matches tn) (map snd (flat_map snd (program_cfun_bods_g p))))
  (NoMCfunL : Forall (no_matches tn) (map snd (flat_map snd (program_cfun_bods_l p))))
  (NoMGfunG : Forall (no_matches tn) (map snd (flat_map snd (program_gfun_bods_g p))))
  (NoMGfunL : Forall (no_matches tn) (map snd (flat_map snd (program_gfun_bods_l p))))
 : program :=
{|
  (* Skeleton *)
  program_skeleton := refunctionalize_to_skeleton p tn;
  (* Ordinary functions *)
  program_fun_bods := new_fun_bods p tn;
  program_has_all_fun_bods := new_has_all_funbods p tn;
  program_fun_bods_typecheck := new_funbods_typecheck p tn NoMFun;
  (* Consumer functions *)
  program_cfun_bods_g := new_cfun_bods_g p tn;
  program_has_all_cfun_bods_g := new_has_all_cfunbods_g p tn;
  program_cfun_bods_typecheck_g := new_cfunbods_g_typecheck p tn NoMCfunG;
  program_cfun_bods_l := new_cfun_bods_l p tn;
  program_has_all_cfun_bods_l := new_has_all_cfunbods_l p tn;
  program_cfun_bods_typecheck_l := new_cfunbods_l_typecheck p tn NoMCfunL;
  (* Generator functions *)
  program_gfun_bods_g := new_gfun_bods_g p tn;
  program_has_all_gfun_bods_g := new_has_all_gfunbods_g p tn;
  program_gfun_bods_typecheck_g := new_gfunbods_g_typecheck p tn NoMGfunG NoMCfunL NoMCfunG;
  program_gfun_bods_l := new_gfun_bods_l p tn;
  program_has_all_gfun_bods_l := new_has_all_gfunbods_l p tn;
  program_gfun_bods_typecheck_l := new_gfunbods_l_typecheck p tn NoMGfunL NoMCfunL NoMCfunG;
  (* Uniqueness conditions *)
  program_match_names_unique := new_match_names_unique p tn;
  program_comatch_names_unique := new_comatch_names_unique p tn;
|}.

