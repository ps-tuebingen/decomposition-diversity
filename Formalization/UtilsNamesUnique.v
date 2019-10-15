(* Standard library imports *)
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Import ListNotations.
(* Project related imports *)
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

Definition unordered_eq {A} (l1 l2 : list A) : Prop :=
  (forall a, In a l1 <-> In a l2) /\ length l1 = length l2.

Fact unordered_eq_symm : forall {A} (l l' : list A),
  unordered_eq l l' -> unordered_eq l' l.
Proof with eauto.
intros. unfold unordered_eq in *. destruct H. split... intros. apply iff_sym...
Qed.

Fact skipn_app_part : forall {A} n (x y : list A),
  n < length x ->
  exists z a, skipn n (x ++ y) = (a::z) ++ y.
Proof with eauto.
intros. generalize dependent n. generalize dependent y.
induction x; intros; simpl in H; try omega.
simpl. destruct n; simpl; [exists x; exists a|]...
apply IHx. omega.
Qed.

Lemma unique_filter_delete_length : forall {A} (a0 a : A) l1
  (Dec : Names.decidable A),
  Unique.unique (a0 :: l1) ->
  In a (a0 :: l1) ->
  length (filter (fun x : A => if Dec a x then false else true) (a0 :: l1)) = length l1.
Proof with eauto.
intros. apply in_split in H0. do 2 destruct H0. rewrite H0. rewrite H0 in H.
rewrite filter_app. simpl. destruct (Dec a a); [|exfalso; apply n]...
apply (f_equal (@length _)) in H0. simpl in H0. rewrite app_length in H0. simpl in H0.
replace (length l1) with (length x0 + length x); try omega.
rewrite app_length. rewrite plus_comm. rewrite <- app_length. rewrite <- filter_app.
rewrite <- app_length.
rewrite <- app_nil_l in H. apply Unique.unique_app_switch in H. inversion H; subst.
generalize H3. generalize (x0++x). clear. induction l; intros... case_eq (Dec a a0); intros; subst.
- exfalso. apply H3. left...
- simpl. rewrite H. simpl. rewrite IHl... unfold not. intros. apply H3. right...
Qed.

Lemma unique_unordered : forall {A} (l1 l2 : list A),
  Names.decidable A -> unordered_eq l1 l2 -> Unique.unique l1 -> Unique.unique l2.
Proof with eauto.
intros A l1 l2 Dec H H0. assert (exists y, y ++ l2 = l2). { exists []... }
generalize dependent l2. intro l2. generalize l2 at 2.
assert ((forall l0, (exists y, y ++ l0 = l2) -> Unique.unique l0) -> Unique.unique l2).
{ intros. apply H. exists []... }
intros. apply H. clear - H0 H1 Dec.
induction l0; intros; constructor.
2:{ apply IHl0. destruct H as [y H]. exists (y++[a]). rewrite <- app_assoc... }
assert ((forall a', In a' l0 -> a' <> a) -> ~In a l0).
{ intros. unfold not in *. intros. apply H2 with (a':=a)... }
apply H2. intros.
assert (In a' l2).
{ destruct H as [y H]. rewrite <- H. apply in_or_app. right. right... }
unfold unordered_eq in H1. pose proof (proj2 (proj1 H1 a') H4).
assert (In a l2).
{ destruct H as [y H]. rewrite <- H. apply in_or_app. right. left... }
pose proof (proj2 (proj1 H1 a) H6).
rename H into Core. rename H3 into Core'. rename H1 into Core2.
clear - H0 H5 H7 Core Core' Core2 Dec.
apply in_split in H5. apply in_split in H7. destruct H5 as [x [y H]]. destruct H7 as [x' [y' H']].
subst.
case_eq (length x <? length x'); intros.
- apply (f_equal (skipn (length x))) in H'.
  rewrite skipn_all_app in H'.
  rewrite Nat.ltb_lt in H.
  destruct (skipn_app_part (length x) x' (a::y') H).
  destruct H1. rewrite H1 in H'. simpl in H'.
  inversion H'; subst. rewrite <- app_nil_l in H0.
  apply Unique.unique_app_switch in H0. simpl in H0.
  inversion H0; subst. unfold not in *. intros. apply H4. subst.
  apply in_or_app. left. apply in_or_app. right. left...
- case_eq (length x =? length x'); intros.
  + exfalso. apply (f_equal (firstn (length x + 1))) in H'.
    rewrite Nat.eqb_eq in H1.
    rewrite H1 in H' at 2. repeat (rewrite firstn_app_2 in H').
    simpl in H'. apply (f_equal (@rev _)) in H'.
    repeat (rewrite rev_unit in H'). inversion H'; subst.
    apply in_split in Core'. destruct Core'. destruct H2. subst l0.
    destruct Core as [z Core]. subst l2. clear - H0 Core2 Dec.
    destruct Core2.
    assert (length (x ++ a :: y) < length (z ++ a :: x0 ++ a :: x1)).
    { clear H1. repeat (rewrite app_length; simpl). do 2 rewrite <- plus_n_Sm.
      apply lt_n_S. unfold lt. do 2 rewrite <- plus_n_Sm. apply le_n_S.
      assert (forall a0, In a0 (x++y) -> In a0 (z++x0++x1)).
      { intros. assert (In a0 (x++a::y)).
        { apply in_app_or in H1. apply in_or_app. destruct H1; [left|]... right. right... }
        pose proof (proj1 (H a0) H2). apply in_or_app. apply in_app_or in H3. simpl in H3.
        destruct H3; [left|]... destruct H3.
        - subst. exfalso. rewrite <- app_nil_l in H0. apply Unique.unique_app_switch in H0.
          inversion H0; subst. apply H5. apply in_or_app. apply in_app_or in H1. destruct H1; [right|left]...
        - apply in_app_or in H3. simpl in H3. right. apply in_or_app. destruct H3; try destruct H3; [left| |]...
          subst. exfalso. rewrite <- app_nil_l in H0. apply Unique.unique_app_switch in H0.
          inversion H0; subst. apply H5. apply in_or_app. apply in_app_or in H1. destruct H1; [right|left]...
      }
      rewrite <- app_nil_l in H0. apply Unique.unique_app_switch in H0. inversion H0; subst.
      rewrite <- app_nil_l in H5. apply Unique.unique_app_switch in H5. simpl in H5.
      clear - H1 H5 Dec. repeat (rewrite <- app_length). generalize H1 H5. clear - Dec.
      generalize (x++y). generalize (z++x0++x1). clear - Dec.

      intros. case_eq (length l0 <=? length l); intros; [apply Nat.leb_le|]...
      exfalso. rewrite Nat.leb_gt in H. assert (exists a, ~In a l /\ In a l0).
      { clear H1. generalize dependent l0. induction l; intros.
        - destruct l0; [simpl in H; omega|]. exists a. split... left...
        - set (l0':=filter (fun x => if Dec a x then false else true) l0).
          assert (length l < length l0').
          { assert (length l0 - 1 <= length l0').
            { clear - H5. replace 1 with (1 + (length l0 - length l0)); try omega.
              unfold l0'. generalize H5. clear. assert (length l0 <= length l0)...
              generalize H. clear H. generalize l0 at - 2 4 5.
              induction l1; intros; [simpl;omega|].
              case_eq (in_dec Dec a (a0::l1)); intros.
              - assert (length (filter (fun x : A => if Dec a x then false else true) (a0 :: l1)) = length l1).
                { clear - H5 i. apply unique_filter_delete_length... }
                rewrite H1. simpl. omega.
              - assert (filter (fun x : A => if Dec a x then false else true) (a0 :: l1) = a0::l1).
                { clear - n. generalize n. generalize (a0::l1). clear. intros.
                  induction l... case_eq (Dec a a0); intros; subst.
                  - exfalso. apply n. left...
                  - simpl. rewrite H. rewrite IHl... unfold not. intros. apply n. right...
                }
                rewrite H1. simpl. omega.
            }
            simpl in H. omega.
          }
          assert (Unique.unique l0') as Uniq.
          { unfold l0'. apply Unique.filter_unique... }
          destruct (IHl l0' Uniq H0) as [a0 [a0Spec1 a0Spec2]]. exists a0. split.
          + unfold not. intros. destruct H1.
            * subst. unfold l0' in *. rewrite filter_In in a0Spec2. destruct a0Spec2.
              destruct (Dec a0 a0)... discriminate.
            * apply a0Spec1...
          + unfold l0' in *. rewrite filter_In in a0Spec2. destruct a0Spec2...
      }
      do 2 destruct H0. apply H0. apply H1 in H2...
    }
    omega.
  + rewrite <- firstn_skipn with (n:=length x') in H0.
    rewrite Nat.ltb_ge in H. rewrite Nat.eqb_neq in H1.
    assert (length x' < length x); try omega.
    apply (f_equal (skipn (length x'))) in H'.
    rewrite skipn_all_app in H'.
    destruct (skipn_app_part (length x') x (a'::y) H2).
    destruct H3. rewrite H3 in H'. simpl in H'. rewrite H3 in H0.
    inversion H'; subst. rewrite <- app_nil_l in H0.
    apply Unique.unique_app_switch in H0. simpl in H0.
    inversion H0; subst. unfold not in *. intros. apply H6. subst.
    apply in_or_app. left. apply in_or_app. right. left...
Qed.

Fact length_concat : forall {A} (l : list (list A)), length (concat l) = fold_left Nat.add (map (@length A) l) 0.
Proof with eauto.
intros. replace (length (concat l)) with (length (concat l) + 0)... generalize 0. induction l; intros...
simpl. rewrite app_length. rewrite plus_comm. rewrite plus_assoc. rewrite plus_comm. apply IHl.
Qed.

Lemma ScopedName_dec: decidable ScopedName.
Proof.
  unfold decidable; intros.
  destruct (eq_ScopedName x y) eqn:E.
  - name_eq_tac; auto.
  - right; intro; subst; name_refl_contradiction_tac.
Qed.

Lemma gfun_bods_type_names : forall p a x1 q,
  In x1 (snd a) ->
  In a (program_gfun_bods_g p) ->
  fst x1 = global q ->
  fst q = fst (fst a).
Proof with eauto.
intros. pose proof (program_gfun_bods_typecheck_g p) as Typ.
unfold gfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
apply Typ in H0. clear Typ. destruct H0 as [qn [args [SigLookup Typ]]].
inversion Typ; subst. pose proof (listTypeDeriv'_lemma _ _ _ _ H10) as Len.
clear - Len H H1 H8 H9. unfold lookup_dtors in H8. unfold QName in *.
case_eq (filter (eq_TypeName (fst (fst a))) (skeleton_cdts (program_skeleton p))); intros;
  rewrite H0 in H8; try discriminate.
inversion H8; subst. clear H8 H0. do 2 rewrite map_length in Len.
rewrite Nat.eqb_eq in Len. symmetry in Len. pose proof (combine_in H Len) as H'.
destruct H' as [y H']. apply in_combine_switch in H'...
rewrite Forall_forall in H9. assert (fst (unscope (fst (fst y))) = fst (fst a)) as Eq.
{ apply in_combine_r in H'. rewrite filter_In in H'. destruct H'. destruct y. destruct p0.
  simpl in *. apply eq_TypeName_eq...
}
apply H9 in H'. destruct x1. destruct y. destruct p0. subst. simpl in *. subst...
Qed.

Lemma gfun_bods_l_type_names : forall p a x1 q,
  In x1 (snd a) ->
  In a (program_gfun_bods_l p) ->
  fst x1 = global q ->
  fst q = fst (fst a).
Proof with eauto.
intros. pose proof (program_gfun_bods_typecheck_l p) as Typ.
unfold gfun_bods_l_typecheck in Typ. rewrite Forall_forall in Typ.
apply Typ in H0. clear Typ. destruct H0 as [qn [args [SigLookup Typ]]].
inversion Typ; subst. pose proof (listTypeDeriv'_lemma _ _ _ _ H10) as Len.
clear - Len H H1 H8 H9. unfold lookup_dtors in H8. unfold QName in *.
case_eq (filter (eq_TypeName (fst (fst a))) (skeleton_cdts (program_skeleton p))); intros;
  rewrite H0 in H8; try discriminate.
inversion H8; subst. clear H8 H0. do 2 rewrite map_length in Len.
rewrite Nat.eqb_eq in Len. symmetry in Len. pose proof (combine_in H Len) as H'.
destruct H' as [y H']. apply in_combine_switch in H'...
rewrite Forall_forall in H9. assert (fst (unscope (fst (fst y))) = fst (fst a)) as Eq.
{ apply in_combine_r in H'. rewrite filter_In in H'. destruct H'. destruct y. destruct p0.
  simpl in *. apply eq_TypeName_eq...
}
apply H9 in H'. destruct x1. destruct y. destruct p0. subst. simpl in *. subst...
Qed.

Lemma gfun_bods_type_names_l : forall p a x1 q,
  In x1 (snd a) ->
  In a (program_gfun_bods_g p) ->
  fst x1 = local q ->
  fst q = fst (fst a).
Proof with eauto.
intros. pose proof (program_gfun_bods_typecheck_g p) as Typ.
unfold gfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
apply Typ in H0. clear Typ. destruct H0 as [qn [args [SigLookup Typ]]].
inversion Typ; subst. pose proof (listTypeDeriv'_lemma _ _ _ _ H10) as Len.
clear - Len H H1 H8 H9. unfold lookup_dtors in H8. unfold QName in *.
case_eq (filter (eq_TypeName (fst (fst a))) (skeleton_cdts (program_skeleton p))); intros;
  rewrite H0 in H8; try discriminate.
inversion H8; subst. clear H8 H0. do 2 rewrite map_length in Len.
rewrite Nat.eqb_eq in Len. symmetry in Len. pose proof (combine_in H Len) as H'.
destruct H' as [y H']. apply in_combine_switch in H'...
rewrite Forall_forall in H9. assert (fst (unscope (fst (fst y))) = fst (fst a)) as Eq.
{ apply in_combine_r in H'. rewrite filter_In in H'. destruct H'. destruct y. destruct p0.
  simpl in *. apply eq_TypeName_eq...
}
apply H9 in H'. destruct x1. destruct y. destruct p0. subst. simpl in *. subst...
Qed.

Lemma cfun_bods_type_names : forall p a x1 q,
  In x1 (snd a) ->
  In a (program_cfun_bods_g p) ->
  fst x1 = global q ->
  fst q = fst (fst a).
Proof with eauto.
intros. pose proof (program_cfun_bods_typecheck_g p) as Typ.
unfold cfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
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

Lemma cfun_bods_l_type_names : forall p a x1 q,
  In x1 (snd a) ->
  In a (program_cfun_bods_l p) ->
  fst x1 = global q ->
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

Lemma cfun_bods_type_names_l : forall p a x1 q,
  In x1 (snd a) ->
  In a (program_cfun_bods_g p) ->
  fst x1 = local q ->
  fst q = fst (fst a).
Proof with eauto.
intros. pose proof (program_cfun_bods_typecheck_g p) as Typ.
unfold cfun_bods_g_typecheck in Typ. rewrite Forall_forall in Typ.
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
