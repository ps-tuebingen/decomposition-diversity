Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Sorting.Permutation.

Require Import GenericTactics.
Require Import GenericLemmas.
Require Import Unique.
Require Import Sublist.

Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (la : list A) (lb : list B) {struct la} : list C :=
  match la, lb with
  | [], _ => []
  | _, [] => []
  | (a::la'), (b::lb') => (f a b) :: zipWith f la' lb'
  end.

Fixpoint sort_by_index_list {A B : Type} (f : A -> B -> bool) (index : list A) (to_sort : list B) : list B :=
  match index with
  | [] => []
  | (i::is) =>
    filter (f i) to_sort ++ sort_by_index_list f is (filter (fun x => negb (f i x)) to_sort)
  end.


Lemma sort_by_index_list_empty: forall {A B : Type} (f : A -> B -> bool) (index : list A),
    sort_by_index_list f index [] = [].
Proof.
  intros A B f index.
  induction index; auto.
Qed.

Lemma sort_by_index_list_filter_false: forall {A B : Type} (f : A -> B -> bool) (p : B -> bool) (index : list A) (to_sort : list B) (b : B),
    p b = false ->
    filter p (sort_by_index_list f index (b :: to_sort)) = filter p (sort_by_index_list f index to_sort).
Proof.
  intros A B f p index to_sort b H.
  gen_induction to_sort index; simpl; auto.
  match_destruct_tac; simpl; try rewrite H; auto.
  repeat rewrite filter_app; f_equal; auto.
Qed.

Lemma sort_by_index_list_filter: forall {A B : Type} (f : A -> B -> bool) (p : B -> bool) (index : list A) (to_sort : list B),
    sort_by_index_list f index (filter p to_sort) = filter p (sort_by_index_list f index to_sort).
Proof.
  intros A B f p index to_sort.
  gen_induction to_sort index; destruct to_sort; simpl; auto.
  - rewrite sort_by_index_list_empty; auto.
  - rewrite filter_app. f_equal.
    + do 2 match_destruct_tac; simpl; try rewrite E_match in *; try rewrite E_match0 in *; try rewrite filter_filter; auto.
    + do 2 match_destruct_tac; simpl;
        try rewrite E_match in *; try rewrite E_match0 in *; simpl; rewrite filter_filter; auto.
      * match goal with
        | [  |- _ = filter _ (_ _ _ ?ls) ] =>
          specialize (IHindex ls)
        end.
        simpl in IHindex; rewrite E_match in IHindex; auto.
      * rewrite sort_by_index_list_filter_false; auto.
Qed.

Lemma permutation_filter_div: forall {A : Type} (p : A -> bool) (l : list A),
    Permutation l (filter p l ++ filter (fun x => negb (p x)) l).
Proof.
  intros A p l.
  induction l; simpl; auto.
  match_destruct_tac; simpl.
  - apply perm_skip; auto.
  - apply Permutation_cons_app; auto.
Qed.

Lemma permutation_filter: forall {A : Type} (p : A -> bool) (l r : list A),
    Permutation l r ->
    Permutation (filter p l) (filter p r).
Proof.
  intros A p l r H.
  induction H; auto; simpl in *.
  - match_destruct_tac; auto.
  - do 2 match_destruct_tac; auto. apply perm_swap.
  - eapply perm_trans; eauto.
Qed.

Lemma Permutation_Forall: forall {A : Type} (P : A -> Prop) (ls ls' : list A),
    Permutation ls ls' ->
    Forall P ls ->
    Forall P ls'.
Proof.
  intros A P ls ls' H H0.
  induction H; auto.
  - inversion_clear H0; apply Forall_cons; auto.
  - repeat match goal with
           | [ H: Forall _ (_ :: _) |- _ ] =>
             inversion_clear H
           end;
      repeat apply Forall_cons; auto.
Qed.

Lemma Permutation_concat: forall {A : Type} (l r : list (list A)),
    Permutation l r ->
    Permutation (concat l) (concat r).
Proof.
  intros A l r H.
  induction H; auto; simpl in *.
  - apply Permutation_app; auto.
  - match goal with
    | [  |- Permutation (?x ++ ?y ++ ?z) (?x' ++ ?y' ++ ?z') ] => 
      reassoc_lists (x ++ y ++ z) ((x ++ y) ++ z);
        reassoc_lists (x' ++ y' ++ z') ((x' ++ y') ++ z')
    end.
    apply Permutation_app; auto.
    apply Permutation_app_comm.
  - eapply perm_trans; eauto.
Qed.

Lemma Permutation_sublist: forall {A : Type} (l r sub : list A),
    Permutation l r ->
    sublist sub r ->
    exists sub_l, Permutation sub_l sub /\ sublist sub_l l.
Proof.
  intros A l r sub H_per H_sub.
  gen_induction sub H_per; auto.
  - inversion H_sub; subst; eauto.
  - inversion H_sub; subst; eauto.
    + exists []; split; auto. apply sublist_nil.
    + specialize (IHH_per sub H1).
      inversion IHH_per. inversion H.
      exists x0; split; auto.
      apply sublist_skip; auto.
    + specialize (IHH_per _ H1).
      inversion IHH_per. inversion H.
      exists (x :: x0); split; auto.
      sublist_tac.
  - inversion H_sub; subst; try solve [exists []; split; auto; sublist_tac].
    + inversion H1; subst; try solve [exists []; split; auto; sublist_tac].
      * exists sub; split; auto. do 2 apply sublist_skip; assumption.
      * exists (y :: sub0); split; auto. apply sublist_cons; apply sublist_skip; assumption.
    + inversion H1; subst.
      * exists [x]; split; auto. apply sublist_skip; apply sublist_cons; sublist_tac.
      * exists (x :: sub0); split; auto. apply sublist_skip; apply sublist_cons; auto.
      * exists (y :: x :: sub); split; auto; try apply perm_swap.
        do 2 apply sublist_cons; auto.
  - specialize (IHH_per2 _ H_sub).
    inversion IHH_per2 as [sub_l1 [H_perm1 H_sub1]].
    specialize (IHH_per1 _ H_sub1).
    inversion IHH_per1 as [sub_l2 [H_perm2 H_sub2]].
    exists sub_l2; split; auto.
    apply (Permutation_trans H_perm2 H_perm1).
Qed.
Lemma Permutation_middle_rem: forall {A : Type} (l r : list A) (a : A),
    Permutation (a :: l) r ->
    exists r1 r2, r = r1 ++ a :: r2 /\ Permutation l (r1 ++ r2).
Proof.
  intros A l r a H_per.
  assert (In a r);
    [ eapply Permutation_in; eauto; left; auto |].
  apply in_split in H; double_exists H.
  split; auto.
  apply Permutation_cons_inv with (a := a).
  eapply (perm_trans H_per _).
  Unshelve. subst.
  apply Permutation_sym.
  apply Permutation_middle.
Qed.

Lemma Permutation_unique: forall {A : Type} (l r : list A),
    Permutation l r ->
    unique l ->
    unique r.
Proof.
  intros A l r H_per H_uniq.
  induction H_per; auto.
  - inversion_clear H_uniq.
    apply Unique_cons; auto.
    intro H_in; apply H.
    apply Permutation_in with (l := l'); auto.
    apply Permutation_sym; assumption.
  - repeat apply Unique_cons;
      repeat match goal with
             | [ H: unique (_ :: _) |- _ ] =>
               inversion_clear H
             end;
      auto.
    + intro H_in; inversion_clear H_in; subst.
      * apply H; left; auto.
      * apply H1; auto.
    + intro H_in; apply H; right; auto.
Qed.

Lemma sort_by_index_list_permutes_helper:forall {A B : Type} (f : A -> B -> bool) (index sub : list A) (to_sort : list B) (g : B -> A),
    sublist sub index ->
    Permutation sub (map g to_sort) ->
    (forall a b, a = g b <-> f a b = true) ->
    Permutation to_sort (sort_by_index_list f index to_sort).
Proof.
  intros A B f index sub to_sort g H_sub H_per E.
  gen_induction (sub, to_sort) index; simpl in *.
  - inversion H_sub; subst. apply Permutation_nil in H_per.
    apply map_eq_nil in H_per; subst; auto.
  - inversion H_sub; subst; simpl in *.
    + apply Permutation_nil in H_per. apply map_eq_nil in H_per; subst; simpl.
      clear; induction index; auto; simpl.
    + apply (perm_trans (permutation_filter_div (f a) to_sort)).
      apply Permutation_app; auto.
      match goal with
      | [ H: Permutation ?sub (map ?g ?ls) |- Permutation (filter ?p ?ls) _ ] => 
        let H_f := fresh in
        pose proof (sublist_filter p ls) as H_f;
          apply (sublist_map _ _ g) in H_f;
          eapply (Permutation_sublist _ _ _ H_per) in H_f;
          inversion H_f as [sub_l [Hl Hr]]
      end.
      eapply IHindex; [| eauto].
      apply (sublist_trans _ _ _ Hr H1).
    + apply (perm_trans (permutation_filter_div (f a) to_sort)).
      apply Permutation_app; auto.
      apply Permutation_middle_rem in H_per.
      repeat match goal with
             | [ H: exists _,_ |- _ ] =>
               inversion_clear H
             | [ H: _ /\ _ |- _ ] =>
               inversion_clear H
             end.
      apply map_app2 in H.
      repeat match goal with
             | [ H: exists _,_ |- _ ] =>
               inversion_clear H
             | [ H: _ /\ _ |- _ ] =>
               inversion_clear H
             end.
      subst.
      destruct x2; inversion H; subst.
      rewrite filter_elem_false; [ | rewrite Bool.negb_false_iff; apply E; reflexivity].
      pose proof (sublist_filter (fun x => negb (f (g b) x)) (x1 ++ x2)) as H_sub_filter.
      apply (sublist_map _ _ g) in H_sub_filter.
      rewrite <- map_app in H2.
      pose proof (Permutation_sublist _ _ _ H2 H_sub_filter).
      repeat match goal with
             | [ H: exists _,_ |- _ ] =>
               inversion_clear H
             | [ H: _ /\ _ |- _ ] =>
               inversion_clear H
             end.
      eapply IHindex.
      * eapply sublist_trans; [eapply H4 | eauto].
      * auto.
Qed.

Lemma sort_by_index_list_permutes: forall {A B : Type} (f : A -> B -> bool) (index : list A) (to_sort : list B),
    (exists (g : B -> A), Permutation index (map g to_sort) /\
                    forall a b, a = g b <-> f a b = true) ->
    Permutation to_sort (sort_by_index_list f index to_sort).
Proof.
  intros.
  inversion_clear H as [g [H_per H_eq]].
  eapply sort_by_index_list_permutes_helper with (g0 := g).
  - eapply sublist_refl.
  - auto.
  - auto.
Qed.

Lemma sort_by_index_list_sorted_like_index:
  forall {A B : Type} (f : A -> B -> bool) (index : list A) (to_sort : list B) (g : B -> A),
    unique index ->
    Permutation index (map g to_sort) ->
    (forall (a : A) (b : B), a = g b <-> f a b = true) ->
    (map g (sort_by_index_list f index to_sort) = index).
Proof.
  intros A B f index to_sort g H_uniq H_per E.
  pose proof (Permutation_unique _ _ H_per H_uniq) as H_uniq_to_sort.
  gen_induction to_sort index; [ inversion H_per; easy |].
  simpl.
  assert (Hx: exists b, In b to_sort /\ g b = a).
  { apply (Permutation_in a) in H_per; [ | left; easy].
    clear - H_per. induction to_sort; simpl in *; inversion H_per; subst.
    - exists a0; split; auto.
    - specialize (IHto_sort H).
      inversion IHto_sort as (b & H_in & E).
      exists b; split; auto.
  }
  inversion_clear Hx as (b & H_in_b & E_g).
  assert (E_in: forall bx, In bx to_sort -> f a bx = true <-> b = bx).
  { clear IHindex H_uniq H_per; intros bx H_in.
    induction to_sort; inversion H_in; inversion H_in_b; subst.
    - split; intro; auto.
      rewrite <- E; easy.
    - symmetry. split; intro; subst.
      + rewrite <- E; easy.
      + rewrite <- E in H.
        apply (in_map g) in H0.
        inversion H_uniq_to_sort; subst.
        rewrite H in *. contradiction.
    - split; intro; subst.
      + rewrite <- E in H0.
        apply (in_map g) in H.
        inversion H_uniq_to_sort; subst.
        rewrite H0 in *.
        contradiction.
      + rewrite <- E; easy.
    - inversion H_uniq_to_sort; auto.
  }
  assert (E_b: filter (f a) to_sort = [b]).
  { clear - E E_g H_in_b E_in H_uniq_to_sort.
    induction to_sort; inversion H_in_b; subst; simpl.
    - rewrite (proj1 (E (g b) b)); [ |easy].
      f_equal.
      inversion_clear H_uniq_to_sort.
      assert (Forall (fun bx => f (g b) bx = false) to_sort).
      { clear IHto_sort H_in_b.
        induction to_sort as [|bx to_sort]; auto.
        apply Forall_cons.
        - simpl map in H; rewrite not_in_cons in H. inversion H.
          rewrite <- Bool.not_true_iff_false.
          contradict H1.
          rewrite <- E in H1; easy.
        - inversion_clear H0. apply IHto_sort; auto.
          + intros; apply E_in.
            inversion H0; subst; [ left | right; right ]; easy.
          + contradict H. right; easy.
      }
      apply Forall_false_filter_nil; easy.
    - inversion_clear H_uniq_to_sort.
      match_destruct_tac.
      + rewrite <- E in E_match; subst.
        contradict H0.
        apply (in_map g) in H; rewrite <- E_match; easy.
      + apply IHto_sort; auto.
        intros; apply E_in; auto.
        right; easy.
  }
  rewrite E_b in *; rewrite map_app; simpl.
  f_equal; auto.
  inversion_clear H_uniq.
  apply IHindex; auto;
    [ |  apply (uniqueness_sublist _ (map g to_sort)); auto; sublist_tac ].
  pose proof (permutation_filter_div (f a) to_sort).
  apply (Permutation_map g) in H1.
  pose proof (perm_trans H_per H1).
  rewrite E_b in H2; simpl in H2.
  rewrite E_g in H2.
  apply Permutation_cons_inv in H2; easy.
Qed.

