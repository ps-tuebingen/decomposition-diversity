(**************************************************************************************************)
(* Total Constructor/Destructorization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: Sublist.v                                                                                 *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import GenericTactics.
Require Import GenericLemmas.


Inductive sublist {A : Type} : list A -> list A -> Prop :=
| sublist_nil: forall (ls : list A), sublist [] ls
| sublist_skip: forall (sub tot: list A) (a : A),
    sublist sub tot ->
    sublist sub (a :: tot)
| sublist_cons: forall (sub tot: list A) (a : A),
    sublist sub tot ->
    sublist (a :: sub) (a :: tot).

Lemma In_sublist: forall {A : Type} (sub tot : list A) (a : A),
    sublist sub tot ->
    In a sub ->
    In a tot.
Proof.
  intros A sub tot a H H0.
  gen_induction sub tot; destruct sub; inversion H0; inversion H; subst.
  - right. apply IHtot with (sub := a :: sub); try assumption.
  - left; auto.
  - right. apply IHtot with (sub := a1 :: sub); try assumption.
  - right; IH_auto_tac.
Qed.

Lemma sublist_refl: forall {A : Type} (ls : list A),
    sublist ls ls.
Proof.
  intros A ls.
  induction ls; try apply sublist_nil.
  apply sublist_cons; assumption.
Qed.

Lemma sublist_trans: forall {A : Type} (l m r: list A),
    sublist l m ->
    sublist m r ->
    sublist l r.
Proof with try assumption; try apply sublist_nil.
  intros A l m r H H0.
  assert (Hy: forall s t (a : A), sublist s t -> sublist s (a :: t));
  [> clear; intros s t a H1; apply sublist_skip; assumption | ].
  assert (Hx: forall s t (a : A), sublist (a :: s) t -> sublist s t).
  { clear - Hy; intros s t a H1.
    gen_induction s t; inversion H1; subst...
    - apply sublist_skip. IH_auto_tac.
    - apply Hy...
  }
  gen_induction (r, m) l; try apply sublist_nil.
  gen_induction m r; destruct m; try solve [inversion H]; try solve [inversion H0].
  inversion H; subst.
  - inversion H0; subst.
    + apply Hy. IH_auto_tac.
    + apply Hy. IH_auto_tac.
  - inversion H0; subst.
    + apply Hy. specialize (IHr (a1 :: m)).
      IH_tac.
    + apply sublist_cons.
      apply IHl with (m := m)...
Qed.


Lemma sublist_app_extend_cov: forall {A : Type} (s t l r : list A),
    sublist s t ->
    sublist s (l ++ t ++ r).
Proof.
  intros A s t l r H.
  gen_induction s l.
  - gen_induction s t; simpl; destruct s as [|s s_rest]; inversion H; try apply sublist_nil.
    + apply sublist_skip. apply IHt; assumption.
    + apply sublist_cons. apply IHt; assumption.
  - apply sublist_skip; IH_auto_tac.
Qed.

Lemma sublist_app_extend_contrav: forall {A : Type} (s t l r : list A),
    sublist (l ++ s ++ r) t ->
    sublist s t.
Proof.
  intros A s t l r H.
  apply sublist_trans with (m := l ++ s ++ r); try assumption.
  apply sublist_app_extend_cov. apply sublist_refl.
Qed.

Lemma sublist_app_embed_l: forall {A : Type} (l r : list A),
    sublist l (l ++ r).
Proof.
  intros A l r.
  induction l.
  - apply sublist_nil.
  - simpl. apply sublist_cons; assumption.
Qed.

Lemma sublist_app_embed_r: forall {A : Type} (l r : list A),
    sublist r (l ++ r).
Proof.
  intros A l r.
  induction l.
  - simpl. apply sublist_refl.
  - simpl. apply sublist_skip; assumption.
Qed.

Lemma sublist_app: forall {A : Type} (l l' r r' : list A),
    sublist l r ->
    sublist l' r' ->
    sublist (l ++ l') (r ++ r').
Proof.
  intros A l l' r r' H H0.
  gen_induction l r; destruct l; inversion H; subst; try assumption; simpl; clear H.
  - apply sublist_skip. apply IHr with (l := []). apply sublist_nil.
  - apply sublist_skip. apply IHr with (l := []). apply sublist_nil.
  - apply sublist_skip. apply IHr with (l := (a0 :: l)). assumption.
  - apply sublist_cons. IH_auto_tac.
Qed.

Lemma sublist_concat': forall {A : Type} (ss ts : list (list A)),
    Forall2 (fun xs ys => sublist xs ys) ss ts ->
    sublist (concat ss) (concat ts).
Proof.
  intros A ss ts H.
  gen_induction ss ts; destruct ss; inversion H; try apply sublist_nil.
  subst; simpl. apply sublist_app; try assumption.
  IH_auto_tac.
Qed.

Lemma sublist_concat: forall {A B : Type} (ls : list A) (f g : A -> list B),
    Forall (fun x => sublist (f x) (g x)) ls ->
    sublist (concat (map f ls)) (concat (map g ls)).
Proof.
  intros A B ls f g H.
  induction ls; try apply sublist_nil.
  simpl; inversion H; subst.
  apply sublist_app; try assumption. IH_auto_tac.
Qed.

Lemma sublist_map: forall {A B : Type} (sub tot : list A) (f : A -> B),
    sublist sub tot ->
    sublist (map f sub) (map f tot).
Proof.
  intros A B sub tot f H.
  gen_induction sub tot; inversion H; simpl; try apply sublist_nil.
  - apply sublist_skip. apply IHtot; auto.
  - apply sublist_cons. apply IHtot; auto.
Qed.

Lemma sublist_singleton_In: forall {A : Type} (x : A) (ls : list A),
    In x ls <-> sublist [x] ls.
Proof.
  intros A x ls.
  split; intro; induction ls; inversion H; subst.
  - apply sublist_cons; apply sublist_nil.
  - apply sublist_skip; auto.
  - right; auto.
  - left; auto.
Qed.

Lemma sublist_filter: forall {A : Type} (p: A -> bool) (ls : list A),
    sublist (filter p ls) ls.
Proof.
  intros A p ls.
  induction ls.
  - simpl. apply sublist_nil.
  - simpl. match_destruct_tac.
    + apply sublist_cons; auto.
    + apply sublist_skip; auto.
Qed.

Ltac sublist_tac :=
  try assumption;
  try apply sublist_refl;
  try apply sublist_nil;
  try apply sublist_app_embed_l;
  try apply sublist_app_embed_r;
  try (apply sublist_map; sublist_tac);
  try (apply sublist_app_extend_cov; sublist_tac);
  try (rewrite <- app_nil_l; apply sublist_app_extend_cov; sublist_tac);
  try (rewrite <- app_nil_r; rewrite <- (app_assoc _ _ []) ; apply sublist_app_extend_cov; sublist_tac);
      (* checking for equality in match is too restrictive, e.g. alpha-equivalence *)
  match goal with
  | [  |- sublist (filter ?f ?l) ?l ] => apply sublist_filter
  | [  |- sublist (?x :: _) (?x :: _) ] => apply sublist_cons; sublist_tac
  | [  |- sublist ?sl (?x :: ?sl) ] =>
    rewrite <- app_nil_r; simpl;
    apply sublist_app_extend_cov with (l := [x]) (t := sl) (r := []); sublist_tac
  | [  |- sublist (?sl ++ ?sr) (?tl ++ ?tr) ] =>
    apply sublist_app; sublist_tac
  | [ H: sublist (?l' ++ ?s' ++ ?r') ?t |- sublist ?s' ?t' ] =>
    apply sublist_app_extend_contrav with (l := l') (r := r'); sublist_tac
  | [ H: sublist (?s' ++ ?r') ?t |- sublist ?s' ?t' ] =>
    apply sublist_app_extend_contrav with (l := []) (r := r'); sublist_tac
  | [ H: sublist (?l' ++ ?s') ?t |- sublist ?s' ?t' ] =>
    apply sublist_app_extend_contrav with (l := l') (r := []); rewrite app_nil_r; sublist_tac
  | [ H: sublist (?x ::?s') ?t |- sublist ?s' ?t' ] =>
    apply sublist_app_extend_contrav with (l := [x]) (r := []); rewrite app_nil_r; sublist_tac
  end.

Lemma Forall_sublist: forall {A : Type} (P : A -> Prop) (ss ts : list A),
    Forall P ts ->
    sublist ss ts ->
    Forall P ss.
Proof.
  intros A P ss ts H H0.
  gen_induction ss ts.
  - inversion H0; apply Forall_nil.
  - destruct ss; try apply Forall_nil.
    apply Forall_cons; inversion_clear H; inversion H0; subst.
    + specialize (IHts H2 (a0 :: ss) H4). inversion IHts; assumption.
    + assumption.
    + apply IHts; auto; sublist_tac.
    + apply IHts; auto.
Qed.

Lemma map_combine_fst_sublist: forall {A B : Type} (ls : list A) (rs : list B),
    sublist (map fst (combine ls rs)) ls.
Proof.
  intros A B ls rs.
  gen_induction rs ls; destruct rs; simpl; try apply sublist_nil.
  apply sublist_cons; auto.
Qed.

Lemma map_combine_snd_sublist: forall {A B : Type} (ls : list A) (rs : list B),
    sublist (map snd (combine ls rs)) rs.
Proof.
  intros A B ls rs.
  gen_induction ls rs; destruct ls; simpl; try apply sublist_nil.
  apply sublist_cons; auto.
Qed.

Ltac In_sublist_tac :=
  match goal with
  | [ H: In ?x ?sub' |- In ?x ?tot' ] =>
    apply In_sublist with (sub := sub') (tot := tot'); sublist_tac
  end.

Ltac Notin_sublist_tac :=
  match goal with
  | [ H: ~In ?x ?tot' |- ~In ?x ?sub' ] =>
    let H' := fresh in
    intro H'; apply H; In_sublist_tac
  end.

Ltac In_concat_tac :=
  match goal with
  | [ H': In ?e ?ls |- In ?e (concat ?ls') ] =>
    let H := fresh in
    pose proof (In_concat ls') as H;
    specialize H with (x := e) (2 := H');
    apply H;
    try unfold compose in *;
    match goal with
    | [  |- In _ (map ?ff _) ] => apply in_map with (f := ff); auto
    end
  end.

Ltac notin_reduce_tac ls :=
  match goal with
  | [ H: ~In ?x (?l ++ ?r) |- _ ] =>
    let H' := fresh in
    let sub :=
        match l with
        | context [ls] => l
        | _ => r
        end
    in assert (H': ~ In x sub); [> intro; apply H; In_sublist_tac | clear H; rename H' into H];
       notin_reduce_tac ls
  | _ => idtac
  end.


Lemma sublist_filter_cong: forall {A : Type} (f : A -> bool) (sub tot : list A),
    sublist sub tot ->
    sublist (filter f sub) (filter f tot).
Proof.
  intros A f sub tot H.
  induction H; simpl; try sublist_tac.
  - match_destruct_tac; auto.
    apply sublist_skip; auto.
  - match_destruct_tac; try apply sublist_cons; auto.
Qed.

Lemma sublist_map_inv: forall {A B : Type} (g : A -> B) (sub : list B) (l : list A),
    sublist sub (map g l) ->
    exists (sub': list A), map g sub' = sub.
Proof.
  intros A B g sub l H.
  gen_induction sub l; inversion_clear H; auto.
  - exists []; auto.
  - exists []; auto.
  - specialize (IHl _ H0).
    inversion IHl as (sub' & E).
    exists (a :: sub'); simpl; f_equal; auto.
Qed.
