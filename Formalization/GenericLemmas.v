(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: GenericLemmas.v                                                                          *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Basics.
Import ListNotations.

Require Import GenericTactics.

(**************************************************************************************************)
(** * Generic Lemmas                                                                              *)
(**************************************************************************************************)

(**************************************************************************************************)
(** ** Various Lemmas                                                                             *)
(**************************************************************************************************)

Lemma In_right_over_exists : forall {A B: Type} (x : A * B) y xs,
    (exists b, In (y,b) xs) ->
    exists b, In (y,b) (x :: xs).
Proof.
    intros A B x y xs H; inversion H; eexists; right; eauto.
Qed.

Ltac fst_eq_translates_In_tac :=
  match goal with
  | [ E: map _ ?ls = map _ ?rs |- exists body, In (?qn, body) ?rs ] =>
    match goal with
    | [ Hin: In ?tup ls |- _ ] =>
      clear - E Hin;
      let rs' := fresh "rs" in
      let rs_h := fresh "head" in
      let rs_t := fresh "tail" in
      generalize dependent rs; intro rs'; intros;
      gen_induction rs' ls; try solve [inversion Hin];
      destruct rs' as [|rs_h rs_t]; inversion E; inversion Hin; subst;
      [> let bod := fresh "bod" in
         let qn_h := fresh "qn" in destruct rs_h as [qn_h bod]; simpl in *;
                                   exists bod; left; f_equal; auto
      | apply In_right_over_exists;
        match goal with
        | [ IH: context [exists bod, In _ _] |- _ ] =>
          specialize IH with (rs' := rs_t);
          IH_tac ltac:(try assumption)
        end
      ]
    end
  end.

Lemma map_id:
  forall {A : Type} (ls : list A), map id ls = ls.
Proof.
  intros A ls. induction ls; auto; simpl; f_equal; auto.
Qed.

Lemma map_fst_map_in_fst: forall {A B C : Type} (ls : list (A * B)) (f : (A * B) -> C),
    map fst (map (fun x => (f x, snd x)) ls) = map f ls.
Proof.
  intros A B C ls f.
  induction ls; try reflexivity.
  simpl. f_equal. assumption.
Qed.

Lemma map_snd_map_in_snd: forall {A B C : Type} (ls : list (A * B)) (f : (A * B) -> C),
    map snd (map (fun x => (fst x, f x)) ls) = map f ls.
Proof.
  intros A B C ls f.
  induction ls; try reflexivity.
  simpl. f_equal. assumption.
Qed.

Section ForHints.
Hint Immediate in_eq.
Hint Immediate in_cons.
Lemma map_extensionality: forall {A B : Type} (f g : A -> B) (ls : list A),
    (forall x, In x ls -> f x = g x) ->
    map f ls = map g ls.
Proof.
  intros A B f g ls H.
  induction ls; auto.
  simpl; f_equal; auto.
Qed.
End ForHints.

Lemma fst_eq_translates_In : forall {A B C : Type} (ls : list (A * B)) (rs : list (A * C)) (a : A) (b : B),
map fst ls = map fst rs ->
        In (a, b) ls ->
        exists c, In (a, c) rs.
Proof.
  intros; fst_eq_translates_In_tac.
Qed.

Lemma fst_fst_eq_translates_In : forall {A B C D : Type} (ls : list (A * B * D)) (rs : list (A * C)) (a : A) (b : B) (d : D),
map (fun x => fst (fst x)) ls = map fst rs ->
        In (a, b, d) ls ->
        exists c, In (a, c) rs.
Proof.
  intros; fst_eq_translates_In_tac.
Qed.

Lemma fst_snd_match : forall {A B C} (p : A * B * C),
    fst (let (y, x3) := p in let (_, x2) := y in (x2, x3)) = snd (fst p).
Proof.
  intros. destruct p. destruct p. auto.
Qed.

Lemma snd_snd_match : forall {A B C} (p : A * B * C),
    snd (let (y, x3) := p in let (_, x2) := y in (x2, x3)) = snd p.
Proof.
  intros. destruct p. destruct p. auto.
Qed.

Lemma fst_as_patternmatch : forall {X Y : Type} (x : X * Y),
    fst x = let (y,_) := x in y.
Proof.
  reflexivity.
Qed.

Lemma map_fst_as_patternmatch : forall {X Y : Type} (ps : list (X * Y)),
    map fst ps = map (fun p : X * Y => let (x,_) := p in x) ps.
Proof.
  intros. induction ps; try reflexivity.
Qed.

Proposition forallb_compose : forall {A B : Type} (f : A -> B) (p : B -> bool) (ls : list A),
    forallb (compose p f) ls = forallb p (map f ls).
Proof.
  intros. induction ls. reflexivity.
  simpl. unfold compose. destruct (p (f a)). simpl. apply IHls. simpl. reflexivity.
Qed.

Lemma map_app2 : forall {A B : Type} (f : A -> B) (b1 b2 : list B) (a : list A),
    map f a = b1 ++ b2 ->
    exists a1 a2,
      map f a1 = b1 /\
      map f a2 = b2 /\
      a1 ++ a2 = a.
Proof.
  intros A B f b1 b2 a H_map.
  generalize dependent a.
  induction b1.
  -intros a H_map. exists []. exists a. auto.
  -intros a0 H_map. destruct a0; try inversion H_map.
   specialize (IHb1 a1 H1). destruct IHb1. destruct H.
   exists (a0 :: x). exists x0.
   simpl. rewrite H0. destruct H. rewrite H. destruct H2. rewrite H2. rewrite H3.
   auto.
Qed.

Lemma map_app3 : forall {A B : Type} (f : A -> B) (b1 b2 b3 : list B)(a : list A),
    map f a = b1 ++ b2 ++ b3 ->
    exists a1 a2 a3,
      map f a1 = b1 /\
      map f a2 = b2 /\
      map f a3 = b3 /\
      a1 ++ a2 ++ a3 = a.
Proof.
  intros A B f b1 b2 b3 a H_map.
  apply map_app2 in H_map.
  destruct H_map as [a1 [a2 [H1 [H2 H3]]]].
  apply map_app2 in H2.
  destruct H2 as [a2' [a2'' [G1 [G2 G3]]]].
  exists a1. exists a2'. exists a2''.
  repeat split; try assumption.
  rewrite G3. rewrite H3. reflexivity.
Qed.

Lemma if_true_branch : forall {A} (b : bool) (x y : A),
    b = true -> ((if b then x else y) = x).
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma let_fst_snd_forallb : forall {A B} (l : list (A * B)) f,
  forallb
    (fun x : A * B =>
     let (a, b) := x in f a b) l =
  forallb
    (fun x : A * B =>
       f (fst x) (snd x)) l.
Proof.
  induction l.
  * simpl. reflexivity.
  * intros. simpl. rewrite IHl. f_equal.
    destruct a. simpl. reflexivity.
Qed.

Lemma In_fst: forall {A B : Type} (a : A) (b : B) (ls : list (A * B)),
    In (a, b) ls ->
    In a (map fst ls).
Proof.
  intros A B a b ls H.
  induction ls; try solve [inversion H].
  inversion H.
  - rewrite H0. simpl. left; reflexivity.
  - right; apply IHls; try assumption.
Qed.

Lemma In_snd: forall {A B : Type} (a : A) (b : B) (ls : list (A * B)),
    In (a, b) ls ->
    In b (map snd ls).
Proof.
  intros A B a b ls H.
  induction ls; try solve [inversion H].
  inversion H.
  - rewrite H0. simpl. left; reflexivity.
  - right; apply IHls; try assumption.
Qed.

Lemma in_firstn : forall {A} n (x : A) l,
    In x (firstn n l) -> In x l.
Proof.
  intros. generalize dependent l. induction n.
  * intros. simpl in H. exfalso. assumption.
  * intros.
    destruct l; simpl in H; try (exfalso; assumption).
    destruct H; simpl; try (left; assumption).
    right. apply IHn. assumption.
Qed.

Lemma firstn_minus_1 : forall {A} n l (x : A),
  nth_error l n = Some x ->
  firstn (S n) l = firstn n l ++ [x].
Proof.
  intros. generalize dependent x. generalize dependent l. induction n.
  * intros. simpl. destruct l. simpl in H. discriminate. simpl in H. inversion H; subst. reflexivity.
  * intros. destruct l. simpl. simpl in H. discriminate. rewrite firstn_cons.
    erewrite IHn. rewrite firstn_cons. rewrite app_comm_cons. instantiate (1:=x). reflexivity.
    simpl in H. assumption.
Qed.

Lemma In_app_symm : forall {A : Type} (xs ys : list A) (a : A),
    In a (xs ++ ys) <-> In a (ys ++ xs).
Proof.
  intros. split.
  - intro. generalize dependent ys. induction xs.
    + intros ys H. simpl in *. rewrite app_nil_r. assumption.
    + intros ys H. simpl in *. destruct H.
      * subst. apply in_or_app. right. simpl. left. reflexivity.
      * apply IHxs in H. apply in_app_or in H. destruct H.
        ** apply in_or_app. left. assumption.
        ** apply in_or_app. right. simpl. right. assumption.
  - intro. generalize dependent xs. induction ys.
    + intros xs H. simpl in *. rewrite app_nil_r. assumption.
    + intros xs H. simpl in *. destruct H.
      * subst. apply in_or_app. right. simpl. left. reflexivity.
      * apply IHys in H. apply in_app_or in H. destruct H.
        ** apply in_or_app. left. assumption.
        ** apply in_or_app. right. simpl. right. assumption.
Qed.

Lemma forallb_false_iff_existsb : forall (A : Type) (P : A -> bool)(ls : list A),
    forallb P ls = false ->
    existsb (fun x => negb (P x)) ls = true.
Proof.
  intros A P ls H. induction ls.
  - simpl in *. inversion H.
  - simpl in *. destruct (P a); simpl in *.
    + apply IHls. assumption.
    + reflexivity.
Qed.

Lemma forallb_app_false : forall {A : Type} (P : A -> bool) (left right : list A),
    forallb P (left ++ right) = false ->
    forallb P left = true ->
    forallb P right = false.
Proof.
  intros A P left right Hall Hleft.
  induction left; try assumption.
  simpl in Hleft. apply andb_true_iff in Hleft. destruct Hleft as [Ha Htail].
  simpl in Hall. rewrite Ha in Hall.
  apply IHleft; try assumption.
Qed.


Lemma app_eq : forall {A : Type} (xs ys ys' : list A),
    (xs ++ ys) = (xs ++ ys') -> ys = ys'.
Proof.
  intros. induction xs; simpl in *; try auto.
  inversion H. apply IHxs. assumption.
Qed.

Lemma Not_In_App : forall {A : Type} (xs ys : list A) (a : A),
    ~ In a (xs ++ ys) <-> ~ In a xs /\ ~ In a ys.
Proof.
  intros A xs ys a. split.
  - intro H. split.
    + induction xs.
      * simpl. intro H2. assumption.
      * simpl in *. intro H2. destruct H2.
        ** subst. apply H. left. reflexivity.
        ** apply H. right. apply in_or_app. left. assumption.
    + intro H_abs. apply H. apply in_or_app. right. assumption.
  -intros [H1 H2] H3. apply in_app_or in H3. destruct H3.
   + apply H1. assumption.
   + apply H2. assumption.
Qed.

(**************************************************************************************************)
(** ** Forall Lemmas                                                                              *)
(**************************************************************************************************)

Lemma Forall_extract : forall {A : Type} (P : A -> Prop) (ls : list A) (a : A),
    Forall P ls ->
    In a ls ->
    P a.
Proof.
  intros A P ls a H H_in.
  induction ls; try solve [inversion H_in].
  inversion H_in as [E | E].
  - rewrite E in H. inversion H. assumption.
  - inversion H; apply IHls; assumption.
Qed.

Lemma Forall_And: forall {A : Type} (P Q : A -> Prop) (ls : list A),
    Forall P ls /\ Forall Q ls <-> Forall (fun x => P x /\ Q x) ls.
Proof.
  split; intros;
    [ inversion_clear H as [H1 H2]; induction ls; inversion_clear H1; inversion_clear H2; try apply Forall_cons; auto
    | split; induction ls; try inversion_clear H as [|_x __x H1 H2]; try apply Forall_cons; try inversion_clear H1; auto
    ].
Qed.

Lemma Forall_eta: forall {A : Type} (ls : list A) (P : A -> Prop),
    Forall (fun x => P x) ls <-> Forall P ls.
Proof.
  intros A ls P.
  split; intro H; induction ls; try apply Forall_nil; apply Forall_cons;
    try solve [inversion H; subst; auto].
Qed.

Lemma Forall_app : forall (A : Type) (P : A -> Prop) (ls ls' : list A),
    Forall P ls ->
    Forall P ls' ->
    Forall P (ls ++ ls').
Proof.
  intros A P ls. induction ls; intros.
  -simpl. assumption.
  -simpl. inversion H; subst. apply Forall_cons.
   +assumption.
   +apply IHls; try assumption.
Qed.

Lemma Forall_app_iff: forall {A : Type} (P : A -> Prop) (ls rs : list A),
    Forall P ls /\ Forall P rs <-> Forall P (ls ++ rs).
Proof.
  intros; split; intro; try (apply Forall_app; inversion H; auto).
  split; induction ls; auto; inversion H; auto.
Qed.

Lemma Forall_In : forall {A : Type} (x : A) (xs : list A) (P : A -> Prop),
    Forall P xs ->
    In x xs ->
    P x.
Proof.
  intros A x xs P H H0. induction xs.
  - inversion H0.
  - inversion H; subst. simpl in H0. destruct H0.
    + subst. assumption.
    + auto.
Qed.

Lemma Forall_In_left : forall {A B: Type} (f : B -> A) (xs ys : list A) (ls : list B),
    Forall (fun x => In (f x) xs) ls ->
    Forall (fun x => In (f x) (xs ++ ys)) ls.
Proof.
  intros A B f xs. induction xs.
  - intros ys ls H. simpl in *. destruct ls.
    + apply Forall_nil.
    + inversion H. contradiction.
  - intros ys ls H. simpl in *. induction ls.
    + apply Forall_nil.
    + inversion H; subst. destruct H2.
      * subst. apply Forall_cons.
        ** left. reflexivity.
        ** apply IHls. assumption.
      * apply Forall_cons.
        ** right. apply in_or_app. left. assumption.
        ** apply IHls. assumption.
Qed.

Lemma Forall_map : forall {A B} P (f : A -> B) (ls : list A),
  Forall (fun x => P (f x)) ls <->
  Forall P (map f ls).
Proof.
  intros; split; intro H;
    [> induction ls;
     [> simpl; apply Forall_nil
     | rewrite Forall_forall; intros; simpl in H0; destruct H0;
       [> inversion H; subst; assumption
       | inversion H; subst; pose proof (IHls H4); rewrite Forall_forall in H1;
         apply H1; assumption
       ]
     ]
       .. ].
Qed.

Lemma Forall_In_right : forall {A B: Type} (f : B -> A) (xs ys : list A) (ls : list B),
    Forall (fun x => In (f x) ys) ls ->
    Forall (fun x => In (f x)  (xs ++ ys)) ls.
Proof.
  intros A B f xs ys ls H. induction ls.
  - apply Forall_nil.
  - apply Forall_cons.
    + apply in_or_app. right. inversion H; subst. assumption.
    + inversion H; subst.  apply IHls. assumption.
Qed.

Lemma Forall_Or_left : forall {A : Type} (P Q : A -> Prop) (ls : list A),
  Forall (fun x => P x) ls ->
  Forall (fun x => P x \/ Q x) ls.
Proof.
  intros A P Q ls H.
  induction ls.
  - apply Forall_nil.
  - apply Forall_cons.
    + inversion H; subst. left. assumption.
    + inversion H; subst. apply IHls. assumption.
Qed.

Lemma Forall_Or_right : forall {A : Type} (P Q : A -> Prop) (ls : list A),
  Forall (fun x => Q x) ls ->
  Forall (fun x => P x \/ Q x) ls.
Proof.
  intros A P Q ls H.
  induction ls.
  - apply Forall_nil.
  - apply Forall_cons.
    + inversion H; subst. right. assumption.
    + inversion H; subst. apply IHls. assumption.
Qed.

Lemma Forall_flatten: forall {A B : Type} (l : list A) (f : A -> list B) (P : B -> Prop),
             Forall P (concat (map f l))
             <-> Forall (fun x => Forall P (f x)) l.
Proof.
  intros A B l f P.
  split; [> intros; induction l; [> apply Forall_nil | simpl] ..].
  - simpl in H.
    apply Forall_cons.
    + clear - H. induction (f a); try apply Forall_nil.
      apply Forall_cons; inversion H.
      * simpl in H; assumption.
      * IH_tac.
    + IH_tac. rewrite Forall_forall in H. rewrite Forall_forall; intros.
      apply H. apply in_app_iff; right; assumption.
  - apply Forall_app; inversion_clear H; try assumption.
    IH_auto_tac.
Qed.

Lemma Forall_impl2: forall {A : Type} (ls : list A) (P Q: A -> Prop),
    Forall (fun x => P x -> Q x) ls -> Forall P ls -> Forall Q ls.
Proof.
  intros A ls P Q H H0.
  induction ls; try apply Forall_nil.
  apply Forall_cons; try (IH_tac Forall_tail_tac).
  inversion H0; inversion H; auto.
Qed.

Lemma Forall_nested_app: forall {A B : Type} (P: A -> B -> Prop) (ls : list A) (l r : list B),
    Forall (fun x => Forall (P x) l) ls ->
    Forall (fun x => Forall (P x) r) ls ->
    Forall (fun x => Forall (P x) (l ++ r)) ls.
Proof.
  intros A B P ls l r Hl Hr.
  induction ls; try apply Forall_nil.
  inversion Hl; subst. inversion Hr; subst.
  apply Forall_cons.
  - apply Forall_app; auto.
  - IH_tac.
Qed.

(**************************************************************************************************)
(** ** Forall2 Lemmas                                                                             *)
(**************************************************************************************************)

Lemma Forall2_length : forall {A B} {P} (ls1 : list A) (ls2 : list B),
    Forall2 P ls1 ls2 -> length ls1 = length ls2.
Proof.
  intros A B P. induction ls1.
  * intros. inversion H. reflexivity.
  * intros. inversion H; subst. simpl. f_equal. apply IHls1. assumption.
Qed.

Lemma Forall2_Forall : forall {A B} {P} (ls1 : list A) (ls2 : list B),
    Forall2 P ls1 ls2 -> Forall (fun x => P (fst x) (snd x)) (combine ls1 ls2).
Proof.
  intros. rewrite Forall_forall.
  induction H.
  * intros. simpl in H. exfalso. assumption.
  * intros. simpl in H1. destruct H1.
  + subst. simpl. assumption.
  + apply IHForall2. assumption.
Qed.

Lemma Forall_Forall2 : forall {A B} {P} (ls1 : list A) (ls2 : list B),
  Forall (fun x => P (fst x) (snd x)) (combine ls1 ls2)->
  length ls1 = length ls2 ->
  Forall2 P ls1 ls2.
Proof.
  intros.
  generalize dependent ls2.
  induction ls1.
  * intros. destruct ls2; try (simpl in H0; discriminate).
    apply Forall2_nil.
  * intros. destruct ls2; try (simpl in H0; discriminate).
    apply Forall2_cons.
  + inversion H; subst. simpl in H3. assumption.
  + apply IHls1.
  - simpl in H. inversion H. assumption.
  - simpl in H0. inversion H0. reflexivity.
Qed.

Lemma Forall2_map : forall {A B C} (ls1 : list A) (ls2 : list B) (f : A -> C) (g : B -> C),
  Forall2 (fun x y => f x = g y) ls1 ls2 ->
  map f ls1 = map g ls2.
Proof.
  intros. generalize dependent ls2. induction ls1.
  * intros. inversion H; subst. simpl. reflexivity.
  * intros. inversion H; subst. simpl. rewrite H2. f_equal. apply IHls1. assumption.
Qed.

Lemma Forall2_inner_some_exists : forall {A B C} (ls1 : list A) (ls2 : list B) (f : A -> option C) (g : B -> option C),
  Forall2 (fun x y => forall z, f x = Some z -> g y = Some z) ls1 ls2 ->
  Forall (fun x => exists z, f x = Some z) ls1 ->
  Forall2 (fun x y => f x = g y) ls1 ls2.
Proof.
  intros.
  generalize dependent ls2.
  induction ls1; intros; inversion H; subst; try (apply Forall2_nil).
  apply Forall2_cons.
  inversion H0; subst.
  destruct H4.
  rewrite H1. symmetry.
  apply H3. assumption.
  apply IHls1.
  inversion H0; subst. assumption.
  assumption.
Qed.

Lemma Forall2_forall_symm: forall {A : Type} (P: A -> A -> Prop) (ls : list A),
    (forall a, P a a) ->
    Forall2 P ls ls.
Proof.
  intros A P ls H.
  induction ls; try apply Forall2_nil.
  apply Forall2_cons; auto.
Qed.

Lemma Forall2_map2: forall {A B C D : Type} (P: B -> D -> Prop) (f : A -> B) (g : C -> D) (ls : list A) (rs : list C),
    Forall2 P (map f ls) (map g rs) <-> Forall2 (fun a c => P (f a) (g c)) ls rs.
Proof.
  intros A B C D P f g ls rs.
  split; intro H;
    gen_induction rs ls; destruct rs; inversion H; subst; try apply Forall2_nil;
      apply Forall2_cons; auto.
Qed.

Lemma Forall2_map_l: forall {A B C: Type} (P: B -> C -> Prop) (f : A -> B) (ls : list A) (rs : list C),
    Forall2 P (map f ls) rs <-> Forall2 (fun a c => P (f a) c) ls rs.
Proof.
  intros A B C P f ls rs.
  rewrite <- Forall2_map2. rewrite map_map.
  apply Forall2_map2.
Qed.

Lemma Forall2_map_r: forall {A B C: Type} (P: A -> C -> Prop) (g : B -> C) (ls : list A) (rs : list B),
    Forall2 P ls (map g rs) <-> Forall2 (fun a b => P a (g b)) ls rs.
Proof.
  intros A B C P f ls rs.
  rewrite <- Forall2_map2. rewrite map_map.
  apply Forall2_map2.
Qed.
(**************************************************************************************************)
(** ** find Lemmas                                                                                *)
(**************************************************************************************************)

Lemma find_none_append : forall (A : Type) (f : A -> bool) (ls ls' : list A),
    find f ls = None ->
    find f ls' = find f (ls ++ ls').
Proof.
  intros A f ls ls' H_none.
  induction ls.
  -simpl. reflexivity.
  -simpl in *. destruct (f a); try inversion H_none. apply IHls. assumption.
Qed.

Lemma find_fst_fst_match : forall {A B C} (ls : list (A * B * C)) f,
    find (fun x => f (fst (fst x))) ls = find (fun x : A * B * C => let (y,_) := x in let (n,_) := y in f n) ls.
Proof.
  intros. induction ls; simpl; try reflexivity. case_eq (f (fst (fst a))); intros;
                                                  destruct a; destruct p; simpl in H; rewrite H; try reflexivity.
  assumption.
Qed.

Lemma find_in: forall {A : Type} (f : A -> bool) (ls : list A) (a : A),
    find f ls = Some a ->
    In a ls.
Proof.
  intros A f ls a H_find.
  induction ls as [| a_l l].
  - inversion H_find.
  - simpl in H_find. destruct (f a_l).
    + left; inversion H_find; reflexivity.
    + right; apply IHl; assumption.
Qed.

(**************************************************************************************************)
(** ** combine Lemmas                                                                             *)
(**************************************************************************************************)

Lemma map_compose:
    forall (A B C : Type) (f : A -> B) (g : B -> C) (ls : list A), map g (map f ls) = map (fun a : A => g (f a)) ls.
Proof.
    intros A B C f g ls.
    induction ls; try reflexivity.
    simpl. f_equal. apply IHls.
Qed.

Lemma map_fst_f_combine : forall {A B C} (l1 : list A) (l2 : list B) (f: A -> C),
    map (fun x => (f (fst x), snd x)) (combine l1 l2) = combine (map f l1) l2.
Proof.
  intros. generalize l2. induction l1.
  * intro. simpl. reflexivity.
  * intro. rewrite map_cons. destruct l0. simpl. reflexivity. simpl. f_equal. apply IHl1.
Qed.

Lemma map_snd_f_combine : forall {A B C} (l1 : list A) (l2 : list B) (f: B -> C),
    map (fun x => (fst x, f (snd x))) (combine l1 l2) = combine l1 (map f l2).
Proof.
  intros. generalize l2. induction l1.
  * intro. simpl. reflexivity.
  * intro. destruct l0. simpl. reflexivity. simpl. f_equal. apply IHl1.
Qed.

Lemma map_fst_combine : forall {A B} (l1 : list A) (l2 : list B),
  length l1 = length l2 ->
  map fst (combine l1 l2) = l1.
Proof.
  intros. generalize dependent l2. induction l1.
  * intro. simpl. reflexivity.
  * intro. destruct l2. simpl. discriminate.
    simpl. intro. rewrite IHl1. reflexivity. inversion H. reflexivity.
Qed.

Lemma map_combine_fst : forall {A A' B} (ls1 : list A) (ls2 : list B) (f : A -> A'),
    map (fun x => (f (fst x), snd x)) (combine ls1 ls2) = combine (map f ls1) ls2.
Proof.
  intros. generalize dependent ls2. induction ls1.
  * simpl. reflexivity.
  * intros. destruct ls2; simpl; try reflexivity. f_equal. apply IHls1.
Qed.

Lemma map_snd_combine : forall {A B : Type} (la : list A) (lb : list B) (H_length : length la = length lb),
    map snd (combine la lb) = lb.
Proof.
  intros A B la. induction la; intros lb H_length; destruct lb; try reflexivity; try (solve [inversion H_length]).
  inversion H_length. apply IHla in H0. simpl. rewrite H0. reflexivity.
Qed.

Lemma combine_fst_snd : forall {X Y : Type} (ps : list (X * Y)),
    ps = combine (map fst ps) (map snd ps).
Proof.
  intros. induction ps; try reflexivity.
  simpl. destruct a. f_equal. apply IHps.
Qed.

Lemma combine_in : forall {A B} {x : A} {xs ys},
    In x xs -> length xs = length ys -> exists y : B, In (y,x) (combine ys xs).
Proof.
  intros A B x. induction xs.
  * intros. inversion H.
  * intros. destruct ys. simpl in H0. discriminate. simpl. inversion H.
  + exists b. rewrite H1. auto.
  + assert (exists y, In (y, x) (combine ys xs)). simpl in H0. inversion H0. apply IHxs; try assumption.
    destruct H2. exists x0. right. assumption.
Qed.

Lemma in_combine_switch : forall {A B} xs ys (x : A) (y : B),
  length xs = length ys ->
  In (x,y) (combine xs ys) ->
  In (y,x) (combine ys xs).
Proof.
  intros. generalize dependent ys. induction xs.
  * intros. exfalso. simpl in H0. assumption.
  * intros. case_eq ys; intros; rewrite H1 in *; inversion H. simpl. simpl in H0.
    destruct H0.
  + left. inversion H0; subst. reflexivity.
  + right. apply IHxs; assumption.
Qed.



Lemma map_snd_match : forall {A11 A12 A2} (ls : list (A11 * A12 * A2)),
    map snd ls = map (fun z : A11 * A12 * A2 => let (y, x) := z in let (_, _) := y in x) ls.
Proof.
  induction ls; try (simpl; reflexivity).
  simpl. rewrite IHls. f_equal. destruct a. destruct p. simpl. reflexivity.
Qed.

Lemma combine_empty_r : forall {X Y : Type} (xs : list X),
    combine xs ([] : list Y) = [].
Proof.
  intros. induction xs; try reflexivity.
Qed.


Lemma combine_simultaneous_snd: forall {X Y : Type} (xs xs' : list X) (ys ys' : list Y),
    List.length xs = List.length ys ->
    List.length xs' = List.length ys' ->
    combine xs ys = combine xs' ys' ->
    ys = ys'.
Proof.
  intros X Y xs xs' ys ys' Hlenx Hleny Hcombine.
  apply f_equal with (f := map snd) in Hcombine.
  assert (Hys : map snd (combine xs ys) = ys). apply map_snd_combine; try assumption.
  assert (Hys' : map snd (combine xs' ys') = ys'). apply map_snd_combine; try assumption.
  rewrite <- Hys; rewrite <- Hys'. assumption.
Qed.
Lemma combine_simultaneous_fst : forall {X Y : Type} (xs xs' : list X) (ys ys' : list Y),
    List.length xs = List.length ys ->
    List.length xs' = List.length ys' ->
    combine xs ys = combine xs' ys' ->
    xs = xs'.
Proof.
  intros X Y xs xs' ys ys' Hlenx Hleny Hcombine.
  apply f_equal with (f := map fst) in Hcombine.
  assert (Hxs : map fst (combine xs ys) = xs). apply map_fst_combine; try assumption.
  assert (Hxs' : map fst (combine xs' ys') = xs'). apply map_fst_combine; try assumption.
  rewrite <- Hxs; rewrite <- Hxs'. assumption.
Qed.

Lemma map_combine_in_fst : forall {X Y Z : Type} (xs : list X) (ys : list Y) (f : X -> Z),
    map (fun p : X * Y => let (x,y) := p in (f x, y)) (combine xs ys)
    = combine (map f xs) ys.
Proof.
  intros X Y Z xs ys f.
  generalize dependent ys. induction xs; intros; try reflexivity.
  simpl. destruct ys; try reflexivity.
  simpl. f_equal. apply IHxs.
Qed.

Lemma map_combine2_in_third : forall {X Y Z R : Type} (xs : list X) (ys : list Y) (zs : list Z) (f : Z -> R),
    map (fun t : X * Y * Z => let (p,z) := t in let (x,y) := p in (x, y, f z)) (combine (combine xs ys) zs)
    = (combine (combine xs ys) (map f zs)).
Proof.
  intros X Y Z R xs ys zs f.
  generalize dependent xs. generalize dependent ys. induction zs; intros; try reflexivity.
  -simpl. destruct xs; try reflexivity.
   simpl. destruct ys; try reflexivity.
  -destruct xs; destruct ys; try reflexivity.
   simpl. f_equal. apply IHzs.
Qed.

Lemma split_pair_lists : forall {X Y : Type} (ps : list (X * Y)),
    exists (xs : list X) (ys : list Y), ps = combine xs ys.
Proof.
  intros. induction ps.
  -do 2 (exists []). reflexivity.
  -destruct a as [x y].
   inversion IHps as [xs H]. exists (x :: xs).
   inversion H as [ys H']. exists (y :: ys).
   simpl. f_equal. assumption.
Qed.

(**************************************************************************************************)
(** ** filter Lemmas                                                                              *)
(**************************************************************************************************)

Lemma Forall_filter : forall (A : Type) (P : A -> Prop)(Q : A -> bool) (ls : list A),
    Forall P ls ->
    Forall P (filter Q ls).
Proof.
  intros A P Q ls H_ls. induction ls.
  -simpl. apply Forall_nil.
  -simpl. destruct (Q a).
   +inversion H_ls; subst. apply Forall_cons.
    *assumption.
    *apply IHls. assumption.
   +inversion H_ls; subst. apply IHls. assumption.
Qed.

Lemma filter_ext_restricted: forall {A : Type} (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = g x) ->
    filter f l = filter g l.
Proof.
  intros A f g l H.
  induction l; auto; simpl; f_equal; auto.
  match_destruct_tac;
    [ rewrite H in E_match; [ | left; easy ];
    rewrite E_match; simpl; f_equal + idtac; apply IHl;
    intros; apply H; right; easy .. ].
Qed.

Lemma Forall_false_filter_nil: forall {A : Type} (f : A -> bool) (ls : list A),
    Forall (fun x => f x = false) ls ->
    filter f ls = [].
Proof.
  intros A f ls H.
  induction ls; auto; simpl; inversion_clear H.
  rewrite H0; auto.
Qed.

Lemma filter_nonempty : forall {A} f l (x : A),
  In x l ->
  f x = true ->
  exists a l0, filter f l = a :: l0.
Proof.
  intros. induction l; inversion H.
  * rewrite <- H1 in H0. exists a. exists (filter f l). simpl. rewrite H0. reflexivity.
  * case_eq (f a); intros; try (exists a; exists (filter f l); simpl; rewrite H2; reflexivity).
    pose proof (IHl H1). destruct H3. destruct H3. exists x0. exists x1. simpl. rewrite H2. assumption.
Qed.

Lemma let_fst_fst_filter : forall {A B C} f l,
    filter (fun x : A * B * C => f (fst (fst x))) l =
    filter (fun x : A * B * C => let (y, _) := x in let (n, _) := y in f n) l.
Proof.
  induction l; simpl; try (reflexivity).
  rewrite IHl.
  assert ((let (y, _) := a in let (n, _) := y in f n) = f (fst (fst a))) as Aux.
  destruct a. destruct p. simpl. reflexivity.
  rewrite <- Aux. reflexivity.
Qed.

Lemma filter_ext: forall {A : Type} (f g : A -> bool),
    (forall a : A, f a = g a) ->
    forall l : list A, filter f l = filter g l.
Proof.
  intros A f g H l.
  induction l; auto; simpl in *; rewrite H; match_destruct_tac; try solve [f_equal; auto]; easy.
Qed.

Lemma filter_app : forall (A : Type) (xs ys : list A) (P : A -> bool),
    filter P (xs ++ ys) = (filter P xs) ++ (filter P ys).
Proof.
  intros A xs ys P.
  generalize dependent ys. induction xs.
  - intros ys. simpl. reflexivity.
  - intros ys. simpl. destruct (P a).
    + simpl. f_equal. apply IHxs.
    + apply IHxs.
Qed.

Lemma filter_elem_false: forall {A : Type} (p : A -> bool) (l r : list A) (a : A),
    p a = false ->
    filter p (l ++ a :: r) = filter p (l ++ r).
Proof.
  intros A p l r a H.
  repeat rewrite filter_app; f_equal.
  simpl; match_destruct_tac; auto.
  inversion H.
Qed.

Lemma filter_map : forall {A B} (l : list A) (f : A -> B) g,
  map f (filter (fun x => g (f x)) l) = filter g (map f l).
Proof with auto. intros. induction l... simpl. case (g (f a))... simpl. f_equal... Qed.

Lemma length_filter_lemma : forall (A B : Type) (xs ys : list A) (P : B -> A -> bool),
    (forall b, length (filter (P b) xs) = 0 \/ length (filter (P b) xs) = 1) ->
    (forall b, length (filter (P b) ys) = 0 \/ length (filter (P b) ys) = 1) ->
    ~(exists b,  length (filter (P b) xs) = 1 /\ length (filter (P b) ys) = 1) ->
    (forall b, length (filter (P b) (xs ++ ys)) = 0 \/ length (filter (P b) (xs ++ ys)) = 1).
Proof.
  intros A B xs ys P H H0 H1 b. specialize (H b). specialize (H0 b).
  destruct H; destruct H0.
  - left. rewrite filter_app. rewrite app_length. omega.
  - right. rewrite filter_app. rewrite app_length. omega.
  - right. rewrite filter_app. rewrite app_length. omega.
  - exfalso. apply H1. exists b. split; assumption.
Qed.

Lemma length_filter_one : forall (A : Type) (P : A -> bool) (xs : list A),
    length (filter P xs) = 1 ->
    (exists x, In x xs /\ P x = true).
Proof.
  intros A P xs H. induction xs.
  - inversion H.
  - simpl in *. destruct (P a) eqn:E.
    + exists a. auto.
    + apply IHxs in H. destruct H as [H1 [H2 H3]]. exists H1. auto.
Qed.

Lemma length_filter_app : forall (A : Type) (pb : A -> bool) (ls ls' : list A),
    length (filter pb (ls ++ ls')) = length (filter pb ls) + length (filter pb ls').
Proof.
  intros A pb ls ls'.
  induction ls.
  - simpl.  reflexivity.
  - simpl. destruct (pb a).
    + simpl. f_equal. assumption.
    + assumption.
Qed.

Lemma filter_filter : forall {A : Type} (P Q : A -> bool) (xs : list A),
    filter P (filter Q xs) = filter Q (filter P xs).
Proof.
  intros A P Q xs. induction xs; try reflexivity.
  simpl. destruct (P a) eqn:E ; destruct (Q a) eqn:E'.
  - simpl. rewrite E. rewrite E'. f_equal. assumption.
  - simpl. rewrite E'. assumption.
  - simpl. rewrite E. assumption.
  - assumption.
Qed.

Lemma filter_filter_zero : forall {A : Type} (P Q : A -> bool) (xs : list A),
    length (filter P xs) = 0 ->
    length (filter Q (filter P xs)) = 0.
Proof.
  intros A P Q xs H. induction xs.
  - simpl. reflexivity.
  - simpl. destruct (P a) eqn:E.
    + simpl in *. rewrite E in *. simpl in *. inversion H.
    + simpl in *. rewrite E in *. apply IHxs. assumption.
Qed.

Lemma filter_length : forall (A : Type) (P Q : A -> bool) (ls : list A) (n : nat),
    length (filter P ls) = n ->
    length (filter P (filter Q ls)) <= n.
Proof.
  intros A P Q ls n H. generalize dependent n.
  induction ls.
  -intros n H. simpl. omega.
  -intros n H. simpl. destruct (Q a) eqn:E.
   +simpl in *. destruct (P a).
    *simpl in *. destruct n; try inversion H. specialize (IHls n H1). omega.
    *apply IHls. assumption.
   +simpl in *. destruct (P a).
    *simpl in H. destruct n; try inversion H. specialize (IHls n H1). omega.
    *apply IHls. assumption.
Qed.

(**************************************************************************************************)
(** ** rev Lemmas                                                                                 *)
(**************************************************************************************************)

Lemma rev_firstn_rev' : forall {A} n l l0 l1 (x y : A),
  rev l = y :: l0 ->
  rev (firstn (S n) l0) ++ [y] = x :: l1 ->
  S n < length l ->
  l1 = rev (firstn (S n) (rev l)).
Proof.
  intros.
  assert (forall xn, nth_error l0 n = Some xn -> rev (firstn (S n) l0) ++ [y] = xn :: rev (firstn (S n) (rev l))).
  * intros.
    rewrite (firstn_minus_1 _ _ xn); try assumption.
    rewrite rev_app_distr.
    rewrite H. simpl. reflexivity.
  * assert (exists xn, nth_error l0 n = Some xn).
    assert (n < length l0) as Len.
    apply (f_equal (length (A:=A))) in H. rewrite rev_length in H. rewrite H in H1. simpl in H1.
    rewrite Nat.lt_succ_r in H1. unfold lt. assumption.
    rewrite <- nth_error_Some in Len.
    case_eq (nth_error l0 n); intros. exists a. reflexivity. exfalso. auto.
    assert (forall xn, nth_error l0 n = Some xn -> xn :: rev (firstn (S n) (rev l)) = x :: l1).
    intros. rewrite <- H2; assumption.
    destruct H3. pose proof (H4 x0 H3). inversion H5. reflexivity.
Qed.

Lemma rev_firstn_rev : forall {A} n l l0 l1 (x y : A),
  rev l = y :: l0 ->
  rev (firstn n l0) ++ [y] = x :: l1 ->
  n < length l ->
  l1 = rev (firstn n (rev l)).
Proof.
  destruct n.
  * intros. simpl. simpl in H0. inversion H0. reflexivity.
  * apply rev_firstn_rev'.
Qed.

Lemma Forall_compose_map : forall {A B : Type} (ls : list A) (f : A -> B) (P : B -> Prop),
    Forall (compose P f) ls <-> Forall P (map f ls).
Proof.
  intros. unfold iff. split.
  -intro. induction ls; try solve [apply Forall_nil].
   apply Forall_cons; try solve [inversion H; assumption].
   apply IHls. inversion H. assumption.
  -intro. induction ls; try solve [apply Forall_nll].
   +apply Forall_nil.
   +apply Forall_cons; try solve [inversion H; assumption].
    apply IHls. inversion H. assumption.
Qed.

Lemma forallb_compose_map : forall {A B : Type} (ls : list A) (f : A -> B) (p : B -> bool),
    forallb (compose p f) ls = forallb p (map f ls).
Proof.
  intros. induction ls; try reflexivity.
  simpl. f_equal. apply IHls.
Qed.


Fact concat_app' : forall {A} (l1 l2 : list (list A)), concat l1 ++ concat l2 = concat (l1 ++ l2).
Proof.
intros. generalize dependent l2. induction l1; intros; auto.
simpl. rewrite <- app_assoc. rewrite IHl1. auto.
Qed.

Fact filter_concat : forall {A} f (l : list (list A)),
  filter f (concat l) = concat (map (filter f) l).
Proof with auto. induction l... simpl. rewrite filter_app. f_equal... Qed.

Lemma flat_map_app: forall {A B : Type} (ls rs : list A) (f : A -> list B),
    flat_map f (ls ++ rs) = flat_map f ls ++ flat_map f rs.
Proof.
  intros A B ls rs f.
  repeat rewrite flat_map_concat_map.
  rewrite map_app. rewrite concat_app. reflexivity.
Qed.

Lemma map_cong: forall {A B : Type} (f g : A -> B) (ls : list A),
    (forall x, f x = g x) ->
    map f ls = map g ls.
Proof.
  intros A B f g ls H.
  induction ls; auto.
  simpl. f_equal; auto.
Qed.


(********************************************************************)
(*** general lemmas ***)
(********************************************************************)

Lemma in_concat_stuff: forall {A B C : Type} (h : A -> list B) (g : B -> list A) (f: A -> list C) (ls : list A) (c : C),
    (forall d a, In d (concat (map f (concat (map g (h a))))) -> In d (f a)) ->
    In c (concat (map f (concat (map g (concat (map h ls)))))) ->
    In c (concat (map f ls)).
Proof.
  intros A B C h g f ls b Hin_com Hin.
  induction ls; simpl in *; auto; try solve [inversion Hin].
  repeat (rewrite map_app in Hin; rewrite concat_app in Hin).
  rewrite in_app_iff; rewrite in_app_iff in Hin.
  inversion Hin; [> left | right]; auto.
Qed.

Lemma In_concat: forall {A : Type} (lss: list (list A)) (ls : list A) (x : A),
    In ls lss ->
    In x ls ->
    In x (concat lss).
Proof.
  intros A lss ls x H_lss H_ls.
  induction lss; inversion_clear H_lss; subst; simpl in *;
    rewrite in_app_iff; auto.
Qed.

Lemma In_concat_iff: forall {A : Type} (lss: list (list A)) (x : A),
    (exists ls, In ls lss /\ In x ls) <->
    In x (concat lss).
Proof.
  intros A lss x; split; intro H; try inversion_clear H as [ls [H1 H2]]; try eapply In_concat; eauto.
  induction lss; simpl in *; try easy.
  rewrite in_app_iff in H; inversion_clear H; eauto.
  specialize (IHlss H0); inversion_clear IHlss as [ls [H H1]].
  eauto.
Qed.

Lemma in_map_concat: forall {A B : Type} (f g : A -> list B) (b : B) (ls : list A),
    (forall b a, In b (f a) -> In b (g a)) ->
    In b (concat (map f ls)) ->
    In b (concat (map g ls)).
Proof.
  intros A B f g b ls H Hin.
  induction ls; auto; simpl in *.
  rewrite in_app_iff in *; inversion Hin; [> left | right ]; auto.
Qed.

Lemma map_concat_switch: forall {A B : Type} (ls : list A) (f : A -> list (list (list B))),
    concat (map (@concat (list B)) (map f ls)) = concat (concat (map f ls)).
Proof.
  intros A B ls f.
  induction ls; auto; simpl in *.
  rewrite concat_app; f_equal; auto.
Qed.

Lemma map_concat_switch': forall {A B : Type} (ls : list (list A)) (f : list A -> list (list B)),
    concat (map (@concat B) (map f ls)) = concat (concat (map f ls)).
Proof.
  intros A B ls f.
  induction ls; auto; simpl in *.
  rewrite concat_app; f_equal; auto.
Qed.

Lemma impl_distributes_over_and_param: forall {A : Type} (P Q R : A -> Prop) (a : A),
    (P a -> Q a /\ R a) <-> (P a -> Q a) /\ (P a -> R a).
Proof.
  intros A P Q R a; split; intro H; [| inversion_clear H];
    [split; intro HP; specialize (H HP); inversion_clear H; auto
    | intro HP; split; auto
    ].
Qed.

Lemma impl_distributes_over_and: forall (P Q R : Prop),
    (P -> Q /\ R) <-> (P -> Q) /\ (P -> R).
Proof.
  intros P Q R; split; intro H; [| inversion_clear H];
    [split; intro HP; specialize (H HP); inversion_clear H; auto
    | intro HP; split; auto
    ].
Qed.
