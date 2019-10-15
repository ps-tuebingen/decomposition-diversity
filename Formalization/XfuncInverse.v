(* Standard library imports *)
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Import ListNotations.
(* Project related imports *)
Require Import LiftComatch.
Require Import DefuncI.
Require Import DefuncII.
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
Require Import DefuncIII.
Require Import RefuncIII.

Fixpoint map_with_index' {A B} (f : nat -> A -> B) (l : list A) (n : nat) : list B :=
  match l with
  | [] => []
  | a::l' => f n a :: map_with_index' f l' (S n)
  end.

Definition map_with_index {A B} (f : nat -> A -> B) (l : list A) : list B :=
  map_with_index' f l 0.

Lemma map_with_index_map : forall {A B} (f : A -> B) (l : list A),
  map f l = map_with_index (fun _ x => f x) l.
Proof with eauto.
intros. unfold map_with_index. generalize 0. induction l; intros... cbn. f_equal...
Qed.

Lemma map_with_index'_length : forall {A B} (f : nat -> A -> B) (l : list A) n,
  length (map_with_index' f l n) = length l.
Proof with eauto.
intros. generalize dependent n. induction l; intros... cbn. f_equal...
Qed.

Lemma with_index_map_map : forall {A B C} (g : nat -> A -> B) (f : nat -> B -> C) (l : list A),
  map_with_index f (map_with_index g l) = map_with_index (fun n x => f n (g n x)) l.
Proof with eauto.
intros. unfold map_with_index. generalize 0. induction l; intros... cbn. f_equal...
Qed.

Lemma with_index'_map_map : forall {A B C} (g : nat -> A -> B) (f : nat -> B -> C) (l : list A) m,
  map_with_index' f (map_with_index g l) m = map_with_index' (fun n x => f n (g (n-m) x)) l m.
Proof with eauto.
intros. unfold map_with_index. replace m with (m + 0) at 1... replace m with (m + 0) at 2...
generalize 0. induction l; intros...
cbn. f_equal.
- f_equal. f_equal. omega.
- replace (S (m + n)) with (m + (S n))...
Qed.

Lemma with_index'_map_map_2 : forall {A B C} (g : nat -> A -> B) (f : B -> C) (l : list A) m,
  map f (map_with_index' g l m) = map_with_index' (fun n x => f (g n x)) l m.
Proof with eauto.
intros. unfold map_with_index. generalize m. induction l; intros... cbn. f_equal...
Qed.

Lemma map_with_index'_cons_n : forall {A B} (f : nat -> A -> B) (l : list A) n,
  map_with_index' f l (S n) = map_with_index' (fun n x => f (S n) x) l n.
Proof with eauto.
intros. unfold map_with_index. generalize dependent n. induction l; intros...
cbn. f_equal...
Qed.

Lemma map_with_index_app : forall {A B C} (g h : nat -> A -> B) (f : nat -> B -> C) (l1 l2 : list A),
  map_with_index f (map_with_index g l1 ++ map_with_index h l2) =
    map_with_index f (map_with_index g l1) ++ map_with_index' f (map_with_index h l2) (length l1).
Proof with eauto.
intros. rewrite <- firstn_skipn with (n:=length l1).
match goal with [|- ?lhs = _] =>
  rewrite <- firstn_skipn with (n:=length l1)(l:=lhs)
end.
f_equal.
- rewrite firstn_app. unfold map_with_index. repeat rewrite map_with_index'_length.
  rewrite Nat.sub_diag. cbn. rewrite app_nil_r. generalize (map_with_index' h l2 0).
  generalize 0. induction l1; intros... cbn. f_equal...
- unfold map_with_index. rewrite <- map_with_index'_length with (l:=l1)(f0:=g)(n:=0).
  rewrite <- map_with_index'_length with (l:=map_with_index' g l1 0)(f0:=f)(n:=0).
  rewrite skipn_all_app. generalize (map_with_index' h l2 0).
  rewrite map_with_index'_length. generalize (map_with_index' g l1 0). clear. intros.
  replace (length l) with (length l + 0) at 2... generalize dependent l0. generalize 0.
  induction l; intros... cbn. replace (S (length l + n)) with (length l + S n)...
Qed.

Lemma map_with_index'_ext_in_aux : forall {A B} (f g : nat -> A -> B) (l : list A) m1 m2,
  (forall a n, In a l -> Some a = nth_error l n -> f (n+m1) a = g (n+m2) a) ->
  map_with_index' f l m1 = map_with_index' g l m2.
Proof with eauto.
intros. generalize dependent m1. generalize dependent m2. induction l; intros... cbn. f_equal.
- replace m1 with (0+m1)... replace m2 with (0+m2)... apply H... left...
- apply IHl. intros. assert (In a0 (a::l)). { right... }
  eapply H with (n:=S n) in H2... replace (n + S m1) with (S n + m1); try omega.
  replace (n + S m2) with (S n + m2); try omega...
Qed.

Lemma map_with_index'_ext_in : forall {A B} (f g : nat -> A -> B) (l : list A) m,
  (forall a n, In a l -> Some a = nth_error l n -> f (n+m) a = g n a) ->
  map_with_index' f l m = map_with_index g l.
Proof with eauto.
intros. unfold map_with_index. apply map_with_index'_ext_in_aux. intros.
replace (n+0) with n...
Qed.

Lemma map_with_index'_ext_in_2 : forall {A B} (f g : nat -> A -> B) (l : list A) m,
  (forall a n, In a l -> Some a = nth_error l n -> f (n+m) a = g (n+m) a) ->
  map_with_index' f l m = map_with_index' g l m.
Proof with eauto.
intros. apply map_with_index'_ext_in_aux...
Qed.

Lemma map_with_index_ext_in : forall {A B} (f g : nat -> A -> B) (l : list A),
  (forall a n, In a l -> Some a = nth_error l n -> f n a = g n a) ->
  map_with_index f l = map_with_index g l.
Proof with eauto.
intros. unfold map_with_index. apply map_with_index'_ext_in_aux.
intros. rewrite Nat.add_0_r...
Qed.

Lemma map_with_index'_irrelevant : forall {A B} (f : A -> B) (l : list A) n,
  map_with_index' (fun _ x => f x) l n = map f l.
Proof with eauto.
intros. generalize dependent n. induction l; intros... cbn. f_equal...
Qed.

Lemma map_with_index_id : forall {A} (l : list A),
  map_with_index (fun (_ : nat) (x : A) => x) l = l.
Proof.
intros. unfold map_with_index. rewrite map_with_index'_irrelevant. apply map_id.
Qed.

Lemma map_with_index'_cons : forall {A B} (f : nat -> A -> B) (l : list A),
  map_with_index' f l 1 = map_with_index (fun n x => f (S n) x) l.
Proof with eauto.
intros. unfold map_with_index. generalize dependent 0. induction l; intros...
cbn. f_equal...
Qed.

Lemma map_with_index'_cons2 : forall {A B} (f : nat -> A -> B) (l : list A),
  map_with_index' f l 2 = map_with_index' (fun n x => f (S n) x) l 1.
Proof with eauto.
intros. unfold map_with_index. generalize dependent 0. induction l; intros...
cbn. f_equal...
Qed.

Lemma map_with_index'_tl : forall {A B} (l : list A) (f : nat -> A -> B),
  map_with_index' f (tl l) 1 = tl (map_with_index f l).
Proof with eauto.
intros. induction l...
Qed.

Lemma map_with_index'_hd : forall {A B} (l : list A) (f : nat -> A -> B) d d',
  l <> [] ->
  f 0 (hd d l) = hd d' (map_with_index f l).
Proof with eauto.
intros. induction l... exfalso. apply H...
Qed.

Remark map_with_index'_empty : forall {A B} (l : list A) (f : nat -> A -> B) n,
  l = [] -> map_with_index' f l n = [].
Proof with eauto. intros. subst... Qed.

Lemma map_with_index_snd_f_combine : forall {A B C} (l1 : list A) (l2 : list B) (f: nat -> B -> C),
    map_with_index (fun n x => (fst x, f n (snd x))) (combine l1 l2) = combine l1 (map_with_index f l2).
Proof.
intros. unfold map_with_index. generalize 0. generalize l2. induction l1.
* intros. simpl. reflexivity.
* intros. destruct l0. simpl. reflexivity. simpl. f_equal. apply IHl1.
Qed.


Definition matrix (A L1 L2 : Type) : Type := (list L1) * (list L2) * (list (list A)).

Fixpoint transpose {A} (m : list (list A)) (n : nat) : list (list A) :=
  match m with
  | [] => repeat [] n
  | l::ls =>
    match l with
    | [] => []
    | a::_ =>
       let m' := transpose ls n in
       map_with_index (fun n l' => (nth n l a)::l') m'
    end
  end.

Definition transpose_matrix {A L1 L2} (m: matrix A L1 L2) : matrix A L2 L1 :=
  match m with (l1, l2, m') => (l2, l1, transpose m' (length l2)) end.


Lemma transpose_distr_aux : forall {A} (l : list (list A)) n,
  Forall (fun x => length x = n) l ->
  tl (transpose l n) = transpose (map (@tl _) l) (n-1).
Proof with eauto.
intros. generalize dependent n.
assert (length l <= length l) as Len...
generalize Len. clear Len. generalize (length l) at 2.
generalize dependent l. intros l n. generalize dependent l.
induction n; intros.
- cbn. destruct l; simpl in Len; [|omega]. cbn. destruct n...
  simpl. rewrite Nat.sub_0_r...
- destruct l.
  + cbn. destruct n0... simpl. rewrite Nat.sub_0_r...
  + cbn. destruct l... cbn - [nth]. destruct l0.
    * cbn - [nth]. destruct l.
      -- inversion H; subst...
      -- destruct n0... replace (S n0 - 1) with n0; try omega.
         cbn - [nth]. rewrite map_with_index'_cons. unfold map_with_index.
         apply map_with_index'_ext_in_2. intros.
         cbn. replace (n1+0) with n1; try omega.
         destruct n1... f_equal. apply nth_indep.
         inversion H; subst. simpl in H4.
         assert (Some a1 <> None). { unfold not. intros. discriminate. }
         rewrite H1 in H2. rewrite nth_error_Some in H2.
         inversion H4; subst. rewrite repeat_length in H2. omega.
    * destruct l.
      -- cbn. destruct l0... inversion H; subst. inversion H3; subst.
         cbn in H4. clear - H4. rewrite map_with_index'_ext_in with
           (g:=fun n l' => a::l').
         2:{ intros. destruct n... destruct n... }
         rewrite with_index_map_map. rewrite <- map_with_index'_tl.
         assert (forall {A B} (l : list A) (f : A -> B),
           map f l = [] -> l = []).
         { intros. destruct l... cbn in H. discriminate. }
         apply H with (f:=@tl _).
         rewrite with_index'_map_map_2. cbn [tl].
         generalize dependent a0. generalize dependent l0. generalize dependent a.
         induction l1; intros...
         cbn [length] in *. cbn - [nth]. destruct a...
         rewrite <- map_with_index'_tl.
         rewrite IHl1... inversion H4; subst...
      -- cbn - [nth]. destruct l0... cbn [tl]. destruct l0.
         ++ inversion H; subst. inversion H3; subst. discriminate.
         ++ match goal with [|- _ _ (map_with_index' ?f ?lhs 0) = _] =>
              replace (map_with_index' f lhs 0) with (map_with_index f lhs) end...
            rewrite <- map_with_index'_tl. rewrite <- map_with_index'_tl.
            do 2 rewrite map_with_index'_cons. rewrite with_index_map_map.
            rewrite with_index'_map_map.
            match goal with [|- _ = map_with_index' ?f ?lhs 0] =>
              replace (map_with_index' f lhs 0) with (map_with_index f lhs) end...
            rewrite IHn.
            2:{ simpl in Len. omega. }
            2:{ inversion H; subst. inversion H3; subst... }
            apply map_with_index_ext_in. intros. cbn. f_equal.
            ** destruct n1... apply nth_indep.
               assert (length (transpose (map (tl (A:=A)) l1) (n0 - 1)) = n0 - 1).
               { inversion H; subst. inversion H5; subst. clear - H6. simpl in *.
                 generalize dependent (length l). intros. clear - H6. induction l1.
                 - cbn. rewrite repeat_length...
                 - cbn. inversion H6; subst. destruct a; try discriminate. destruct a0; try discriminate.
                   simpl. unfold map_with_index. rewrite map_with_index'_length...
               }
               assert (nth_error (transpose (map (tl (A:=A)) l1) (n0 - 1)) (S n1) <> None).
               { unfold not. intros. rewrite H3 in H1. discriminate. }
               rewrite nth_error_Some in H3. rewrite H2 in H3. inversion H; subst.
               simpl in H3. omega.
            ** rewrite Nat.sub_0_r. destruct n1... f_equal. apply nth_indep.
               assert (length (transpose (map (tl (A:=A)) l1) (n0 - 1)) = n0 - 1).
               { inversion H; subst. inversion H5; subst. clear - H6. simpl in *.
                 generalize dependent (length l). intros. clear - H6. induction l1.
                 - cbn. rewrite repeat_length...
                 - cbn. inversion H6; subst. destruct a; try discriminate. destruct a0; try discriminate.
                   simpl. unfold map_with_index. rewrite map_with_index'_length...
               }
               assert (nth_error (transpose (map (tl (A:=A)) l1) (n0 - 1)) (S n1) <> None).
               { unfold not. intros. rewrite H3 in H1. discriminate. }
               rewrite nth_error_Some in H3. rewrite H2 in H3. inversion H; subst.
               inversion H7; subst. rewrite <- H6 in H3. simpl in H3. omega.
Qed.

Lemma transpose_distr_aux_hd : forall {A} (l : list (list A)) n d,
  Forall (fun x => length x = n) l ->
  hd (repeat d (length l)) (transpose l n) = map (hd d) l.
Proof with eauto.
intros. generalize dependent n.
assert (length l <= length l) as Len...
generalize Len. clear Len. generalize (length l) at 2.
generalize dependent l. intros l n. generalize dependent l.
induction n; intros.
- cbn. destruct l; simpl in Len; [|omega]. cbn. destruct n...
- destruct l.
  + cbn. destruct n0...
  + cbn. destruct l.
    * cbn. f_equal. inversion H; subst. clear - H3. cbn in H3.
      induction l0... cbn. inversion H3; subst. rewrite IHl0... f_equal.
      destruct a; try discriminate...
    * cbn - [nth]. destruct l0.
      -- cbn - [nth]. destruct n0... inversion H; subst. discriminate.
      -- cbn - [nth]. destruct l0.
         ++ inversion H; subst. inversion H3; subst. discriminate.
         ++ rewrite with_index'_map_map.
            match goal with [|- _ _ (map_with_index' ?f ?lhs 0) = _] =>
              replace (map_with_index' f lhs 0) with (map_with_index f lhs) end...
            rewrite <- map_with_index'_hd with (d0:=(repeat d (length l1))).
            2:{ destruct n0. {  inversion H; subst. simpl in H2. discriminate. }
              inversion H; subst. inversion H3; subst.
              clear - H5. generalize dependent n0. induction l1; intros; cbn.
              - unfold not. intros. discriminate.
              - inversion H5; subst. destruct a; try discriminate.
                case_eq (transpose l1 (S n0)); intros.
                + specialize IHl1 with (n0:=n0). rewrite <- H in IHl1. exfalso.
                  apply IHl1...
                + cbn. unfold not. intros. discriminate.
            }
            repeat f_equal. simpl in Len. apply IHn; [omega|]. inversion H; subst.
            inversion H3; subst...
Qed.

Lemma transpose_prepend_aux : forall {A} l (l0 : list A) m a,
  Forall (fun x : list A => length x = m) l ->
  length l0 = length l + 1 ->
  transpose (map_with_index' (fun (n0 : nat) (l' : list A) => nth n0 l0 a :: l') l 1) (S m)
  = (tl l0) :: transpose l m.
Proof with eauto.
intros A l l0 m a Len. intros.
match goal with [|- _ ?lhs _ = _] => case_eq lhs; intros end.
- cbn. destruct l.
  + destruct l0; simpl in H; [omega|]. cbn. destruct l0; try discriminate...
  + cbn in H0. discriminate.
- cbn. destruct l1.
  + destruct l; discriminate.
  + case_eq (transpose l2 (S m)); intros.
    * exfalso. destruct l; try discriminate. cbn in H0. inversion H0; subst.
      assert (length
        (transpose (map_with_index' (fun (n0 : nat) (l' : list A) => nth n0 l0 a :: l') l3 2) (S m))
        > 0).
      { clear - Len. inversion Len; subst. clear - H2. generalize 2. induction l3; intros.
        - cbn. omega.
        - cbn. unfold map_with_index. rewrite map_with_index'_length. apply IHl3. inversion H2...
      }
      rewrite H1 in H2. cbn in H2. omega.
    * cbn - [nth]. f_equal.
      -- evar (d : A). replace l3 with (hd (repeat d (length l2)) (transpose l2 (S m))).
         2:{ rewrite H1... }
         rewrite transpose_distr_aux_hd with (d0:=d).
         2:{ destruct l; try discriminate. cbn in H0. inversion H0; subst.
           inversion Len; subst. clear - H5. rewrite Forall_forall in *. intros.
           assert (x <> []) as NonEmpty.
           { clear - H. apply (in_map (@length _)) in H. rewrite with_index'_map_map_2 in H.
             cbn in H. rewrite map_with_index'_cons2 in H. rewrite map_with_index'_cons in H.
             rewrite <- map_with_index_map in H. rewrite in_map_iff in H. do 2 destruct H.
             destruct x; discriminate.
           }
           apply (in_map (@tl _)) in H. rewrite with_index'_map_map_2 in H.
           cbn in H. rewrite map_with_index'_cons2 in H. rewrite map_with_index'_cons in H.
           rewrite <- map_with_index_map in H. rewrite map_id in H. apply H5 in H.
           destruct x. { exfalso. apply NonEmpty... } cbn in *...
         }
         cbn. apply (f_equal (map (hd d))) in H0. cbn in H0. rewrite <- H0.
         rewrite with_index'_map_map_2. cbn. rewrite map_with_index'_cons.
         destruct l0; simpl in H; try omega. clear - H. cbn. generalize dependent l0.
         induction l; intros.
         ++ cbn. destruct l0; simpl in H; try omega...
         ++ cbn. destruct l0; simpl in H; try omega. f_equal.
            rewrite map_with_index'_cons. cbn...
      -- apply (f_equal (map (@tl _))) in H0. cbn in H0.
         rewrite with_index'_map_map_2 in H0. cbn in H0. destruct l.
         ++ cbn in H0. discriminate.
         ++ cbn in H0. inversion H0; subst. rewrite map_with_index'_cons2 in H4.
            rewrite map_with_index'_cons in H4. unfold map_with_index in H4.
            rewrite map_with_index'_irrelevant in H4. rewrite map_id in H4. subst l5.
            destruct l1.
            ** cbn - [nth]. destruct l4... inversion Len; subst.
               clear - H1 H5.
               exfalso. cbn in *. clear - H1 H5.
               assert (Forall (fun x => length x <= 1) l2).
               { clear - H5. induction l2... inversion H5; subst. constructor... destruct a...
                 cbn in H1. cbn. rewrite H1...
               }
               clear - H H1.
               assert (length (transpose l2 1) <= 1).
               { clear - H. induction l2... inversion H; subst.
                 cbn. destruct a... unfold map_with_index. rewrite map_with_index'_length...
               }
               rewrite H1 in H0. cbn in H0. omega.
            ** rewrite map_with_index'_cons. cbn - [transpose].
               apply (f_equal (@tl _)) in H1. cbn in H1. subst l4.
               cbn. match goal with [|- _ _ ?lhs = _ _ ?rhs] => replace lhs with rhs end.
               { apply map_with_index_ext_in. intros. f_equal. destruct n...
                 apply nth_indep.
                 assert (length (transpose (map (tl (A:=A)) l2) m) = m).
                 { inversion H; subst. inversion Len; subst. clear - H7. simpl in *.
                   generalize dependent (length l1). intros. clear - H7. induction l2.
                   - cbn. rewrite repeat_length...
                   - cbn. inversion H7; subst. destruct a; try discriminate. destruct a0; try discriminate.
                     simpl. unfold map_with_index. rewrite map_with_index'_length...
                 }
                 assert (nth_error (transpose (map (tl (A:=A)) l2) m) (S n) <> None).
                 { unfold not. intros. rewrite H4 in H2. discriminate. }
                 rewrite nth_error_Some in H4. rewrite H3 in H4. inversion Len; subst.
                 simpl in H4. omega.
               }
               replace m with (S m - 1) at 1; try omega. symmetry. apply transpose_distr_aux.
               inversion Len; subst. clear - H4. cbn in *. generalize dependent (length l1).
               intros. induction l2... inversion H4; subst. constructor.
               --- destruct a; try discriminate. cbn in *. rewrite H1...
               --- apply IHl2...
Unshelve. all:auto.
Qed.

Fact nth_error_nth : forall {A} n0 l (x d : A),
  nth_error l n0 = Some x -> nth n0 l d = x.
Proof with eauto.
intros. generalize dependent n0. induction l; intros.
- destruct n0; simpl in H; discriminate.
- destruct n0; simpl in H; try inversion H...
Qed.

Lemma transpose_transpose : forall {A L1 L2} (m : matrix A L1 L2),
  length (fst (fst m)) = length (snd m) ->
  Forall (fun l => length l = length (snd (fst m))) (snd m) ->
  transpose_matrix (transpose_matrix m) = m.
Proof with eauto.
intros. destruct m. destruct p. simpl in *. f_equal. rewrite H.
generalize dependent (length l1). clear. intros.
rename n into n'. remember (length l) as n. generalize dependent l.
generalize dependent n'.
induction n; intros.
- destruct l; try discriminate. cbn. destruct n'...
- destruct l; try discriminate. cbn. destruct l.
  + cbn. f_equal. inversion H0; subst. simpl in Heqn. inversion Heqn; subst.
    clear - H3. induction l0... inversion H3; subst. destruct a; try discriminate.
    simpl. f_equal. apply IHl0...
  + match goal with [|- transpose ?lhs _ = _] => case_eq lhs; intros end.
    * assert (transpose l0 n' <> []).
      { clear - H0. induction l0.
        - cbn. inversion H0; subst. cbn. unfold not. intros. discriminate.
        - cbn. inversion H0; subst. inversion H3; subst. rewrite Forall_forall in IHl0.
          assert (transpose l0 (length (a :: l)) <> []).
          { apply IHl0. intros. destruct H. { rewrite H... } rewrite Forall_forall in H4... }
          case_eq (transpose l0 (length (a :: l))); intros...
          destruct a0; discriminate.
      }
      case_eq (transpose l0 n'); intros... { rewrite H2 in H1. exfalso... } rewrite H2 in H. discriminate.
    * pose proof H as H'. apply (f_equal (@tl _)) in H. cbn [tl] in H. subst l2.
      rewrite <- map_with_index'_tl. rewrite transpose_distr_aux.
      2:{ inversion H0... }
      cbn [transpose]. rewrite transpose_prepend_aux.
      2:{ cbn in Heqn. inversion Heqn; subst.
        clear - H0. cbn in H0. inversion H0; subst. clear - H3. cbn in *. rewrite Nat.sub_0_r.
        generalize dependent (length l). intros.
        induction l0; intros.
        - cbn. induction n; cbn...
        - cbn. destruct a0; cbn... destruct a1... rewrite Forall_forall. intros.
          inversion H3; subst. apply IHl0 in H4. apply (in_map (@length _)) in H.
          rewrite map_with_index_map in H. rewrite with_index_map_map in H.
          cbn in H. rewrite <- map_with_index_map in H. rewrite in_map_iff in H.
          do 2 destruct H. rewrite <- H. rewrite Forall_forall in H4.
          apply H4 in H0...
      }
      2:{ cbn. rewrite Nat.add_1_r. f_equal. inversion H0; subst. cbn. rewrite Nat.sub_0_r.
        clear - H3. cbn in H3. generalize dependent l. induction l0; intros.
        - cbn. rewrite repeat_length...
        - cbn. destruct a0. { inversion H3; subst. discriminate. } cbn.
          destruct a1. { inversion H3; subst. simpl in H1. simpl. omega. }
          unfold map_with_index. rewrite map_with_index'_length. apply IHl0.
          inversion H3; subst...
      }
      replace (S n - 1) with n; [| omega]. rewrite IHn.
      2:{ clear - H0. induction l0. { cbn. constructor. } cbn. constructor.
        - clear - H0. inversion H0; subst. inversion H3; subst. destruct a0; try discriminate.
          cbn. inversion H2; subst. omega.
        - apply IHl0. inversion H0; subst. inversion H3; subst. constructor...
      }
      2:{ rewrite map_length. inversion Heqn... }
      cbn [tl]. destruct l1.
      -- case_eq (transpose l0 n'); intros.
         ** rewrite H in H'. cbn in H'. discriminate.
         ** rewrite H in H'. cbn in H'. inversion H'.
      -- cbn - [nth]. rewrite map_with_index'_cons. cbn. rewrite map_with_index_map.
         rewrite with_index_map_map. f_equal; f_equal.
         ++ case_eq (transpose l0 n'); intros.
            ** rewrite H in H'. cbn in H'. discriminate.
            ** rewrite H in H'. cbn in H'. inversion H'...
         ++ rewrite <- map_id. rewrite map_with_index_map. apply map_with_index_ext_in.
            intros. unfold id.
            apply (f_equal (map (@tl _))) in H'.
            cbn - [nth] in H'. rewrite map_with_index_map in H'. rewrite with_index_map_map in H'.
            cbn - [nth] in H'. rewrite map_with_index_id in H'. destruct l0; [inversion H|].
            replace (l0::l2) with
              (map_with_index' (fun (n0 : nat) (l' : list A) => nth n0 (map (hd a) ([]::l0::l2)) a :: l')
                 (map (@tl _) (l0::l2)) 1) in H'.
            2:{ do 2 rewrite map_with_index_map. rewrite with_index'_map_map. rewrite <- map_with_index_map.
              cbn. destruct l0. 1:{ clear - H0. inversion H0; subst. inversion H3; subst. discriminate. }
              cbn. f_equal. clear - H0. rewrite <- map_id. do 2 rewrite map_with_index_map.
              rewrite map_with_index'_cons2. rewrite map_with_index'_cons.
              apply map_with_index_ext_in. intros. rewrite <- map_with_index_map.
              destruct a0.
              { inversion H0; subst. inversion H5; subst. rewrite Forall_forall in H6. apply H6 in H. discriminate. }
              unfold id. cbn. erewrite nth_indep.
              - rewrite map_nth. erewrite nth_error_nth... cbn...
              - rewrite map_length. rewrite <- nth_error_Some. rewrite <- H1. unfold not. intros.
                discriminate.
            }
            inversion H0; subst. cbn [length] in H'.
            rewrite transpose_prepend_aux in H'.
            2:{ clear - H5. cbn in H5. generalize dependent (l0::l2). intros.
              generalize dependent (length l). intros. induction l1; cbn... constructor.
              - inversion H5; subst. destruct a0; try discriminate. cbn...
              - apply IHl1. inversion H5...
            }
            2:{ repeat rewrite map_length. simpl. omega. }
            inversion H'. clear H4.
            replace (hd a l0 :: map (hd a) l2) with (map (hd a) (l0::l2))...
            erewrite nth_indep.
            ** rewrite map_nth. symmetry in H1. erewrite nth_error_nth...
               destruct a1... clear - H H0. exfalso. generalize dependent (l0::l2). intros.
               inversion H0; subst. rewrite Forall_forall in H4. apply H4 in H. discriminate.
            ** rewrite map_length. rewrite <- nth_error_Some. rewrite <- H1. unfold not. intros.
               discriminate.
Unshelve. all:auto.
Qed.


Definition scoped_gfun_bod_named : Type := ScopedName * gfun_bod.
Definition scoped_gfun_bods := list scoped_gfun_bod_named.

Definition scoped_cfun_bod_named : Type := ScopedName * cfun_bod.
Definition scoped_cfun_bods := list scoped_cfun_bod_named.


Definition program_matrix := matrix expr ScopedName ScopedName.

Definition read_gfuns_into_matrix (gfbs : scoped_gfun_bods) : program_matrix :=
  (map fst gfbs, match gfbs with [] => [] | l::_ => map fst (snd l) end, map (fun x => map snd x) (map snd gfbs)).

Definition read_cfuns_into_matrix (cfbs : scoped_cfun_bods) : program_matrix :=
  (map fst cfbs, match cfbs with [] => [] | l::_ => map fst (snd l) end, map (fun x => map snd x) (map snd cfbs)).


Definition read_gfuns_from_matrix (m : program_matrix) : scoped_gfun_bods :=
  match m with
  | (l1, l2, m') => combine l1 (map (combine l2) m')
  end.

Definition read_cfuns_from_matrix (m : program_matrix) : scoped_cfun_bods :=
  match m with
  | (l1, l2, m') => combine l1 (map (combine l2) m')
  end.

Lemma read_gfuns_into_from_matrix : forall gfbs,
  (forall gfb1 gfb2, In gfb1 gfbs -> In gfb2 gfbs -> map fst (snd gfb1) = map fst (snd gfb2)) ->
  read_gfuns_from_matrix (read_gfuns_into_matrix gfbs) = gfbs.
Proof with eauto.
intros. destruct gfbs... unfold read_gfuns_into_matrix. unfold read_gfuns_from_matrix.
match goal with [|- combine _ ?lhs = _] => assert (lhs = map snd (p::gfbs)) end.
- rewrite map_map. rewrite map_ext_in with (g:=id); [rewrite map_id|]...
  intros. assert (Aux: exists a', In (a',a) (p::gfbs)).
  + rewrite combine_fst_snd with (ps:=p::gfbs).
    apply combine_in... repeat rewrite map_length...
  + destruct Aux as [a' Aux]. erewrite H...
    * simpl. rewrite <- combine_fst_snd...
    * apply in_eq.
- rewrite H0. rewrite <- combine_fst_snd...
Qed.

Lemma read_gfuns_from_into_matrix : forall m,
  snd m <> [] ->
  length (fst (fst m)) = length (snd m) ->
  (forall l', In l' (snd m) -> length (snd (fst m)) = length l') ->
  read_gfuns_into_matrix (read_gfuns_from_matrix m) = m.
Proof with eauto.
intros. destruct m. destruct p. unfold read_gfuns_into_matrix. unfold read_gfuns_from_matrix.
rewrite map_map. f_equal; try f_equal.
- rewrite map_fst_combine... rewrite map_length...
- cbn in *. destruct l; [exfalso; apply H |]...
  case_eq (combine l0 (map (combine l1) (l :: l2))); intros.
  + destruct l0; discriminate.
  + destruct l0; try discriminate. cbn in H2. inversion H2; subst. cbn.
    rewrite map_fst_combine... apply H1. left...
- cbn in *. rewrite <- map_map. rewrite map_snd_combine.
  + rewrite map_map. rewrite <- map_id. apply map_ext_in. intros. rewrite map_snd_combine...
  + rewrite map_length...
Qed.

Lemma read_cfuns_into_from_matrix : forall cfbs,
  (forall cfb1 cfb2, In cfb1 cfbs -> In cfb2 cfbs -> map fst (snd cfb1) = map fst (snd cfb2)) ->
  read_cfuns_from_matrix (read_cfuns_into_matrix cfbs) = cfbs.
Proof with eauto.
intros. destruct cfbs... unfold read_cfuns_into_matrix. unfold read_cfuns_from_matrix.
match goal with [|- combine _ ?lhs = _] => assert (lhs = map snd (p::cfbs)) end.
- rewrite map_map. rewrite map_ext_in with (g:=id); [rewrite map_id|]...
  intros. assert (Aux: exists a', In (a',a) (p::cfbs)).
  + rewrite combine_fst_snd with (ps:=p::cfbs).
    apply combine_in... repeat rewrite map_length...
  + destruct Aux as [a' Aux]. erewrite H...
    * simpl. rewrite <- combine_fst_snd...
    * apply in_eq.
- rewrite H0. rewrite <- combine_fst_snd...
Qed.

Lemma read_cfuns_from_into_matrix : forall m,
  snd m <> [] ->
  length (fst (fst m)) = length (snd m) ->
  (forall l', In l' (snd m) -> length (snd (fst m)) = length l') ->
  read_cfuns_into_matrix (read_cfuns_from_matrix m) = m.
Proof with eauto.
intros. destruct m. destruct p. unfold read_cfuns_into_matrix. unfold read_cfuns_from_matrix.
rewrite map_map. f_equal; try f_equal.
- rewrite map_fst_combine... rewrite map_length...
- cbn in *. destruct l; [exfalso; apply H |]...
  case_eq (combine l0 (map (combine l1) (l :: l2))); intros.
  + destruct l0; discriminate.
  + destruct l0; try discriminate. cbn in H2. inversion H2; subst. cbn.
    rewrite map_fst_combine... apply H1. left...
- cbn in *. rewrite <- map_map. rewrite map_snd_combine.
  + rewrite map_map. rewrite <- map_id. apply map_ext_in. intros. rewrite map_snd_combine...
  + rewrite map_length...
Qed.



Definition program_gfun_bods_for_type (tn : TypeName) (p : program) :=
  filter (fun x => eq_TypeName (fst (unscope (fst x))) tn)
    (map (fun x => (global (fst x), snd x)) (program_gfun_bods_g p) ++
     map (fun x => (local (fst x), snd x)) (program_gfun_bods_l p)).

Definition program_cfun_bods_for_type (tn : TypeName) (p : program) :=
  filter (fun x => eq_TypeName (fst (unscope (fst x))) tn)
    (map (fun x => (global (fst x), snd x)) (program_cfun_bods_g p) ++
     map (fun x => (local (fst x), snd x)) (program_cfun_bods_l p)).

Definition program_gfun_bods (p : program) :=
  map (fun x => (global (fst x), snd x)) (program_gfun_bods_g p) ++
  map (fun x => (local (fst x), snd x)) (program_gfun_bods_l p).

Definition program_cfun_bods (p : program) :=
  map (fun x => (global (fst x), snd x)) (program_cfun_bods_g p) ++
  map (fun x => (local (fst x), snd x)) (program_cfun_bods_l p).


Definition defunc_term_helper (p : skeleton) (tn : TypeName) (dname : ScopedName) (cname : ScopedName) (e : expr) : expr :=
  let dlength := lookup_dtor p dname >>= fun x => Some (length (snd (fst x))) in
  match dlength with
  | Some n => DefuncIII.switch_indices_aux p cname n tn e
  | None => e
  end.

Definition refunc_term_helper (p : skeleton) (tn : TypeName) (dname : ScopedName) (cname : ScopedName) (e : expr) : expr :=
  let clength := lookup_ctor_sig p cname >>= fun x => Some (length (snd x)) in
  match clength with
  | Some n => RefuncIII.switch_indices_aux p dname n tn e
  | None => e
  end.


Lemma derefunc_exp_inverse : forall p tn e
  (DefuncCdt : forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn)
  (DefuncCdt2 : In tn (skeleton_cdts (program_skeleton p)))
  (InProg : In e (map snd (flat_map snd (program_gfun_bods p))) \/ In e (map snd (flat_map snd (program_cfun_bods p)))
     \/ In e (map snd (program_fun_bods p))),
  refunctionalize_expr tn (defunctionalize_expr tn e) = e.
Proof with eauto.
intros.
assert (Sub : exists e', (In e' (map snd (flat_map snd (program_gfun_bods p))) \/
  In e' (map snd (flat_map snd (program_cfun_bods p))) \/ In e' (map snd (program_fun_bods p))) /\
  subterm e e'). { exists e. split... constructor. }
clear InProg.
induction e using expr_strong_ind; intros...
- cbn. case_eq (eq_TypeName tn (fst (unscope n))); intros.
  + exfalso. unfold not in DefuncCdt.
    assert (exists cargs, In (n, cargs) (skeleton_ctors (program_skeleton p))).
    { destruct Sub. destruct H1. destruct H1; [ | destruct H1 ].
      - rewrite in_map_iff in H1. destruct H1. destruct H1.
        rewrite in_flat_map in H3. do 2 destruct H3. unfold program_gfun_bods in H3.
        apply in_app_or in H3. destruct H3.
        + rewrite in_map_iff in H3. do 2 destruct H3.
          pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
          rewrite Forall_forall in TypG. apply TypG in H5. destruct H5 as [qn [args [SigLookup Typ]]].
          subst. cbn in *. destruct x0.
          assert (Sub : subterm (E_Constr n ls) (E_CoMatch (fst x2) (index_list 0 args) (snd x2))).
          { eapply Sub_Trans... cbn. apply Sub_CoMatch_cocases. apply in_map with (f:=snd) in H4... }
          pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
          clear - TypSub. destruct TypSub. destruct H. inversion H; subst. exists cargs...
        + rewrite in_map_iff in H3. do 2 destruct H3.
          pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
          rewrite Forall_forall in TypL. apply TypL in H5. destruct H5 as [qn [args [SigLookup Typ]]].
          subst. cbn in *. destruct x0.
          assert (Sub : subterm (E_Constr n ls) (E_CoMatch (fst x2) (index_list 0 args) (snd x2))).
          { eapply Sub_Trans... cbn. apply Sub_CoMatch_cocases. apply in_map with (f:=snd) in H4... }
          pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
          clear - TypSub. destruct TypSub. destruct H. inversion H; subst. exists cargs...
      - rewrite in_map_iff in H1. destruct H1. destruct H1.
        rewrite in_flat_map in H3. do 2 destruct H3. unfold program_cfun_bods in H3.
        apply in_app_or in H3. destruct H3.
        + rewrite in_map_iff in H3. do 2 destruct H3.
          pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
          rewrite Forall_forall in TypG. apply TypG in H5. destruct H5 as [qn [args [t [SigLookup Typ]]]].
          subst. cbn in *. destruct x0.
          assert (Sub : subterm (E_Constr n ls) (E_Match (fst x2) (E_Var 0) (index_list 1 args) (snd x2) t)).
          { eapply Sub_Trans... cbn. apply Sub_Match_cases. apply in_map with (f:=snd) in H4... }
          pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
          clear - TypSub. destruct TypSub. destruct H. inversion H; subst. exists cargs...
        + rewrite in_map_iff in H3. do 2 destruct H3.
          pose proof (program_cfun_bods_typecheck_l p) as TypG. unfold cfun_bods_l_typecheck in TypG.
          rewrite Forall_forall in TypG. apply TypG in H5. destruct H5 as [qn [args [t [SigLookup Typ]]]].
          subst. cbn in *. destruct x0.
          assert (Sub : subterm (E_Constr n ls) (E_Match (fst x2) (E_Var 0) (index_list 1 args) (snd x2) t)).
          { eapply Sub_Trans... cbn. apply Sub_Match_cases. apply in_map with (f:=snd) in H4... }
          pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
          clear - TypSub. destruct TypSub. destruct H. inversion H; subst. exists cargs...
      - rewrite in_map_iff in H1. destruct H1. destruct H1.
        pose proof (program_fun_bods_typecheck p) as TypF. unfold fun_bods_typecheck in TypF.
        rewrite Forall_forall in TypF. apply TypF in H3. destruct H3 as [qn [args [t [SigLookup Typ]]]].
        subst. cbn in *. destruct x0. cbn in *.
        pose proof (subterm_typechecks _ _ _ _ _ Typ H2) as TypSub.
        clear - TypSub. destruct TypSub. destruct H. inversion H; subst. exists cargs...
    }
    destruct H1. eapply DefuncCdt...
    cbn. rewrite eq_TypeName_eq in H0...
  + f_equal. clear - H Sub.
    assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H0. generalize dependent H. generalize ls at - 3.
    induction ls0; intros...
    cbn. inversion H; subst. f_equal.
    * apply H3. clear - Sub H0. destruct Sub. exists x. destruct H. split...
      destruct H0. eapply subterm_switch_Trans... apply Sub_Constr. subst.
      apply in_or_app. right. left...
    * apply IHls0... clear - H0. destruct H0. exists (x++[a]). rewrite <- app_assoc...
- cbn. case_eq (eq_TypeName tn (fst (unscope n))); intros.
  + cbn. rewrite H0. f_equal.
    * apply IHe. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans... constructor.
    * assert (exists ls', ls' ++ ls = ls). { exists []... }
      generalize dependent H1. generalize dependent H. generalize ls at - 3.
      induction ls0; intros... cbn. inversion H; subst. f_equal.
      -- apply H4. destruct Sub. destruct H2. exists x. split... eapply subterm_switch_Trans...
         constructor. destruct H1. subst. apply in_or_app. right. left...
      -- apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
  + cbn. f_equal.
    * apply IHe. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans... constructor.
    * assert (exists ls', ls' ++ ls = ls). { exists []... }
      generalize dependent H1. generalize dependent H. generalize ls at - 3.
      induction ls0; intros... cbn. inversion H; subst. f_equal.
      -- apply H4. destruct Sub. destruct H2. exists x. split... eapply subterm_switch_Trans...
         constructor. destruct H1. subst. apply in_or_app. right. left...
      -- apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal...
  assert (exists ls', ls' ++ ls = ls). { exists []... }
  generalize dependent H0. generalize dependent H. generalize ls at - 3.
  induction ls0; intros... cbn. inversion H; subst. f_equal.
  + apply H3. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans...
    constructor. destruct H0. subst. apply in_or_app. right. left...
  + apply IHls0... destruct H0. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. case_eq (eq_TypeName tn (fst (unscope sn))); intros.
  + exfalso.
    destruct Sub. destruct H1. destruct H1; [ | destruct H1 ].
    * rewrite in_map_iff in H1. destruct H1. destruct H1.
      rewrite in_flat_map in H3. do 2 destruct H3. unfold program_gfun_bods in H3.
      apply in_app_or in H3. destruct H3.
      -- pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
         rewrite Forall_forall in TypG.
         rewrite in_map_iff in H3. do 2 destruct H3.
         apply TypG in H5. destruct H5 as [qn [args [SigLookup Typ]]].
         subst. cbn in *. destruct x0.
         assert (Sub : subterm (E_ConsFunCall sn e ls) (E_CoMatch (fst x2) (index_list 0 args) (snd x2))).
         { eapply Sub_Trans... cbn. apply Sub_CoMatch_cocases. apply in_map with (f:=snd) in H4... }
         pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
         destruct TypSub as [ctx' [t' TypSub]]. inversion TypSub; subst.
         ++ pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as SigInDt.
            unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
            apply SigInDt in H8. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - DefuncCdt2 H8.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
         ++ pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as SigInDt.
            unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
            apply SigInDt in H8. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - DefuncCdt2 H8.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
      -- pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
         rewrite Forall_forall in TypL.
         rewrite in_map_iff in H3. do 2 destruct H3.
         apply TypL in H5. destruct H5 as [qn [args [SigLookup Typ]]].
         subst. cbn in *. destruct x0.
         assert (Sub : subterm (E_ConsFunCall sn e ls) (E_CoMatch (fst x2) (index_list 0 args) (snd x2))).
         { eapply Sub_Trans... cbn. apply Sub_CoMatch_cocases. apply in_map with (f:=snd) in H4... }
         pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
         destruct TypSub as [ctx' [t' TypSub]]. inversion TypSub; subst.
         ++ pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as SigInDt.
            unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
            apply SigInDt in H8. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - DefuncCdt2 H8.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
         ++ pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as SigInDt.
            unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
            apply SigInDt in H8. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - DefuncCdt2 H8.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
    * rewrite in_map_iff in H1. destruct H1. destruct H1.
      rewrite in_flat_map in H3. do 2 destruct H3. unfold program_cfun_bods in H3.
      apply in_app_or in H3. destruct H3.
      -- pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
         rewrite Forall_forall in TypG.
         rewrite in_map_iff in H3. do 2 destruct H3.
         apply TypG in H5. destruct H5 as [qn [args [t [SigLookup Typ]]]].
         subst. cbn in *. destruct x0.
         assert (Sub : subterm (E_ConsFunCall sn e ls) (E_Match (fst x2) (E_Var 0) (index_list 1 args) (snd x2) t)).
         { eapply Sub_Trans... cbn. apply Sub_Match_cases. apply in_map with (f:=snd) in H4... }
         pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
         destruct TypSub as [ctx' [t' TypSub]]. inversion TypSub; subst.
         ++ pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as SigInDt.
            unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
            apply SigInDt in H8. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - DefuncCdt2 H8.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
         ++ pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as SigInDt.
            unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
            apply SigInDt in H8. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - DefuncCdt2 H8.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
      -- pose proof (program_cfun_bods_typecheck_l p) as TypG. unfold cfun_bods_l_typecheck in TypG.
         rewrite Forall_forall in TypG.
         rewrite in_map_iff in H3. do 2 destruct H3.
         apply TypG in H5. destruct H5 as [qn [args [t [SigLookup Typ]]]].
         subst. cbn in *. destruct x0.
         assert (Sub : subterm (E_ConsFunCall sn e ls) (E_Match (fst x2) (E_Var 0) (index_list 1 args) (snd x2) t)).
         { eapply Sub_Trans... cbn. apply Sub_Match_cases. apply in_map with (f:=snd) in H4... }
         pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
         destruct TypSub as [ctx' [t' TypSub]]. inversion TypSub; subst.
         ++ pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as SigInDt.
            unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
            apply SigInDt in H8. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - DefuncCdt2 H8.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
         ++ pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as SigInDt.
            unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
            apply SigInDt in H8. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - DefuncCdt2 H8.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
    * rewrite in_map_iff in H1. destruct H1. destruct H1.
      pose proof (program_fun_bods_typecheck p) as TypF. unfold fun_bods_typecheck in TypF.
      rewrite Forall_forall in TypF. apply TypF in H3. destruct H3 as [qn [args [t [SigLookup Typ]]]].
      subst. cbn in *. destruct x0. cbn in *.
      pose proof (subterm_typechecks _ _ _ _ _ Typ H2) as TypSub.
      clear - DefuncCdt2 TypSub H0. destruct TypSub. destruct H. inversion H; subst.
      -- pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as SigInDt.
         unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
         apply SigInDt in H6. cbn in *. rewrite eq_TypeName_eq in *. subst.
         pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
         unfold dts_cdts_disjoint in Disj. unfold not in Disj. cbn in *.
         apply Disj with (t:=fst qn). split...
      -- pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as SigInDt.
         unfold cfun_sigs_in_dts in SigInDt. rewrite Forall_forall in SigInDt.
         apply SigInDt in H6. cbn in *. rewrite eq_TypeName_eq in *. subst.
         pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
         unfold dts_cdts_disjoint in Disj. unfold not in Disj. cbn in *.
         apply Disj with (t:=fst qn). split...
  + f_equal.
    * apply IHe. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans... constructor.
    * assert (exists ls', ls' ++ ls = ls). { exists []... }
      generalize dependent H1. generalize dependent H. generalize ls at - 3.
      induction ls0; intros... cbn. inversion H; subst. f_equal.
      -- apply H4. destruct Sub. destruct H2. exists x. split... eapply subterm_switch_Trans...
         constructor. destruct H1. subst. apply in_or_app. right. left...
      -- apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. case_eq (eq_TypeName tn (fst (unscope sn))); intros.
  + cbn. rewrite H0. f_equal.
    assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H1. generalize dependent H. generalize ls at - 3.
    induction ls0; intros... cbn. inversion H; subst. f_equal.
    * apply H4. destruct Sub. destruct H2. exists x. split... eapply subterm_switch_Trans...
      constructor. destruct H1. subst. apply in_or_app. right. left...
    * apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
  + cbn. f_equal.
    assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H1. generalize dependent H. generalize ls at - 3.
    induction ls0; intros... cbn. inversion H; subst. f_equal.
    * apply H4. destruct Sub. destruct H2. exists x. split... eapply subterm_switch_Trans...
      constructor. destruct H1. subst. apply in_or_app. right. left...
    * apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + apply IHe. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans... constructor.
  + assert (exists es', es' ++ es = es). { exists []... }
    generalize dependent H1. generalize dependent H0. generalize es at - 3.
    induction es0; intros... cbn. inversion H0; subst. f_equal.
    * destruct a. cbn in *. f_equal. apply H4. destruct Sub. destruct H2.
      exists x. split... eapply subterm_switch_Trans...
      constructor. destruct H1. subst. rewrite in_map_iff. exists (e0,t). split...
      apply in_or_app. right. left...
    * apply IHes0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
  + assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H1. generalize dependent H. generalize ls at - 3.
    induction ls0; intros... cbn. inversion H; subst. f_equal.
    * destruct a. cbn in *. f_equal. apply H4. destruct Sub. destruct H2.
      exists x. split... eapply subterm_switch_Trans...
      apply Sub_Match_cases. destruct H1. subst. rewrite in_map_iff. exists (s,e0). split...
      apply in_or_app. right. left...
    * apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + assert (exists es', es' ++ es = es). { exists []... }
    generalize dependent H1. generalize dependent H0. generalize es at - 3.
    induction es0; intros... cbn. inversion H0; subst. f_equal.
    * destruct a. cbn in *. f_equal. apply H4. destruct Sub. destruct H2. exists x. split...
      eapply subterm_switch_Trans... constructor. destruct H1. subst.
      rewrite in_map_iff. exists (e,t). split... apply in_or_app. right. left...
    * apply IHes0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
  + assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H1. generalize dependent H. generalize ls at - 3.
    induction ls0; intros... cbn. inversion H; subst. f_equal.
    * destruct a. cbn in *. f_equal. apply H4. destruct Sub. destruct H2. exists x. split...
      eapply subterm_switch_Trans... apply Sub_CoMatch_cocases. destruct H1. subst.
      rewrite in_map_iff. exists (s,e). split... apply in_or_app. right. left...
    * apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + apply IHe1. destruct Sub. exists x. destruct H. split... eapply subterm_switch_Trans...
    constructor.
  + apply IHe2. destruct Sub. exists x. destruct H. split... eapply subterm_switch_Trans...
    constructor.
Qed.

Lemma redefunc_exp_inverse : forall p tn e
  (RefuncDt : forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn)
  (RefuncDt2 : In tn (skeleton_dts (program_skeleton p)))
  (InProg : In e (map snd (flat_map snd (program_cfun_bods p))) \/ In e (map snd (flat_map snd (program_gfun_bods p)))
     \/ In e (map snd (program_fun_bods p))),
  defunctionalize_expr tn (refunctionalize_expr tn e) = e.
Proof with eauto.
intros.
assert (Sub : exists e', ((In e' (map snd (flat_map snd (program_cfun_bods p))) \/
  In e' (map snd (flat_map snd (program_gfun_bods p))) \/ In e' (map snd (program_fun_bods p)))
  /\ subterm e e')). { exists e. split... constructor. }
clear InProg.
induction e using expr_strong_ind; intros...
- cbn. case_eq (eq_TypeName tn (fst (unscope n))); intros.
  + cbn. rewrite H0. f_equal. clear - H Sub.
    assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H0. generalize dependent H. generalize ls at - 3.
    induction ls0; intros...
    cbn. inversion H; subst. f_equal.
    * apply H3. clear - Sub H0. destruct Sub. exists x. destruct H. split...
      destruct H0. eapply subterm_switch_Trans... apply Sub_Constr. subst.
      apply in_or_app. right. left...
    * apply IHls0... clear - H0. destruct H0. exists (x++[a]). rewrite <- app_assoc...
  + cbn. f_equal. clear - H Sub.
    assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H0. generalize dependent H. generalize ls at - 3.
    induction ls0; intros...
    cbn. inversion H; subst. f_equal.
    * apply H3. clear - Sub H0. destruct Sub. exists x. destruct H. split...
      destruct H0. eapply subterm_switch_Trans... apply Sub_Constr. subst.
      apply in_or_app. right. left...
    * apply IHls0... clear - H0. destruct H0. exists (x++[a]). rewrite <- app_assoc...
- cbn. case_eq (eq_TypeName tn (fst (unscope n))); intros.
  + exfalso. unfold not in RefuncDt.
    assert (exists dargs t, In (n, dargs, t) (skeleton_dtors (program_skeleton p))).
    { destruct Sub. destruct H1. destruct H1; [ | destruct H1 ].
      - rewrite in_map_iff in H1. destruct H1. destruct H1.
        rewrite in_flat_map in H3. do 2 destruct H3. unfold program_cfun_bods in H3.
        apply in_app_or in H3. destruct H3.
        + rewrite in_map_iff in H3. do 2 destruct H3.
          pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
          rewrite Forall_forall in TypG. apply TypG in H5. destruct H5 as [qn [args [t [SigLookup Typ]]]].
          subst. cbn in *. destruct x0.
          assert (Sub : subterm (E_DestrCall n e ls) (E_Match (fst x2) (E_Var 0) (index_list 1 args) (snd x2) t)).
          { eapply Sub_Trans... cbn. apply Sub_Match_cases. apply in_map with (f:=snd) in H4... }
          pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
          clear - TypSub. destruct TypSub. destruct H. inversion H; subst...
        + rewrite in_map_iff in H3. do 2 destruct H3.
          pose proof (program_cfun_bods_typecheck_l p) as TypL. unfold cfun_bods_l_typecheck in TypL.
          rewrite Forall_forall in TypL. apply TypL in H5. destruct H5 as [qn [args [t [SigLookup Typ]]]].
          subst. cbn in *. destruct x0.
          assert (Sub : subterm (E_DestrCall n e ls) (E_Match (fst x2) (E_Var 0) (index_list 1 args) (snd x2) t)).
          { eapply Sub_Trans... cbn. apply Sub_Match_cases. apply in_map with (f:=snd) in H4... }
          pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
          clear - TypSub. destruct TypSub. destruct H. inversion H; subst...
      - rewrite in_map_iff in H1. destruct H1. destruct H1.
        rewrite in_flat_map in H3. do 2 destruct H3. unfold program_gfun_bods in H3.
        apply in_app_or in H3. destruct H3.
        + rewrite in_map_iff in H3. do 2 destruct H3.
          pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
          rewrite Forall_forall in TypG. apply TypG in H5. destruct H5 as [qn [args [SigLookup Typ]]].
          subst. cbn in *. destruct x0.
          assert (Sub : subterm (E_DestrCall n e ls) (E_CoMatch (fst x2) (index_list 0 args) (snd x2))).
          { eapply Sub_Trans... cbn. apply Sub_CoMatch_cocases. apply in_map with (f:=snd) in H4... }
          pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
          clear - TypSub. destruct TypSub. destruct H. inversion H; subst...
        + rewrite in_map_iff in H3. do 2 destruct H3.
          pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
          rewrite Forall_forall in TypL. apply TypL in H5. destruct H5 as [qn [args [SigLookup Typ]]].
          subst. cbn in *. destruct x0.
          assert (Sub : subterm (E_DestrCall n e ls) (E_CoMatch (fst x2) (index_list 0 args) (snd x2))).
          { eapply Sub_Trans... cbn. apply Sub_CoMatch_cocases. apply in_map with (f:=snd) in H4... }
          pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
          clear - TypSub. destruct TypSub. destruct H. inversion H; subst...
      - rewrite in_map_iff in H1. destruct H1. destruct H1.
        pose proof (program_fun_bods_typecheck p) as TypF. unfold fun_bods_typecheck in TypF.
        rewrite Forall_forall in TypF. apply TypF in H3. destruct H3 as [qn [args [t [SigLookup Typ]]]].
        subst. cbn in *. destruct x0. cbn in *.
        pose proof (subterm_typechecks _ _ _ _ _ Typ H2) as TypSub.
        clear - TypSub. destruct TypSub. destruct H. inversion H; subst. exists dargs...
    }
    do 2 destruct H1. eapply RefuncDt...
    cbn. rewrite eq_TypeName_eq in H0...
  + clear - H Sub IHe. f_equal.
    * apply IHe. destruct Sub. destruct H0. exists x. split... eapply subterm_switch_Trans... constructor.
    * assert (exists ls', ls' ++ ls = ls). { exists []... }
      generalize dependent H0. generalize dependent H. generalize ls at - 3.
      induction ls0; intros... cbn. inversion H; subst. f_equal.
      -- apply H3. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans...
         constructor. destruct H0. subst. apply in_or_app. right. left...
      -- apply IHls0... destruct H0. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal...
  assert (exists ls', ls' ++ ls = ls). { exists []... }
  generalize dependent H0. generalize dependent H. generalize ls at - 3.
  induction ls0; intros... cbn. inversion H; subst. f_equal.
  + apply H3. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans...
    constructor. destruct H0. subst. apply in_or_app. right. left...
  + apply IHls0... destruct H0. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. case_eq (eq_TypeName tn (fst (unscope sn))); intros.
  + cbn. rewrite H0. f_equal.
    * apply IHe. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans... constructor.
    * assert (exists ls', ls' ++ ls = ls). { exists []... }
      generalize dependent H1. generalize dependent H. generalize ls at - 3.
      induction ls0; intros... cbn. inversion H; subst. f_equal.
      -- apply H4. destruct Sub. destruct H2. exists x. split... eapply subterm_switch_Trans...
         constructor. destruct H1. subst. apply in_or_app. right. left...
      -- apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
  + cbn. f_equal.
    * apply IHe. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans... constructor.
    * assert (exists ls', ls' ++ ls = ls). { exists []... }
      generalize dependent H1. generalize dependent H. generalize ls at - 3.
      induction ls0; intros... cbn. inversion H; subst. f_equal.
      -- apply H4. destruct Sub. destruct H2. exists x. split... eapply subterm_switch_Trans...
         constructor. destruct H1. subst. apply in_or_app. right. left...
      -- apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. case_eq (eq_TypeName tn (fst (unscope sn))); intros.
  + exfalso.
    destruct Sub. destruct H1. destruct H1; [ | destruct H1].
    * rewrite in_map_iff in H1. destruct H1. destruct H1.
      rewrite in_flat_map in H3. do 2 destruct H3. unfold program_cfun_bods in H3.
      apply in_app_or in H3. destruct H3.
      -- pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
         rewrite Forall_forall in TypG.
         rewrite in_map_iff in H3. do 2 destruct H3.
         apply TypG in H5. destruct H5 as [qn [args [t [SigLookup Typ]]]].
         subst. cbn in *. destruct x0.
         assert (Sub : subterm (E_GenFunCall sn ls) (E_Match (fst x2) (E_Var 0) (index_list 1 args) (snd x2) t)).
         { eapply Sub_Trans... cbn. apply Sub_Match_cases. apply in_map with (f:=snd) in H4... }
         pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
         destruct TypSub as [ctx' [t' TypSub]]. inversion TypSub; subst.
         ++ pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as SigInCdt.
            unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
            apply SigInCdt in H7. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - RefuncDt2 H7.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
         ++ pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as SigInCdt.
            unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
            apply SigInCdt in H7. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - RefuncDt2 H7.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
      -- pose proof (program_cfun_bods_typecheck_l p) as TypL. unfold cfun_bods_l_typecheck in TypL.
         rewrite Forall_forall in TypL.
         rewrite in_map_iff in H3. do 2 destruct H3.
         apply TypL in H5. destruct H5 as [qn [args [t [SigLookup Typ]]]].
         subst. cbn in *. destruct x0.
         assert (Sub : subterm (E_GenFunCall sn ls) (E_Match (fst x2) (E_Var 0) (index_list 1 args) (snd x2) t)).
         { eapply Sub_Trans... cbn. apply Sub_Match_cases. apply in_map with (f:=snd) in H4... }
         pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
         destruct TypSub as [ctx' [t' TypSub]]. inversion TypSub; subst.
         ++ pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as SigInCdt.
            unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
            apply SigInCdt in H7. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - RefuncDt2 H7.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
         ++ pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as SigInCdt.
            unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
            apply SigInCdt in H7. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - RefuncDt2 H7.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
    * rewrite in_map_iff in H1. destruct H1. destruct H1.
      rewrite in_flat_map in H3. do 2 destruct H3. unfold program_gfun_bods in H3.
      apply in_app_or in H3. destruct H3.
      -- pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
         rewrite Forall_forall in TypG.
         rewrite in_map_iff in H3. do 2 destruct H3.
         apply TypG in H5. destruct H5 as [qn [args [SigLookup Typ]]].
         subst. cbn in *. destruct x0.
         assert (Sub : subterm (E_GenFunCall sn ls) (E_CoMatch (fst x2) (index_list 0 args) (snd x2))).
         { eapply Sub_Trans... cbn. apply Sub_CoMatch_cocases. apply in_map with (f:=snd) in H4... }
         pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
         destruct TypSub as [ctx' [t' TypSub]]. inversion TypSub; subst.
         ++ pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as SigInCdt.
            unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
            apply SigInCdt in H7. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - RefuncDt2 H7.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
         ++ pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as SigInCdt.
            unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
            apply SigInCdt in H7. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - RefuncDt2 H7.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
      -- pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
         rewrite Forall_forall in TypL.
         rewrite in_map_iff in H3. do 2 destruct H3.
         apply TypL in H5. destruct H5 as [qn [args [SigLookup Typ]]].
         subst. cbn in *. destruct x0.
         assert (Sub : subterm (E_GenFunCall sn ls) (E_CoMatch (fst x2) (index_list 0 args) (snd x2))).
         { eapply Sub_Trans... cbn. apply Sub_CoMatch_cocases. apply in_map with (f:=snd) in H4... }
         pose proof (subterm_typechecks _ _ _ _ _ Typ Sub) as TypSub.
         destruct TypSub as [ctx' [t' TypSub]]. inversion TypSub; subst.
         ++ pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as SigInCdt.
            unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
            apply SigInCdt in H7. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - RefuncDt2 H7.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
         ++ pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as SigInCdt.
            unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
            apply SigInCdt in H7. cbn in *. rewrite eq_TypeName_eq in *. subst.
            clear - RefuncDt2 H7.
            pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
            unfold dts_cdts_disjoint in Disj. unfold not in Disj. apply Disj with (t:=fst qn0).
            split...
    * rewrite in_map_iff in H1. destruct H1. destruct H1.
      pose proof (program_fun_bods_typecheck p) as TypF. unfold fun_bods_typecheck in TypF.
      rewrite Forall_forall in TypF. apply TypF in H3. destruct H3 as [qn [args [t [SigLookup Typ]]]].
      subst. cbn in *. destruct x0. cbn in *.
      pose proof (subterm_typechecks _ _ _ _ _ Typ H2) as TypSub.
      clear - RefuncDt2 TypSub H0. destruct TypSub. destruct H. inversion H; subst.
      -- pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as SigInCdt.
         unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
         apply SigInCdt in H5. cbn in *. rewrite eq_TypeName_eq in *. subst.
         pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
         unfold dts_cdts_disjoint in Disj. unfold not in Disj. cbn in *.
         apply Disj with (t:=fst qn). split...
      -- pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as SigInCdt.
         unfold gfun_sigs_in_cdts in SigInCdt. rewrite Forall_forall in SigInCdt.
         apply SigInCdt in H5. cbn in *. rewrite eq_TypeName_eq in *. subst.
         pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
         unfold dts_cdts_disjoint in Disj. unfold not in Disj. cbn in *.
         apply Disj with (t:=fst qn). split...
  + f_equal. assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H1. generalize dependent H. generalize ls at - 3.
    induction ls0; intros... cbn. inversion H; subst. f_equal.
    * apply H4. destruct Sub. destruct H2. exists x. split... eapply subterm_switch_Trans...
      constructor. destruct H1. subst. apply in_or_app. right. left...
    * apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + apply IHe. destruct Sub. destruct H1. exists x. split... eapply subterm_switch_Trans... constructor.
  + assert (exists es', es' ++ es = es). { exists []... }
    generalize dependent H1. generalize dependent H0. generalize es at - 3.
    induction es0; intros... cbn. inversion H0; subst. f_equal.
    * destruct a. cbn in *. f_equal. apply H4. destruct Sub. destruct H2.
      exists x. split... eapply subterm_switch_Trans...
      constructor. destruct H1. subst. rewrite in_map_iff. exists (e0,t). split...
      apply in_or_app. right. left...
    * apply IHes0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
  + assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H1. generalize dependent H. generalize ls at - 3.
    induction ls0; intros... cbn. inversion H; subst. f_equal.
    * destruct a. cbn in *. f_equal. apply H4. destruct Sub. destruct H2.
      exists x. split... eapply subterm_switch_Trans...
      apply Sub_Match_cases. destruct H1. subst. rewrite in_map_iff. exists (s,e0). split...
      apply in_or_app. right. left...
    * apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + assert (exists es', es' ++ es = es). { exists []... }
    generalize dependent H1. generalize dependent H0. generalize es at - 3.
    induction es0; intros... cbn. inversion H0; subst. f_equal.
    * destruct a. cbn in *. f_equal. apply H4. destruct Sub. destruct H2. exists x. split...
      eapply subterm_switch_Trans... constructor. destruct H1. subst.
      rewrite in_map_iff. exists (e,t). split... apply in_or_app. right. left...
    * apply IHes0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
  + assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H1. generalize dependent H. generalize ls at - 3.
    induction ls0; intros... cbn. inversion H; subst. f_equal.
    * destruct a. cbn in *. f_equal. apply H4. destruct Sub. destruct H2. exists x. split...
      eapply subterm_switch_Trans... apply Sub_CoMatch_cocases. destruct H1. subst.
      rewrite in_map_iff. exists (s,e). split... apply in_or_app. right. left...
    * apply IHls0... destruct H1. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + apply IHe1. destruct Sub. exists x. destruct H. split... eapply subterm_switch_Trans...
    constructor.
  + apply IHe2. destruct Sub. exists x. destruct H. split... eapply subterm_switch_Trans...
    constructor.
Qed.


(* e is subterm of e' with n intermediate lets *)
Inductive subterm_at_depth : expr -> expr -> nat -> Prop :=
  | Sub_Refl : forall e, subterm_at_depth e e 0
  | Sub_Trans_NoLet : forall e1 e2 e3 n,
      (forall e_1 e_2, e2 <> E_Let e_1 e_2) ->
      (forall q e_0 bs cases t,
        e2 = E_Match q e_0 bs cases t ->
        e1 = e_0 \/ In e1 (map fst bs)) ->
      (forall q bs cocases,
        e2 = E_CoMatch q bs cocases ->
        In e1 (map fst bs)) ->
      direct_subterm e1 e2 ->
      subterm_at_depth e2 e3 n ->
      subterm_at_depth e1 e3 n
  | Sub_Trans_Let_1 : forall e1 e2 e3 e' n,
      e2 = E_Let e1 e' ->
      subterm_at_depth e2 e3 n ->
      subterm_at_depth e1 e3 n
  | Sub_Trans_Let_2 : forall e1 e2 e3 e' n,
      e2 = E_Let e' e1 ->
      subterm_at_depth e2 e3 n ->
      subterm_at_depth e1 e3 (S n).

Lemma switch_indices_helper_inverse : forall p p2 e d c
  (VarLt : forall i n, subterm_at_depth (E_Var i) e n -> i < d + c + n),
  (switch_indices_helper (switch_indices_helper e p c d 0) p2 d c 0) = e.
Proof with eauto.
intros.
assert (Sub : subterm_at_depth e e 0); try constructor.
generalize Sub. clear Sub. generalize e at - 2. intro e0.
generalize 0.
induction e0 using expr_strong_ind; intros.
- cbn - [ Nat.ltb ]. case_eq (v <? n); intros.
  + cbn - [ Nat.ltb ]. case_eq (v <? n); intros...
    case_eq (v <? n + c); intros; rewrite H in H0; discriminate.
  + case_eq (v <? n + d); intros.
    * cbn - [ Nat.ltb ]. case_eq (v + c <? n); intros.
      -- rewrite Nat.ltb_ge in H. rewrite Nat.ltb_lt in H1. omega.
      -- case_eq (v + c <? n + c); intros.
         ++ rewrite Nat.ltb_ge in *. rewrite Nat.ltb_lt in *. omega.
         ++ rewrite Nat.add_sub...
    * cbn - [ Nat.ltb ]. case_eq (v - d <? n); intros.
      -- rewrite Nat.ltb_ge in *. rewrite Nat.ltb_lt in *. omega.
      -- case_eq (v - d <? n + c); intros.
         ++ rewrite Nat.ltb_ge in *. rewrite Nat.ltb_lt in *.
            replace (v - d + d) with v; try omega...
         ++ rewrite Nat.ltb_ge in *.
            apply VarLt in Sub. omega.
- cbn. f_equal. clear - H Sub.
  assert (exists ls', ls' ++ ls = ls). { exists []... }
  generalize dependent H0. generalize dependent H. generalize ls at - 3.
  induction ls0; intros...
  cbn. inversion H; subst. f_equal.
  + apply H3. eapply Sub_Trans_NoLet...
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    clear - H0. apply Sub_Constr. destruct H0. subst. apply in_or_app. right. left...
  + apply IHls0... clear - H0. destruct H0. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + apply IHe0.
    eapply Sub_Trans_NoLet...
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    apply Sub_DestrCall_e0.
  + assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H0. generalize dependent H. generalize ls at - 3.
    induction ls0; intros...
    cbn. inversion H; subst. f_equal.
    * apply H3. eapply Sub_Trans_NoLet...
      { intros. unfold not. intros. discriminate. }
      { intros. unfold not. intros. discriminate. }
      { intros. unfold not. intros. discriminate. }
      clear - H0. apply Sub_DestrCall_es. destruct H0. subst. apply in_or_app. right. left...
    * apply IHls0... clear - H0. destruct H0. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal. clear - H Sub.
  assert (exists ls', ls' ++ ls = ls). { exists []... }
  generalize dependent H0. generalize dependent H. generalize ls at - 3.
  induction ls0; intros...
  cbn. inversion H; subst. f_equal.
  + apply H3. eapply Sub_Trans_NoLet...
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    clear - H0. apply Sub_FunCall. destruct H0. subst. apply in_or_app. right. left...
  + apply IHls0... clear - H0. destruct H0. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + apply IHe0. eapply Sub_Trans_NoLet...
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    apply Sub_ConsFunCall_e0.
  + assert (exists ls', ls' ++ ls = ls). { exists []... }
    generalize dependent H0. generalize dependent H. generalize ls at - 3.
    induction ls0; intros...
    cbn. inversion H; subst. f_equal.
    * apply H3. eapply Sub_Trans_NoLet...
      { intros. unfold not. intros. discriminate. }
      { intros. unfold not. intros. discriminate. }
      { intros. unfold not. intros. discriminate. }
      clear - H0. apply Sub_ConsFunCall_es. destruct H0. subst. apply in_or_app. right. left...
    * apply IHls0... clear - H0. destruct H0. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal. clear - H Sub.
  assert (exists ls', ls' ++ ls = ls). { exists []... }
  generalize dependent H0. generalize dependent H. generalize ls at - 3.
  induction ls0; intros...
  cbn. inversion H; subst. f_equal.
  + apply H3. eapply Sub_Trans_NoLet...
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    clear - H0. apply Sub_GenFunCall. destruct H0. subst. apply in_or_app. right. left...
  + apply IHls0... clear - H0. destruct H0. subst. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + apply IHe0. eapply Sub_Trans_NoLet...
    { intros. unfold not. intros. discriminate. }
    { intros. inversion H1... }
    { intros. unfold not. intros. discriminate. }
    apply Sub_Match_e0.
  + clear - H0 Sub.
    assert (exists es', es' ++ es = es). { exists []... }
    generalize dependent H. generalize dependent H0. generalize es at - 3.
    induction es0; intros...
    cbn. inversion H0; subst. f_equal.
    * destruct a. cbn. f_equal. apply H3. clear - Sub H. eapply Sub_Trans_NoLet...
      { intros. unfold not. intros. discriminate. }
      { intros. inversion H0; subst. destruct H. subst. right. rewrite map_app. apply in_or_app. right. cbn... }
      { intros. unfold not. intros. discriminate. }
      apply Sub_Match_bs. destruct H. subst. rewrite map_app. apply in_or_app. right. cbn. left...
    * apply IHes0... clear - H. destruct H. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  clear - H0 Sub.
  assert (exists es', es' ++ es = es). { exists []... }
  generalize dependent H. generalize dependent H0. generalize es at - 3.
  induction es0; intros...
  cbn. inversion H0; subst. f_equal.
  + destruct a. cbn. f_equal. apply H3. clear - Sub H. eapply Sub_Trans_NoLet...
    { intros. unfold not. intros. discriminate. }
    { intros. unfold not. intros. discriminate. }
    { intros. inversion H0; subst. destruct H. subst. rewrite map_app. apply in_or_app. right. cbn... }
    apply Sub_CoMatch_bs. destruct H. subst. rewrite map_app. apply in_or_app. right. cbn. left...
  + apply IHes0... clear - H. destruct H. exists (x++[a]). rewrite <- app_assoc...
- cbn. f_equal.
  + apply IHe0_1. eapply Sub_Trans_Let_1...
  + apply IHe0_2. replace (n+1) with (S n); try omega.
    eapply Sub_Trans_Let_2...
Qed.

Lemma switch_indices_helper_defunc_exchange : forall p tn c d e,
  switch_indices_helper (defunctionalize_expr tn e) p c d 0 =
  defunctionalize_expr tn (switch_indices_helper e p c d 0).
Proof with eauto.
intros. generalize 0. induction e using expr_strong_ind; intros.
- cbn - [ Nat.ltb ]. case_eq (v <? n); intros... case_eq (v <? n + d); intros...
- cbn. f_equal. induction ls... cbn. inversion H; subst. rewrite H2. f_equal...
- cbn. destruct (eq_TypeName tn (fst (unscope n))).
  + cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
  + cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
- cbn. f_equal. induction ls... inversion H; subst. cbn. f_equal...
- cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
- cbn. destruct (eq_TypeName tn (fst (unscope sn))).
  + cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
  + cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
- cbn. f_equal... induction es... inversion H0; subst. cbn. f_equal...
  destruct a. f_equal...
- cbn. f_equal. induction es... inversion H0; subst. cbn. f_equal...
  destruct a. f_equal...
- cbn. f_equal...
Qed.

Lemma switch_indices_helper_refunc_exchange : forall p tn c d e,
  switch_indices_helper (refunctionalize_expr tn e) p c d 0 =
  refunctionalize_expr tn (switch_indices_helper e p c d 0).
Proof with eauto.
intros. generalize 0. induction e using expr_strong_ind; intros.
- cbn - [ Nat.ltb ]. case_eq (v <? n); intros... case_eq (v <? n + d); intros...
- cbn. destruct (eq_TypeName tn (fst (unscope n))).
  + cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
  + cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
- cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
- cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
- cbn. destruct (eq_TypeName tn (fst (unscope sn))).
  + cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
  + cbn. f_equal... induction ls... inversion H; subst. cbn. f_equal...
- cbn. f_equal. induction ls... inversion H; subst. cbn. f_equal...
- cbn. f_equal... induction es... inversion H0; subst. cbn. f_equal...
  destruct a. f_equal...
- cbn. f_equal. induction es... inversion H0; subst. cbn. f_equal...
  destruct a. f_equal...
- cbn. f_equal...
Qed.

Lemma ctor_gsig_length : forall p tn a c g
  (DefuncCdt : forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn)
  (InGbods: In a (map fst (program_gfun_bods_for_type tn p))),
  lookup_ctor_sig (defunctionalize_to_skeleton p tn) a = Some c ->
  Some g = lookup_gfun_sig_scoped (program_skeleton p) a ->
  length (snd g) = length (snd c).
Proof with eauto.
intros. unfold lookup_ctor_sig in H. apply find_some in H.
unfold lookup_gfun_sig_scoped in H0. destruct a.
- unfold lookup_gfun_sig_l in H0. unfold lookup_gfun_sig_x in H0. symmetry in H0.
  apply find_some in H0. cbn in H. destruct H. destruct c. cbn in H1.
  destruct s; try discriminate. rewrite eq_QName_eq in H1. subst q0.
  cbn. destruct g. cbn. destruct H0. rewrite eq_QName_eq in H1. cbn in H1. subst q0.
  apply in_app_or in H. destruct H.
  + unfold computeNewDatatype in H. apply in_app_or in H. destruct H.
    * rewrite in_map_iff in H. do 2 destruct H. inversion H.
    * rewrite in_map_iff in H. do 2 destruct H. inversion H; subst. clear H.
      rewrite filter_In in H1. destruct H1. rewrite eq_TypeName_eq in H1. subst tn.
      destruct x. cbn in *. pose proof (skeleton_gfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
      unfold gfun_sigs_names_unique in Uniq. clear - H H0 Uniq.
      generalize dependent (skeleton_gfun_sigs_l (program_skeleton p)); intros.
      induction g; [ inversion H | ]. cbn in Uniq. inversion Uniq; subst.
      destruct H0; subst.
      -- destruct H; subst; [ inversion H | ]... apply (in_map fst) in H. cbn in *. exfalso...
      -- destruct H; subst; [| apply IHg]... apply (in_map fst) in H0. cbn in *. exfalso...
  + apply DefuncCdt in H. cbn in H. rewrite in_map_iff in InGbods. destruct InGbods as [x [qEq xIn]].
    unfold program_gfun_bods_for_type in xIn. rewrite filter_In in xIn. destruct xIn as [_ xEq].
    rewrite eq_TypeName_eq in xEq. subst tn. rewrite qEq in H. cbn in H. exfalso...
- unfold lookup_gfun_sig_g in H0. unfold lookup_gfun_sig_x in H0. symmetry in H0.
  apply find_some in H0. cbn in H. destruct H. destruct c. cbn in H1.
  destruct s; try discriminate. rewrite eq_QName_eq in H1. subst q0.
  cbn. destruct g. cbn. destruct H0. rewrite eq_QName_eq in H1. cbn in H1. subst q0.
  apply in_app_or in H. destruct H.
  + unfold computeNewDatatype in H. apply in_app_or in H. destruct H.
    * rewrite in_map_iff in H. do 2 destruct H. inversion H; subst. clear H.
      rewrite filter_In in H1. destruct H1. rewrite eq_TypeName_eq in H1. subst tn.
      destruct x. cbn in *. pose proof (skeleton_gfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
      unfold gfun_sigs_names_unique in Uniq. clear - H H0 Uniq.
      generalize dependent (skeleton_gfun_sigs_g (program_skeleton p)); intros.
      induction g; [ inversion H | ]. cbn in Uniq. inversion Uniq; subst.
      destruct H0; subst.
      -- destruct H; subst; [ inversion H | ]... apply (in_map fst) in H. cbn in *. exfalso...
      -- destruct H; subst; [| apply IHg]... apply (in_map fst) in H0. cbn in *. exfalso...
    * rewrite in_map_iff in H. do 2 destruct H. inversion H.
  + apply DefuncCdt in H. cbn in H. rewrite in_map_iff in InGbods. destruct InGbods as [x [qEq xIn]].
    unfold program_gfun_bods_for_type in xIn. rewrite filter_In in xIn. destruct xIn as [_ xEq].
    rewrite eq_TypeName_eq in xEq. subst tn. rewrite qEq in H. cbn in H. exfalso...
Qed.

Lemma ctor_gsig_length' : forall p tn a c g
  (RefuncDt : forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn)
  (RefuncDt2 : In tn (skeleton_dts (program_skeleton p)))
  (CtorType : fst (unscope (fst c)) = tn),
  lookup_ctor_sig (program_skeleton p) a = Some c ->
  Some g = lookup_gfun_sig_scoped (refunctionalize_to_skeleton p tn) a ->
  length (snd c) = length (snd g).
Proof with eauto.
intros. unfold lookup_ctor_sig in H. apply find_some in H.
unfold lookup_gfun_sig_scoped in H0. destruct a.
- unfold lookup_gfun_sig_l in H0. unfold lookup_gfun_sig_x in H0. symmetry in H0.
  apply find_some in H0. cbn in H. destruct H. destruct c. cbn in H1.
  destruct s; try discriminate. rewrite eq_QName_eq in H1. subst q0.
  cbn. destruct g. cbn. destruct H0. rewrite eq_QName_eq in H1. cbn in H1. subst q0.
  apply in_app_or in H0. destruct H0.
  + rewrite in_map_iff in H0. do 2 destruct H0. unfold gfunsigs_mapfun in H0. destruct x.
    inversion H0; subst. rewrite filter_In in H1. destruct H1. cbn in H2. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H2. destruct q. cbn in *. clear H2 H0.
    pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
    unfold dts_ctor_names_unique in Uniq. clear - H H1 Uniq.
    generalize dependent (skeleton_ctors (program_skeleton p)); intros.
    induction c; [ inversion H | ]. cbn in Uniq. inversion Uniq; subst.
    destruct H1; subst.
    * destruct H; subst; [ inversion H | ]... apply (in_map fst) in H. cbn in *. exfalso...
    * destruct H; subst; [| apply IHc]... apply (in_map fst) in H0. cbn in *. exfalso...
  + cbn in CtorType. pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)).
    unfold gfun_sigs_in_cdts in H1. rewrite Forall_forall in H1. apply H1 in H0.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
    unfold dts_cdts_disjoint in Disj. exfalso. unfold not in Disj. cbn in H0. subst...
- unfold lookup_gfun_sig_g in H0. unfold lookup_gfun_sig_x in H0. symmetry in H0.
  apply find_some in H0. cbn in H. destruct H. destruct c. cbn in H1.
  destruct s; try discriminate. rewrite eq_QName_eq in H1. subst q0.
  cbn. destruct g. cbn. destruct H0. rewrite eq_QName_eq in H1. cbn in H1. subst q0.
  apply in_app_or in H0. destruct H0.
  + rewrite in_map_iff in H0. do 2 destruct H0. unfold gfunsigs_mapfun in H0. destruct x.
    inversion H0; subst. rewrite filter_In in H1. destruct H1. cbn in H2. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H2. destruct q. cbn in *. clear H2 H0.
    pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq.
    unfold dts_ctor_names_unique in Uniq. clear - H H1 Uniq.
    generalize dependent (skeleton_ctors (program_skeleton p)); intros.
    induction c; [ inversion H | ]. cbn in Uniq. inversion Uniq; subst.
    destruct H1; subst.
    * destruct H; subst; [ inversion H | ]... apply (in_map fst) in H. cbn in *. exfalso...
    * destruct H; subst; [| apply IHc]... apply (in_map fst) in H0. cbn in *. exfalso...
  + cbn in CtorType. pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)).
    unfold gfun_sigs_in_cdts in H1. rewrite Forall_forall in H1. apply H1 in H0.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
    unfold dts_cdts_disjoint in Disj. exfalso. unfold not in Disj. cbn in H0. subst...
Qed.

Lemma dtor_csig_length : forall p tn a d c0
  (DefuncCdt : forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn)
  (DefuncCdt2 : In tn (skeleton_cdts (program_skeleton p)))
  (DtorType : fst (unscope (fst (fst d))) = tn),
  lookup_dtor (program_skeleton p) a = Some d ->
  Some c0 = lookup_cfun_sig_scoped (defunctionalize_to_skeleton p tn) a ->
  length (snd (fst d)) = length (snd (fst c0)).
Proof with eauto.
intros. unfold lookup_dtor in H. apply find_some in H.
unfold lookup_cfun_sig_scoped in H0. destruct a.
- unfold lookup_cfun_sig_l in H0. unfold lookup_cfun_sig_x in H0. symmetry in H0.
  apply find_some in H0. cbn in H. destruct H. destruct d. destruct p0. cbn in H1.
  destruct s; try discriminate. rewrite eq_QName_eq in H1. subst q0.
  cbn. destruct c0. destruct p0. cbn. destruct H0. rewrite eq_QName_eq in H1. cbn in H1. subst q0.
  apply in_app_or in H0. destruct H0.
  + rewrite in_map_iff in H0. do 2 destruct H0. unfold cfunsigs_mapfun in H0. destruct x. destruct p0.
    inversion H0; subst. rewrite filter_In in H1. destruct H1. cbn in H2. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H2. destruct q. cbn in *. clear H2 H0.
    pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)) as Uniq.
    unfold cdts_dtor_names_unique in Uniq. clear - H H1 Uniq.
    generalize dependent (skeleton_dtors (program_skeleton p)); intros.
    induction d; [ inversion H | ]. cbn in Uniq. inversion Uniq; subst.
    destruct H1; subst.
    * destruct H; subst; [ inversion H | ]... do 2 apply (in_map fst) in H. cbn in *. rewrite map_map in H. exfalso...
    * destruct H; subst; [| apply IHd]... do 2 apply (in_map fst) in H0. cbn in *. rewrite map_map in H0. exfalso...
  + cbn in DtorType. pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)).
    unfold cfun_sigs_in_dts in H1. rewrite Forall_forall in H1. apply H1 in H0.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
    unfold dts_cdts_disjoint in Disj. exfalso. unfold not in Disj. cbn in H0. subst...
- unfold lookup_cfun_sig_g in H0. unfold lookup_cfun_sig_x in H0. symmetry in H0.
  apply find_some in H0. cbn in H. destruct H. destruct d. destruct p0. cbn in H1.
  destruct s; try discriminate. rewrite eq_QName_eq in H1. subst q0.
  cbn. destruct c0. destruct p0. cbn. destruct H0. rewrite eq_QName_eq in H1. cbn in H1. subst q0.
  apply in_app_or in H0. destruct H0.
  + rewrite in_map_iff in H0. do 2 destruct H0. unfold cfunsigs_mapfun in H0. destruct x. destruct p0.
    inversion H0; subst. rewrite filter_In in H1. destruct H1. cbn in H2. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H2. destruct q. cbn in *. clear H2 H0.
    pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)) as Uniq.
    unfold cdts_dtor_names_unique in Uniq. clear - H H1 Uniq.
    generalize dependent (skeleton_dtors (program_skeleton p)); intros.
    induction d; [ inversion H | ]. cbn in Uniq. inversion Uniq; subst.
    destruct H1; subst.
    * destruct H; subst; [ inversion H | ]... do 2 apply (in_map fst) in H. cbn in *. rewrite map_map in H. exfalso...
    * destruct H; subst; [| apply IHd]... do 2 apply (in_map fst) in H0. cbn in *. rewrite map_map in H0. exfalso...
  + cbn in DtorType. pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)).
    unfold cfun_sigs_in_dts in H1. rewrite Forall_forall in H1. apply H1 in H0.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
    unfold dts_cdts_disjoint in Disj. exfalso. unfold not in Disj. cbn in H0. subst...
Qed.

Lemma dtor_csig_length' : forall p tn a d c0
  (RefuncDt : forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn)
  (InCbods: In a (map fst (program_cfun_bods_for_type tn p))),
  lookup_dtor (refunctionalize_to_skeleton p tn) a = Some d ->
  Some c0 = lookup_cfun_sig_scoped (program_skeleton p) a ->
  length (snd (fst c0)) = length (snd (fst d)).
Proof with eauto.
intros. unfold lookup_dtor in H. apply find_some in H.
unfold lookup_cfun_sig_scoped in H0. destruct a.
- unfold lookup_cfun_sig_l in H0. unfold lookup_cfun_sig_x in H0. symmetry in H0.
  apply find_some in H0. cbn in H. destruct H. destruct d. destruct p0. cbn in H1.
  destruct s; try discriminate. rewrite eq_QName_eq in H1. subst q0.
  cbn. destruct c0. destruct p0. cbn. destruct H0. rewrite eq_QName_eq in H1. cbn in H1. subst q0.
  apply in_app_or in H. destruct H.
  + unfold computeNewDatatype in H. apply in_app_or in H. destruct H.
    * rewrite in_map_iff in H. do 2 destruct H. inversion H.
    * rewrite in_map_iff in H. do 2 destruct H. inversion H; subst. clear H.
      rewrite filter_In in H1. destruct H1. rewrite eq_TypeName_eq in H1. subst tn.
      destruct x. destruct p0. cbn in *. pose proof (skeleton_cfun_sigs_names_unique_l (program_skeleton p)) as Uniq.
      unfold cfun_sigs_names_unique in Uniq. clear - H H0 Uniq.
      generalize dependent (skeleton_cfun_sigs_l (program_skeleton p)); intros.
      induction c; [ inversion H | ]. cbn in Uniq. inversion Uniq; subst.
      destruct H0; subst.
      -- destruct H; subst; [ inversion H | ]... do 2 apply (in_map fst) in H. cbn in *. rewrite map_map in H. exfalso...
      -- destruct H; subst; [| apply IHc]... do 2 apply (in_map fst) in H0. cbn in *. rewrite map_map in H0. exfalso...
  + apply RefuncDt in H. cbn in H. rewrite in_map_iff in InCbods. destruct InCbods as [x [qEq xIn]].
    unfold program_cfun_bods_for_type in xIn. rewrite filter_In in xIn. destruct xIn as [_ xEq].
    rewrite eq_TypeName_eq in xEq. subst tn. rewrite qEq in H. cbn in H. exfalso...
- unfold lookup_cfun_sig_g in H0. unfold lookup_cfun_sig_x in H0. symmetry in H0.
  apply find_some in H0. cbn in H. destruct H. destruct d. destruct p0. cbn in H1.
  destruct s; try discriminate. rewrite eq_QName_eq in H1. subst q0.
  cbn. destruct c0. destruct p0. cbn. destruct H0. rewrite eq_QName_eq in H1. cbn in H1. subst q0.
  apply in_app_or in H. destruct H.
  + unfold computeNewCoDatatype in H. apply in_app_or in H. destruct H.
    * rewrite in_map_iff in H. do 2 destruct H. inversion H; subst. clear H.
      rewrite filter_In in H1. destruct H1. rewrite eq_TypeName_eq in H1. subst tn.
      destruct x. cbn in *. pose proof (skeleton_cfun_sigs_names_unique_g (program_skeleton p)) as Uniq.
      unfold cfun_sigs_names_unique in Uniq. clear - H H0 Uniq.
      generalize dependent (skeleton_cfun_sigs_g (program_skeleton p)); intros.
      induction c; [ inversion H | ]. cbn in Uniq. inversion Uniq; subst.
      destruct H0; subst.
      -- destruct H; subst; [ inversion H | ]... do 2 apply (in_map fst) in H. cbn in *. rewrite map_map in H. exfalso...
      -- destruct H; subst; [| apply IHc]... do 2 apply (in_map fst) in H0. cbn in *. rewrite map_map in H0. exfalso...
    * rewrite in_map_iff in H. do 2 destruct H. inversion H.
  + apply RefuncDt in H. cbn in H. rewrite in_map_iff in InCbods. destruct InCbods as [x [qEq xIn]].
    unfold program_cfun_bods_for_type in xIn. rewrite filter_In in xIn. destruct xIn as [_ xEq].
    rewrite eq_TypeName_eq in xEq. subst tn. rewrite qEq in H. cbn in H. exfalso...
Qed.

Lemma no_gfun_no_ctor : forall p tn a
  (InGbods : In a (map fst (program_gfun_bods_for_type tn p))),
  lookup_gfun_sig_scoped (program_skeleton p) a = None ->
  lookup_ctor_sig (defunctionalize_to_skeleton p tn) a = None.
Proof with eauto.
intros. unfold lookup_gfun_sig_scoped in H. cbn in *. unfold computeNewDatatype. destruct a.
- unfold lookup_gfun_sig_l in H. unfold lookup_gfun_sig_x in H.
  rewrite <- find_none_append; [| rewrite <- find_none_append ].
  + rewrite in_map_iff in InGbods. destruct InGbods. destruct H0.
    unfold program_gfun_bods_for_type in H1. rewrite filter_In in H1. destruct H1.
    apply in_app_or in H1. destruct H1.
    * rewrite in_map_iff in H1. do 2 destruct H1. subst. discriminate.
    * pose proof (find_none _ _ H). rewrite in_map_iff in H1. do 2 destruct H1. subst.
      apply (in_map fst) in H4. rewrite <- program_has_all_gfun_bods_l in H4.
      rewrite in_map_iff in H4. destruct H4. destruct H1. apply H3 in H4. cbn in *.
      inversion H0; subst. rewrite H1 in H4. rewrite eq_QName_refl in H4. discriminate.
  + pose proof (find_none _ _ H). match goal with [|- ?lhs = _] => case_eq lhs end; intros...
    pose proof (find_some _ _ H1). destruct H2. rewrite in_map_iff in H2. do 2 destruct H2.
    rewrite filter_In in H4. destruct H4. apply H0 in H4. inversion H2; subst. clear - H4 H5 H3.
    cbn in *. rewrite H4 in H3. discriminate.
  + match goal with [|- ?lhs = _] => case_eq lhs end; intros... clear - H0.
    apply find_some in H0. destruct H0. rewrite in_map_iff in H. do 2 destruct H.
    destruct p0. inversion H; subst. clear - H0. cbn in H0. discriminate.
- unfold lookup_gfun_sig_g in H. unfold lookup_gfun_sig_x in H.
  rewrite <- find_none_append; [| rewrite <- find_none_append ].
  + rewrite in_map_iff in InGbods. destruct InGbods. destruct H0.
    unfold program_gfun_bods_for_type in H1. rewrite filter_In in H1. destruct H1.
    apply in_app_or in H1. destruct H1.
    * pose proof (find_none _ _ H). rewrite in_map_iff in H1. do 2 destruct H1. subst.
      apply (in_map fst) in H4. rewrite <- program_has_all_gfun_bods_g in H4.
      rewrite in_map_iff in H4. destruct H4. destruct H1. apply H3 in H4. cbn in *.
      inversion H0; subst. rewrite H1 in H4. rewrite eq_QName_refl in H4. discriminate.
    * rewrite in_map_iff in H1. do 2 destruct H1. subst. discriminate.
  + match goal with [|- ?lhs = _] => case_eq lhs end; intros... clear - H0.
    apply find_some in H0. destruct H0. rewrite in_map_iff in H. do 2 destruct H.
    destruct p0. inversion H; subst. clear - H0. cbn in H0. discriminate.
  + pose proof (find_none _ _ H). match goal with [|- ?lhs = _] => case_eq lhs end; intros...
    pose proof (find_some _ _ H1). destruct H2. rewrite in_map_iff in H2. do 2 destruct H2.
    rewrite filter_In in H4. destruct H4. apply H0 in H4. inversion H2; subst. clear - H4 H5 H3.
    cbn in *. rewrite H4 in H3. discriminate.
Qed.

Lemma no_cfun_no_dtor : forall p tn a
  (InCbods : In a (map fst (program_cfun_bods_for_type tn p))),
  lookup_cfun_sig_scoped (program_skeleton p) a = None ->
  lookup_dtor (refunctionalize_to_skeleton p tn) a = None.
Proof with eauto.
intros. unfold lookup_cfun_sig_scoped in H. cbn in *. unfold computeNewCoDatatype. destruct a.
- unfold lookup_cfun_sig_l in H. unfold lookup_cfun_sig_x in H.
  rewrite <- find_none_append; [| rewrite <- find_none_append ].
  + rewrite in_map_iff in InCbods. destruct InCbods. destruct H0.
    unfold program_cfun_bods_for_type in H1. rewrite filter_In in H1. destruct H1.
    apply in_app_or in H1. destruct H1.
    * rewrite in_map_iff in H1. do 2 destruct H1. subst. discriminate.
    * pose proof (find_none _ _ H). rewrite in_map_iff in H1. do 2 destruct H1. subst.
      apply (in_map fst) in H4. rewrite <- program_has_all_cfun_bods_l in H4.
      rewrite in_map_iff in H4. destruct H4. destruct H1. apply H3 in H4. cbn in *.
      inversion H0; subst. rewrite H1 in H4. rewrite eq_QName_refl in H4. discriminate.
  + pose proof (find_none _ _ H). match goal with [|- ?lhs = _] => case_eq lhs end; intros...
    pose proof (find_some _ _ H1). destruct H2. rewrite in_map_iff in H2. do 2 destruct H2.
    rewrite filter_In in H4. destruct H4. apply H0 in H4. inversion H2; subst. clear - H4 H5 H3.
    cbn in *. rewrite H4 in H3. discriminate.
  + match goal with [|- ?lhs = _] => case_eq lhs end; intros... clear - H0.
    apply find_some in H0. destruct H0. rewrite in_map_iff in H. do 2 destruct H.
    destruct p0. inversion H; subst. clear - H0. cbn in H0. discriminate.
- unfold lookup_cfun_sig_g in H. unfold lookup_cfun_sig_x in H.
  rewrite <- find_none_append; [| rewrite <- find_none_append ].
  + rewrite in_map_iff in InCbods. destruct InCbods. destruct H0.
    unfold program_cfun_bods_for_type in H1. rewrite filter_In in H1. destruct H1.
    apply in_app_or in H1. destruct H1.
    * pose proof (find_none _ _ H). rewrite in_map_iff in H1. do 2 destruct H1. subst.
      apply (in_map fst) in H4. rewrite <- program_has_all_cfun_bods_g in H4.
      rewrite in_map_iff in H4. destruct H4. destruct H1. apply H3 in H4. cbn in *.
      inversion H0; subst. rewrite H1 in H4. rewrite eq_QName_refl in H4. discriminate.
    * rewrite in_map_iff in H1. do 2 destruct H1. subst. discriminate.
  + match goal with [|- ?lhs = _] => case_eq lhs end; intros... clear - H0.
    apply find_some in H0. destruct H0. rewrite in_map_iff in H. do 2 destruct H.
    destruct p0. inversion H; subst. clear - H0. cbn in H0. discriminate.
  + pose proof (find_none _ _ H). match goal with [|- ?lhs = _] => case_eq lhs end; intros...
    pose proof (find_some _ _ H1). destruct H2. rewrite in_map_iff in H2. do 2 destruct H2.
    rewrite filter_In in H4. destruct H4. apply H0 in H4. inversion H2; subst. clear - H4 H5 H3.
    cbn in *. rewrite H4 in H3. discriminate.
Qed.

Fact nth_option_nth_error : forall {A} n (l : list A), nth_option n l = nth_error l n.
Proof with eauto. intros. generalize dependent n. induction l; destruct n... Qed.

Lemma listTypeDeriv_app : forall p ctx ctx' es es' ts ts',
  length ctx = length es ->
  length ctx = length ts ->
  p /// ctx ++ ctx' |||- es ++ es' ::: (ts ++ ts') ->
  p /// ctx' |||- es' ::: ts'.
Proof with eauto.
intros. generalize dependent es. generalize dependent ts. induction ctx; intros.
- destruct es; try discriminate. destruct ts; try discriminate...
- destruct es; try discriminate. destruct ts; try discriminate.
  inversion H1; subst. eapply IHctx...
Qed.

Lemma listTypeDeriv'_app : forall p ctx es es' ts ts',
  length es = length ts ->
  p // ctx ||- (es ++ es') :: (ts ++ ts') ->
  p // ctx ||- es' :: ts'.
Proof with eauto.
intros. generalize dependent ts. generalize dependent ctx. induction es; intros.
- destruct ts; try discriminate...
- destruct ts; try discriminate.
  inversion H0; subst. eapply IHes...
Qed.

Lemma combine_app : forall {A B} (l1 l1' : list A) (l2 l2' : list B),
  length l1 = length l2 ->
  combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
Proof with eauto.
intros. generalize dependent l1'. generalize dependent l2'. generalize dependent l2.
induction l1; intros...
- cbn. destruct l2; try discriminate...
- destruct l2; try discriminate. cbn. f_equal...
Qed.

(* e is subterm of e' with n intermediate lets *)
(* alternative, semantically equivalent variant with inductive structure turned around *)
Inductive subterm_at_depth' : expr -> expr -> nat -> Prop :=
  | Sub'_Refl : forall e, subterm_at_depth' e e 0
  | Sub'_Trans_NoLet : forall e1 e2 e3 n,
      (forall e_1 e_2, e3 <> E_Let e_1 e_2) ->
      (forall q e_0 bs cases t,
        e3 = E_Match q e_0 bs cases t ->
        e2 = e_0 \/ In e2 (map fst bs)) ->
      (forall q bs cocases,
        e3 = E_CoMatch q bs cocases ->
        In e2 (map fst bs)) ->
      subterm_at_depth' e1 e2 n ->
      direct_subterm e2 e3 ->
      subterm_at_depth' e1 e3 n
  | Sub'_Trans_Let_1 : forall e1 e2 e3 e' n,
      e3 = E_Let e2 e' ->
      subterm_at_depth' e1 e2 n ->
      subterm_at_depth' e1 e3 n
  | Sub'_Trans_Let_2 : forall e1 e2 e3 e' n,
      e3 = E_Let e' e2 ->
      subterm_at_depth' e1 e2 n ->
      subterm_at_depth' e1 e3 (S n).

Remark subterm_at_depth'_switch_Trans : forall e1 e2 e3 n,
  subterm_at_depth' e2 e3 n ->
 ((forall e_1 e_2,
    e2 = E_Let e_1 e_2 ->
    e1 = e_1) ->
  (forall q e_0 bs cases t,
    e2 = E_Match q e_0 bs cases t ->
    e1 = e_0 \/ In e1 (map fst bs)) ->
  (forall q bs cocases,
    e2 = E_CoMatch q bs cocases ->
    In e1 (map fst bs)) ->
  direct_subterm e1 e2 ->
  subterm_at_depth' e1 e3 n)
/\
 ((exists e', e2 = E_Let e' e1) ->
  subterm_at_depth' e1 e3 (S n)).
Proof with eauto.
intros. induction H; split; intros.
- destruct e;
  try solve [
    inversion H2; subst; apply Sub'_Trans_NoLet with (e2:=e1);
      intros; try discriminate; try constructor; eauto; try inversion H; eauto ];
  try solve [
    inversion H2; subst;
    [ apply Sub'_Trans_NoLet with (e2:=e)
    | apply Sub'_Trans_NoLet with (e2:=e1) ];
    intros; try discriminate; try constructor; eauto ].
  + pose proof (eq_refl (E_Match q e l l0 t)). apply H0 in H3.
    destruct H3; subst; eapply Sub'_Trans_NoLet; eauto; try constructor; intros;
      unfold not; intros; discriminate.
  + inversion H2; subst.
    * eapply Sub'_Trans_Let_1... constructor.
    * pose proof (eq_refl (E_Let e2 e3)). apply H in H3; subst.
      eapply Sub'_Trans_Let_1... constructor.
- destruct H. eapply Sub'_Trans_Let_2... constructor.
- destruct IHsubterm_at_depth'. eapply Sub'_Trans_NoLet...
- destruct IHsubterm_at_depth'. apply H6 in H4. eapply Sub'_Trans_NoLet...
- destruct IHsubterm_at_depth'. eapply Sub'_Trans_Let_1...
- destruct IHsubterm_at_depth'. eapply Sub'_Trans_Let_1...
- destruct IHsubterm_at_depth'. eapply Sub'_Trans_Let_2...
- destruct IHsubterm_at_depth'. eapply Sub'_Trans_Let_2...
Qed.

Lemma subterm_at_depth_subterm' : forall e1 e2 n,
  subterm_at_depth e1 e2 n -> subterm_at_depth' e1 e2 n.
Proof with eauto.
intros. induction H; intros; subst.
- constructor.
- eapply subterm_at_depth'_switch_Trans...
  intros. exfalso. unfold not in H. eapply H...
- apply subterm_at_depth'_switch_Trans with (e2:=E_Let e1 e');
    try discriminate; try constructor...
  intros. inversion H...
- eapply subterm_at_depth'_switch_Trans...
Qed.

Lemma direct_subterm_no_let_tc : forall p ctx e1 e2 t
  (NoMatch : (forall q e_0 bs cases t,
      e2 = E_Match q e_0 bs cases t ->
      e1 = e_0 \/ In e1 (map fst bs)))
  (NoCoMatch : forall q bs cocases,
      e2 = E_CoMatch q bs cocases ->
      In e1 (map fst bs)),
  (forall e_1 e_2 : expr, e2 <> E_Let e_1 e_2) ->
  direct_subterm e1 e2 ->
  program_skeleton p / ctx |- e2 : t ->
  exists t', program_skeleton p / ctx |- e1 : t'.
Proof with eauto.
intros. inversion H0; subst;
  try solve [ inversion H1; subst; eauto ];
  try solve [ exfalso; unfold not in H; eapply H; eauto ];
  try solve [
    inversion H1; subst;
    apply in_split in H2; do 2 destruct H2; subst;
    try (rename argts into cargs); try (rename dargs into cargs);
    try (rename H9 into H8);
    assert (length x = length (firstn (length x) cargs)); [
      apply listTypeDeriv_lemma in H8; rewrite firstn_length;
      rewrite Nat.eqb_eq in H8; rewrite app_length in H8; cbn in H8;
      rewrite H8; rewrite <- Nat.add_0_r with (n:=length x) at 2;
      rewrite Nat.add_min_distr_l; eauto
    | ];
    rewrite <- firstn_skipn with (l:=cargs)(n:=length x) in H8;
    pose proof (listTypeDeriv'_app _ _ _ _ _ _ H2 H8);
    inversion H3; subst; eexists; eauto
  ];
  try solve [
    inversion H1; subst;
    apply in_split in H2; do 2 destruct H2; subst;
    try (rename argts into cargs); try (rename H8 into InDargs); try (rename H11 into H8);
    assert (length x = length (firstn (length x) dargs)); [
      apply listTypeDeriv_lemma in H8; rewrite firstn_length;
      rewrite Nat.eqb_eq in H8; rewrite app_length in H8; cbn in H8;
      rewrite H8; rewrite <- Nat.add_0_r with (n:=length x) at 2;
      rewrite Nat.add_min_distr_l; eauto
    | ];
    rewrite <- firstn_skipn with (l:=dargs)(n:=length x) in H8;
    pose proof (listTypeDeriv'_app _ _ _ _ _ _ H2 H8);
    inversion H3; subst; eexists; eauto
  ].
- inversion H1; subst;
  apply in_split in H2; do 2 destruct H2; subst;
    try (rename argts into cargs); try (rename H9 into H8);
    assert (length x = length (firstn (length x) cargs)); [
      apply listTypeDeriv_lemma in H8; rewrite firstn_length;
      rewrite Nat.eqb_eq in H8; rewrite app_length in H8; cbn in H8;
      rewrite H8; rewrite <- Nat.add_0_r with (n:=length x) at 2;
      rewrite Nat.add_min_distr_l; eauto
    |
    | apply listTypeDeriv_lemma in H8; rewrite firstn_length;
      rewrite Nat.eqb_eq in H8; rewrite app_length in H8; cbn in H8;
      rewrite H8; rewrite <- Nat.add_0_r with (n:=length x) at 2;
      rewrite Nat.add_min_distr_l; eauto
    | ];
    rewrite <- firstn_skipn with (l:=cargs)(n:=length x) in H8;
    pose proof (listTypeDeriv'_app _ _ _ _ _ _ H2 H8);
    inversion H3; subst; eexists; eauto.
- inversion H1; subst;
    inversion H1; subst;
    apply in_split in H2; do 2 destruct H2; subst;
    try (rename H8 into InDargs); try (rename H11 into H8);
    assert (length x = length (firstn (length x) argts)); [
      apply listTypeDeriv_lemma in H8; rewrite firstn_length;
      rewrite Nat.eqb_eq in H8; rewrite app_length in H8; cbn in H8;
      rewrite H8; rewrite <- Nat.add_0_r with (n:=length x) at 2;
      rewrite Nat.add_min_distr_l; eauto
    |
    | apply listTypeDeriv_lemma in H8; rewrite firstn_length;
      rewrite Nat.eqb_eq in H8; rewrite app_length in H8; cbn in H8;
      rewrite H8; rewrite <- Nat.add_0_r with (n:=length x) at 2;
      rewrite Nat.add_min_distr_l; eauto
    | ];
    rewrite <- firstn_skipn with (l:=argts)(n:=length x) in H8;
    pose proof (listTypeDeriv'_app _ _ _ _ _ _ H2 H8);
    inversion H3; subst; eexists; eauto.
- inversion H1; subst.
  apply in_split in H2; do 2 destruct H2.
  rewrite map_fst_combine in H2;
    [ | symmetry; rewrite <- Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto ]; subst.
  assert (length x = length (firstn (length x) bindings_types)).
  { apply listTypeDeriv_lemma in H13; rewrite firstn_length;
    rewrite Nat.eqb_eq in H13; rewrite app_length in H13; cbn in H13;
    rewrite H13; rewrite <- Nat.add_0_r with (n:=length x) at 2;
    rewrite Nat.add_min_distr_l...
  }
  rewrite <- firstn_skipn with (l:=bindings_types)(n:=length x) in H13.
  pose proof (listTypeDeriv'_app _ _ _ _ _ _ H2 H13).
  inversion H3; subst; eexists...
- inversion H1; subst.
  pose proof (eq_refl (E_Match q e0 (combine bindings_exprs bindings_types) cases t)).
  apply NoMatch in H3. destruct H3; subst; [ eexists; eauto |].
  clear H2. rename H3 into H2.
  apply in_split in H2; do 2 destruct H2.
  rewrite map_fst_combine in H2;
    [ | symmetry; rewrite <- Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto ]; subst.
  assert (length x = length (firstn (length x) bindings_types)).
  { apply listTypeDeriv_lemma in H13; rewrite firstn_length;
    rewrite Nat.eqb_eq in H13; rewrite app_length in H13; cbn in H13;
    rewrite H13; rewrite <- Nat.add_0_r with (n:=length x) at 2;
    rewrite Nat.add_min_distr_l...
  }
  rewrite <- firstn_skipn with (l:=bindings_types)(n:=length x) in H13.
  pose proof (listTypeDeriv'_app _ _ _ _ _ _ H2 H13).
  inversion H3; subst; eexists...
- inversion H1; subst.
  apply in_split in H2; do 2 destruct H2.
  rewrite map_fst_combine in H2;
    [ | symmetry; rewrite <- Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto ]; subst.
  assert (length x = length (firstn (length x) bindings_types)).
  { apply listTypeDeriv_lemma in H7; rewrite firstn_length;
    rewrite Nat.eqb_eq in H7; rewrite app_length in H7; cbn in H7;
    rewrite H7; rewrite <- Nat.add_0_r with (n:=length x) at 2;
    rewrite Nat.add_min_distr_l...
  }
  rewrite <- firstn_skipn with (l:=bindings_types)(n:=length x) in H7.
  pose proof (listTypeDeriv'_app _ _ _ _ _ _ H2 H7).
  inversion H3; subst; eexists...
- inversion H1; subst.
  pose proof (eq_refl (E_CoMatch q (combine bindings_exprs bindings_types) cocases)).
  apply NoCoMatch in H3.
  clear H2. rename H3 into H2.
  apply in_split in H2; do 2 destruct H2.
  rewrite map_fst_combine in H2;
    [ | symmetry; rewrite <- Nat.eqb_eq; eapply listTypeDeriv_lemma; eauto ]; subst.
  assert (length x = length (firstn (length x) bindings_types)).
  { apply listTypeDeriv_lemma in H7; rewrite firstn_length;
    rewrite Nat.eqb_eq in H7; rewrite app_length in H7; cbn in H7;
    rewrite H7; rewrite <- Nat.add_0_r with (n:=length x) at 2;
    rewrite Nat.add_min_distr_l...
  }
  rewrite <- firstn_skipn with (l:=bindings_types)(n:=length x) in H7.
  pose proof (listTypeDeriv'_app _ _ _ _ _ _ H2 H7).
  inversion H3; subst; eexists...
Qed.

Lemma direct_subterm_let_1_tc : forall p ctx e1 e_2 t,
  program_skeleton p / ctx |- (E_Let e1 e_2) : t ->
  exists t', program_skeleton p / ctx |- e1 : t'.
Proof with eauto.
intros. inversion H; subst...
Qed.

Lemma direct_subterm_let_2_tc : forall p ctx e_1 e2 t,
  program_skeleton p / ctx |- (E_Let e_1 e2) : t ->
  exists t' c, program_skeleton p / (c::ctx) |- e2 : t'.
Proof with eauto.
intros. inversion H; subst...
Qed.

Lemma subterm_depth_n_tc : forall p e e' n ctx t,
  subterm_at_depth e' e n ->
  program_skeleton p / ctx |- e : t ->
  exists t' ctx',
    length ctx' = n /\
    program_skeleton p / (ctx' ++ ctx) |- e' : t'.
Proof with eauto.
intros. apply subterm_at_depth_subterm' in H.
generalize dependent t. generalize dependent ctx.
induction H; intros...
- exists t. exists []. split...
- pose proof (direct_subterm_no_let_tc _ _ _ _ _ H0 H1 H H3 H4).
  destruct H5. eapply IHsubterm_at_depth'...
- subst. pose proof (direct_subterm_let_1_tc _ _ _ _ _ H1).
  destruct H. eapply IHsubterm_at_depth'...
- subst. pose proof (direct_subterm_let_2_tc _ _ _ _ _ H1).
  do 2 destruct H.
  apply IHsubterm_at_depth' in H. do 3 destruct H.
  exists x1. exists (x2++[x0]). split.
  + rewrite app_length. cbn. omega.
  + rewrite <- app_assoc...
Qed.

Lemma E_Var_lt : forall p tn a a0 e g d a' i n
  (InProg : In (a0, e) a' /\ In (a, a') (program_gfun_bods_for_type tn p))
  (Aux : tn = fst (unscope a0)),
  lookup_dtor (program_skeleton p) a0 = Some d ->
  Some g = lookup_gfun_sig_scoped (program_skeleton p) a ->
  subterm_at_depth (E_Var i) e n ->
  i < length (snd (fst d)) + length (snd g) + n.
Proof with eauto.
intros.
- rename H1 into Sub. destruct InProg. unfold program_gfun_bods_for_type in H2.
  rewrite filter_In in H2. destruct H2. apply in_app_or in H2. destruct H2.
  * rewrite in_map_iff in H2. do 2 destruct H2. pose proof (program_gfun_bods_typecheck_g p) as TypG.
    unfold gfun_bods_g_typecheck in TypG. rewrite Forall_forall in TypG. apply TypG in H4.
    do 3 destruct H4. inversion H5; subst. inversion H2; subst. pose proof H1 as  H1'.
    apply (in_map snd) in H1. cbn in H1. clear - H1 H1' H14 H15 H H0 H4 H13 H9 H10 Sub.
    rename H into Dtor. rename H0 into Gsig. rename H4 into LookupSig. rename H13 into dtorlistEq.
    rename H9 into Btypes. rename H10 into BtypesLen. apply listTypeDeriv_lemma in BtypesLen.
    assert (exists ctx t, (program_skeleton p / ctx |- e : t) /\
      length ctx <= length (snd (fst d)) + length (snd g)).
    { apply in_split in H1'. destruct H1'. destruct H. unfold gfun_bod in *. rewrite H in *.
      clear - H14 H15 Dtor Gsig LookupSig dtorlistEq Btypes BtypesLen.
      rewrite <- firstn_skipn with (l:=dtorlist)(n:=length x2) in H15.
      repeat rewrite map_app in H15. apply listTypeDeriv_app in H15.
      2:{ repeat rewrite map_length... rewrite firstn_length. repeat rewrite <- map_app in H15.
        rewrite firstn_skipn in H15. apply listTypeDeriv'_lemma in H15.
        rewrite Nat.eqb_eq in H15. rewrite map_length in H15. rewrite H15. rewrite map_length.
        rewrite app_length. cbn. apply min_l. omega.
      }
      2:{ repeat rewrite map_length... }
      inversion H15; subst. exists ctx. exists t. split...
      case_eq (skipn (length x2) dtorlist); intros; rewrite H0 in H; try discriminate.
      inversion H; subst. rewrite <- firstn_skipn with (l:=dtorlist)(n:=length x2) in H14.
      rewrite combine_app in H14. 2:{ rewrite firstn_length.
        case_eq (length x2 <? length dtorlist); intros.
        - rewrite Nat.ltb_lt in H1. symmetry. apply min_l. omega.
        - rewrite Nat.ltb_ge in H1. clear - H0 H1. exfalso.
          assert (skipn (length x2) dtorlist = []).
          { clear - H1. generalize dependent (length x2). intros.
            generalize dependent dtorlist. induction n; intros.
            - cbn. destruct dtorlist... cbn in H1. omega.
            - destruct dtorlist... cbn in *. apply IHn. omega.
          }
          rewrite H in H0. discriminate.
      }
      rewrite <- Forall_app_iff in H14. destruct H14 as [_ Almost1].
      assert (snd (fst p0) = snd (fst d)).
      { rewrite H0 in Almost1. inversion Almost1; subst. destruct p0. destruct p0. subst. cbn.
        clear - H0 Dtor dtorlistEq. unfold lookup_dtors in dtorlistEq.
        case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
          rewrite H in dtorlistEq; try discriminate.
        inversion dtorlistEq; subst. clear dtorlistEq.
        pose proof (in_eq (s,l0,t0) l). rewrite <- H0 in H1. apply skipn_In in H1.
        rewrite filter_In in H1. destruct H1.
        unfold lookup_dtor in Dtor. apply find_some in Dtor. destruct Dtor. clear - H3 H4 H1.
        pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)).
        unfold cdts_dtor_names_unique in H. generalize dependent (skeleton_dtors (program_skeleton p)).
        intros. induction d0; [inversion H3 |].
        inversion H3; subst.
        - inversion H1; subst... inversion H; subst. destruct d. destruct p0. cbn in *.
          rewrite eq_ScopedName_eq in H4. subst s0. do 2 apply (in_map fst) in H0.
          rewrite map_map in H0. apply H6 in H0. exfalso...
        - inversion H1; subst.
          + inversion H; subst. destruct d. destruct p0. cbn in *.
            rewrite eq_ScopedName_eq in H4. subst s0. destruct H3; try inversion H2...
            do 2 apply (in_map fst) in H2. rewrite map_map in H2. apply H6 in H2. exfalso...
          + inversion H; subst. apply IHd0...
      }
      rewrite H1.
      assert (bindings_types = snd g).
      { clear - LookupSig Gsig Btypes BtypesLen.
        destruct g. cbn. unfold lookup_gfun_sig_scoped in Gsig.
        unfold lookup_gfun_sig_g in *. rewrite LookupSig in Gsig. inversion Gsig; subst.
        clear - Btypes BtypesLen. generalize dependent bindings_types.
        generalize dependent bindings_exprs. generalize 0.
        induction x1; intros.
        { cbn in Btypes. rewrite Nat.eqb_eq in BtypesLen. destruct bindings_types...
          destruct bindings_exprs; discriminate.
        }
        destruct bindings_types. { destruct bindings_exprs; discriminate. }
        cbn in Btypes. destruct bindings_exprs; try discriminate.
        cbn in Btypes. inversion Btypes; subst. f_equal...
      }
      rewrite H2. rewrite app_length. omega.
    }
    do 3 destruct H. pose proof (subterm_depth_n_tc _ _ _ _ _ _ Sub H).
    do 3 destruct H2. inversion H3; subst. rewrite nth_option_nth_error in H7.
    assert (nth_error (x5 ++ x2) i <> None). { unfold not. intros. rewrite H2 in H7. discriminate. }
    apply nth_error_Some in H2. rewrite app_length in H2. omega.
  * rewrite in_map_iff in H2. do 2 destruct H2. pose proof (program_gfun_bods_typecheck_l p) as TypL.
    unfold gfun_bods_l_typecheck in TypL. rewrite Forall_forall in TypL. apply TypL in H4.
    do 3 destruct H4. inversion H5; subst. inversion H2; subst. pose proof H1 as  H1'.
    apply (in_map snd) in H1. cbn in H1. clear - H1 H1' H14 H15 H H0 H4 H13 H9 H10 Sub.
    rename H into Dtor. rename H0 into Gsig. rename H4 into LookupSig. rename H13 into dtorlistEq.
    rename H9 into Btypes. rename H10 into BtypesLen. apply listTypeDeriv_lemma in BtypesLen.
    assert (exists ctx t, (program_skeleton p / ctx |- e : t) /\
      length ctx <= length (snd (fst d)) + length (snd g)).
    { apply in_split in H1'. destruct H1'. destruct H. unfold gfun_bod in *. rewrite H in *.
      clear - H14 H15 Dtor Gsig LookupSig dtorlistEq Btypes BtypesLen.
      rewrite <- firstn_skipn with (l:=dtorlist)(n:=length x2) in H15.
      repeat rewrite map_app in H15. apply listTypeDeriv_app in H15.
      2:{ repeat rewrite map_length... rewrite firstn_length. repeat rewrite <- map_app in H15.
        rewrite firstn_skipn in H15. apply listTypeDeriv'_lemma in H15.
        rewrite Nat.eqb_eq in H15. rewrite map_length in H15. rewrite H15. rewrite map_length.
        rewrite app_length. cbn. apply min_l. omega.
      }
      2:{ repeat rewrite map_length... }
      inversion H15; subst. exists ctx. exists t. split...
      case_eq (skipn (length x2) dtorlist); intros; rewrite H0 in H; try discriminate.
      inversion H; subst. rewrite <- firstn_skipn with (l:=dtorlist)(n:=length x2) in H14.
      rewrite combine_app in H14. 2:{ rewrite firstn_length.
        case_eq (length x2 <? length dtorlist); intros.
        - rewrite Nat.ltb_lt in H1. symmetry. apply min_l. omega.
        - rewrite Nat.ltb_ge in H1. clear - H0 H1. exfalso.
          assert (skipn (length x2) dtorlist = []).
          { clear - H1. generalize dependent (length x2). intros.
            generalize dependent dtorlist. induction n; intros.
            - cbn. destruct dtorlist... cbn in H1. omega.
            - destruct dtorlist... cbn in *. apply IHn. omega.
          }
          rewrite H in H0. discriminate.
      }
      rewrite <- Forall_app_iff in H14. destruct H14 as [_ Almost1].
      assert (snd (fst p0) = snd (fst d)).
      { rewrite H0 in Almost1. inversion Almost1; subst. destruct p0. destruct p0. subst. cbn.
        clear - H0 Dtor dtorlistEq. unfold lookup_dtors in dtorlistEq.
        case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
          rewrite H in dtorlistEq; try discriminate.
        inversion dtorlistEq; subst. clear dtorlistEq.
        pose proof (in_eq (s,l0,t0) l). rewrite <- H0 in H1. apply skipn_In in H1.
        rewrite filter_In in H1. destruct H1.
        unfold lookup_dtor in Dtor. apply find_some in Dtor. destruct Dtor. clear - H3 H4 H1.
        pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)).
        unfold cdts_dtor_names_unique in H. generalize dependent (skeleton_dtors (program_skeleton p)).
        intros. induction d0; [inversion H3 |].
        inversion H3; subst.
        - inversion H1; subst... inversion H; subst. destruct d. destruct p0. cbn in *.
          rewrite eq_ScopedName_eq in H4. subst s0. do 2 apply (in_map fst) in H0.
          rewrite map_map in H0. apply H6 in H0. exfalso...
        - inversion H1; subst.
          + inversion H; subst. destruct d. destruct p0. cbn in *.
            rewrite eq_ScopedName_eq in H4. subst s0. destruct H3; try inversion H2...
            do 2 apply (in_map fst) in H2. rewrite map_map in H2. apply H6 in H2. exfalso...
          + inversion H; subst. apply IHd0...
      }
      rewrite H1.
      assert (bindings_types = snd g).
      { clear - LookupSig Gsig Btypes BtypesLen.
        destruct g. cbn. unfold lookup_gfun_sig_scoped in Gsig.
        unfold lookup_gfun_sig_g in *. rewrite LookupSig in Gsig. inversion Gsig; subst.
        clear - Btypes BtypesLen. generalize dependent bindings_types.
        generalize dependent bindings_exprs. generalize 0.
        induction x1; intros.
        { cbn in Btypes. rewrite Nat.eqb_eq in BtypesLen. destruct bindings_types...
          destruct bindings_exprs; discriminate.
        }
        destruct bindings_types. { destruct bindings_exprs; discriminate. }
        cbn in Btypes. destruct bindings_exprs; try discriminate.
        cbn in Btypes. inversion Btypes; subst. f_equal...
      }
      rewrite H2. rewrite app_length. omega.
    }
    do 3 destruct H. pose proof (subterm_depth_n_tc _ _ _ _ _ _ Sub H).
    do 3 destruct H2. inversion H3; subst. rewrite nth_option_nth_error in H7.
    assert (nth_error (x5 ++ x2) i <> None). { unfold not. intros. rewrite H2 in H7. discriminate. }
    apply nth_error_Some in H2. rewrite app_length in H2. omega.
Qed.

Lemma E_Var_lt' : forall p tn a a0 e c0 c a' i n
  (InProg : In (a0, e) a' /\ In (a, a') (program_cfun_bods_for_type tn p))
  (Aux : tn = fst (unscope a0)),
  lookup_ctor_sig (program_skeleton p) a0 = Some c ->
  Some c0 = lookup_cfun_sig_scoped (program_skeleton p) a ->
  subterm_at_depth (E_Var i) e n ->
  i < length (snd c) + length (snd (fst c0)) + n.
Proof with eauto.
intros.
- rename H1 into Sub. destruct InProg. unfold program_cfun_bods_for_type in H2.
  rewrite filter_In in H2. destruct H2. apply in_app_or in H2. destruct H2.
  * rewrite in_map_iff in H2. do 2 destruct H2. pose proof (program_cfun_bods_typecheck_g p) as TypG.
    unfold cfun_bods_g_typecheck in TypG. rewrite Forall_forall in TypG. apply TypG in H4.
    do 4 destruct H4. inversion H5; subst. inversion H2; subst. pose proof H1 as  H1'.
    apply (in_map snd) in H1. cbn in H1. clear - H1 H1' H18 H19 H H0 H4 H17 H14 H16 Sub.
    rename H into Ctor. rename H0 into Csig. rename H4 into LookupSig. rename H17 into ctorlistEq.
    rename H14 into Btypes. rename H16 into BtypesLen. apply listTypeDeriv_lemma in BtypesLen.
    assert (exists ctx t, (program_skeleton p / ctx |- e : t) /\
      length ctx <= length (snd c) + length (snd (fst c0))).
    { apply in_split in H1'. destruct H1'. destruct H. unfold cfun_bod in *. rewrite H in *.
      clear - H18 H19 Ctor Csig LookupSig ctorlistEq Btypes BtypesLen.
      assert (length x3 <= length ctorlist) as LenAux.
      { apply listTypeDeriv'_lemma_ctx in H19. rewrite Nat.eqb_eq in H19.
        repeat rewrite map_length in H19. rewrite app_length in H19. omega.
      }
      rewrite <- firstn_skipn with (l:=ctorlist)(n:=length x3) in H19.
      repeat rewrite map_app in H19.
      replace (repeat x2 (length (x3 ++ (a0, e) :: x4))) with
        (repeat x2 (length x3) ++ repeat x2 (S (length x4))) in H19.
      2:{ rewrite app_length. cbn [length]. generalize (length x3). generalize (length x4). clear.
        induction n; intros. { induction n... cbn. rewrite <- IHn... }
        replace (n0 + S (S n)) with ((S n0) + S n); try omega.
        rewrite <- IHn. cbn. rewrite app_comm_cons.
        replace (x2 :: repeat x2 n0) with (repeat x2 n0 ++ [x2]); [rewrite <- app_assoc |]...
        clear. induction n0... cbn. f_equal...
      }
      apply listTypeDeriv_app in H19.
      2:{ repeat rewrite map_length... rewrite firstn_length. repeat rewrite <- map_app in H19.
        rewrite firstn_skipn in H19. apply listTypeDeriv'_lemma_ctx in H19.
        rewrite Nat.eqb_eq in H19. rewrite map_length in H19. rewrite H19. rewrite map_length.
        rewrite app_length. cbn. apply min_l. omega.
      }
      2:{ repeat rewrite map_length. rewrite firstn_length. rewrite min_l... rewrite repeat_length... }
      inversion H19; subst. exists ctx. exists x2. split...
      case_eq (skipn (length x3) ctorlist); intros; rewrite H0 in H; try discriminate.
      inversion H; subst. rewrite <- firstn_skipn with (l:=ctorlist)(n:=length x3) in H18.
      rewrite combine_app in H18. 2:{ rewrite firstn_length.
        case_eq (length x3 <? length ctorlist); intros.
        - rewrite Nat.ltb_lt in H1. symmetry. apply min_l. omega.
        - rewrite Nat.ltb_ge in H1. clear - H0 H1. exfalso.
          assert (skipn (length x3) ctorlist = []).
          { clear - H1. generalize dependent (length x3). intros.
            generalize dependent ctorlist. induction n; intros.
            - cbn. destruct ctorlist... cbn in H1. omega.
            - destruct ctorlist... cbn in *. apply IHn. omega.
          }
          rewrite H in H0. discriminate.
      }
      rewrite <- Forall_app_iff in H18. destruct H18 as [_ Almost1].
      assert (snd p0 = snd c).
      { rewrite H0 in Almost1. inversion Almost1; subst. destruct p0. subst. cbn.
        clear - H0 Ctor ctorlistEq. unfold lookup_ctors in ctorlistEq.
        case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
          rewrite H in ctorlistEq; try discriminate.
        inversion ctorlistEq; subst. clear ctorlistEq.
        pose proof (in_eq (s,l0) l). rewrite <- H0 in H1. apply skipn_In in H1.
        rewrite filter_In in H1. destruct H1.
        unfold lookup_ctor_sig in Ctor. apply find_some in Ctor. destruct Ctor. clear - H3 H4 H1.
        pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)).
        unfold dts_ctor_names_unique in H. generalize dependent (skeleton_ctors (program_skeleton p)).
        intros. induction c0; [inversion H3 |].
        inversion H3; subst.
        - inversion H1; subst... inversion H; subst. destruct c. cbn in *.
          rewrite eq_ScopedName_eq in H4. subst s0. apply (in_map fst) in H0.
          apply H6 in H0. exfalso...
        - inversion H1; subst.
          + inversion H; subst. destruct c. cbn in *.
            rewrite eq_ScopedName_eq in H4. subst s0. destruct H3; try inversion H2...
            apply (in_map fst) in H2. apply H6 in H2. exfalso...
          + inversion H; subst. apply IHc0...
      }
      rewrite H1.
      assert (bindings_types = snd (fst c0)).
      { clear - LookupSig Csig Btypes BtypesLen.
        destruct c0. cbn. unfold lookup_cfun_sig_scoped in Csig.
        unfold lookup_cfun_sig_g in *. rewrite LookupSig in Csig. inversion Csig; subst.
        clear - Btypes BtypesLen. generalize dependent bindings_types.
        generalize dependent bindings_exprs. generalize 0.
        induction x1; intros.
        { cbn in Btypes. rewrite Nat.eqb_eq in BtypesLen. destruct bindings_types...
          destruct bindings_exprs; discriminate.
        }
        destruct bindings_types. { destruct bindings_exprs; discriminate. }
        cbn in Btypes. destruct bindings_exprs; try discriminate.
        cbn in Btypes. inversion Btypes; subst. cbn. f_equal...
      }
      rewrite H2. rewrite app_length. omega.
    }
    do 3 destruct H. pose proof (subterm_depth_n_tc _ _ _ _ _ _ Sub H).
    do 3 destruct H2. inversion H3; subst. rewrite nth_option_nth_error in H7.
    assert (nth_error (x6 ++ x3) i <> None). { unfold not. intros. rewrite H2 in H7. discriminate. }
    apply nth_error_Some in H2. rewrite app_length in H2. omega.
  * rewrite in_map_iff in H2. do 2 destruct H2. pose proof (program_cfun_bods_typecheck_l p) as TypL.
    unfold cfun_bods_l_typecheck in TypL. rewrite Forall_forall in TypL. apply TypL in H4.
    do 4 destruct H4. inversion H5; subst. inversion H2; subst. pose proof H1 as  H1'.
    apply (in_map snd) in H1. cbn in H1. clear - H1 H1' H18 H19 H H0 H4 H17 H14 H16 Sub.
    rename H into Ctor. rename H0 into Csig. rename H4 into LookupSig. rename H17 into ctorlistEq.
    rename H14 into Btypes. rename H16 into BtypesLen. apply listTypeDeriv_lemma in BtypesLen.
    assert (exists ctx t, (program_skeleton p / ctx |- e : t) /\
      length ctx <= length (snd c) + length (snd (fst c0))).
    { apply in_split in H1'. destruct H1'. destruct H. unfold cfun_bod in *. rewrite H in *.
      clear - H18 H19 Ctor Csig LookupSig ctorlistEq Btypes BtypesLen.
      assert (length x3 <= length ctorlist) as LenAux.
      { apply listTypeDeriv'_lemma_ctx in H19. rewrite Nat.eqb_eq in H19.
        repeat rewrite map_length in H19. rewrite app_length in H19. omega.
      }
      rewrite <- firstn_skipn with (l:=ctorlist)(n:=length x3) in H19.
      repeat rewrite map_app in H19.
      replace (repeat x2 (length (x3 ++ (a0, e) :: x4))) with
        (repeat x2 (length x3) ++ repeat x2 (S (length x4))) in H19.
      2:{ rewrite app_length. cbn [length]. generalize (length x3). generalize (length x4). clear.
        induction n; intros. { induction n... cbn. rewrite <- IHn... }
        replace (n0 + S (S n)) with ((S n0) + S n); try omega.
        rewrite <- IHn. cbn. rewrite app_comm_cons.
        replace (x2 :: repeat x2 n0) with (repeat x2 n0 ++ [x2]); [rewrite <- app_assoc |]...
        clear. induction n0... cbn. f_equal...
      }
      apply listTypeDeriv_app in H19.
      2:{ repeat rewrite map_length... rewrite firstn_length. repeat rewrite <- map_app in H19.
        rewrite firstn_skipn in H19. apply listTypeDeriv'_lemma_ctx in H19.
        rewrite Nat.eqb_eq in H19. rewrite map_length in H19. rewrite H19. rewrite map_length.
        rewrite app_length. cbn. apply min_l. omega.
      }
      2:{ repeat rewrite map_length. rewrite firstn_length. rewrite min_l... rewrite repeat_length... }
      inversion H19; subst. exists ctx. exists x2. split...
      case_eq (skipn (length x3) ctorlist); intros; rewrite H0 in H; try discriminate.
      inversion H; subst. rewrite <- firstn_skipn with (l:=ctorlist)(n:=length x3) in H18.
      rewrite combine_app in H18. 2:{ rewrite firstn_length.
        case_eq (length x3 <? length ctorlist); intros.
        - rewrite Nat.ltb_lt in H1. symmetry. apply min_l. omega.
        - rewrite Nat.ltb_ge in H1. clear - H0 H1. exfalso.
          assert (skipn (length x3) ctorlist = []).
          { clear - H1. generalize dependent (length x3). intros.
            generalize dependent ctorlist. induction n; intros.
            - cbn. destruct ctorlist... cbn in H1. omega.
            - destruct ctorlist... cbn in *. apply IHn. omega.
          }
          rewrite H in H0. discriminate.
      }
      rewrite <- Forall_app_iff in H18. destruct H18 as [_ Almost1].
      assert (snd p0 = snd c).
      { rewrite H0 in Almost1. inversion Almost1; subst. destruct p0. subst. cbn.
        clear - H0 Ctor ctorlistEq. unfold lookup_ctors in ctorlistEq.
        case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
          rewrite H in ctorlistEq; try discriminate.
        inversion ctorlistEq; subst. clear ctorlistEq.
        pose proof (in_eq (s,l0) l). rewrite <- H0 in H1. apply skipn_In in H1.
        rewrite filter_In in H1. destruct H1.
        unfold lookup_ctor_sig in Ctor. apply find_some in Ctor. destruct Ctor. clear - H3 H4 H1.
        pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)).
        unfold dts_ctor_names_unique in H. generalize dependent (skeleton_ctors (program_skeleton p)).
        intros. induction c0; [inversion H3 |].
        inversion H3; subst.
        - inversion H1; subst... inversion H; subst. destruct c. cbn in *.
          rewrite eq_ScopedName_eq in H4. subst s0. apply (in_map fst) in H0.
          apply H6 in H0. exfalso...
        - inversion H1; subst.
          + inversion H; subst. destruct c. cbn in *.
            rewrite eq_ScopedName_eq in H4. subst s0. destruct H3; try inversion H2...
            apply (in_map fst) in H2. apply H6 in H2. exfalso...
          + inversion H; subst. apply IHc0...
      }
      rewrite H1.
      assert (bindings_types = snd (fst c0)).
      { clear - LookupSig Csig Btypes BtypesLen.
        destruct c0. cbn. unfold lookup_cfun_sig_scoped in Csig.
        unfold lookup_cfun_sig_g in *. rewrite LookupSig in Csig. inversion Csig; subst.
        clear - Btypes BtypesLen. generalize dependent bindings_types.
        generalize dependent bindings_exprs. generalize 0.
        induction x1; intros.
        { cbn in Btypes. rewrite Nat.eqb_eq in BtypesLen. destruct bindings_types...
          destruct bindings_exprs; discriminate.
        }
        destruct bindings_types. { destruct bindings_exprs; discriminate. }
        cbn in Btypes. destruct bindings_exprs; try discriminate.
        cbn in Btypes. inversion Btypes; subst. cbn. f_equal...
      }
      rewrite H2. rewrite app_length. omega.
    }
    do 3 destruct H. pose proof (subterm_depth_n_tc _ _ _ _ _ _ Sub H).
    do 3 destruct H2. inversion H3; subst. rewrite nth_option_nth_error in H7.
    assert (nth_error (x6 ++ x3) i <> None). { unfold not. intros. rewrite H2 in H7. discriminate. }
    apply nth_error_Some in H2. rewrite app_length in H2. omega.
Qed.

Lemma switch_indices_aux_inverse : forall p tn a a0 e c d a'
  (InProg : In (a0, e) a' /\ In (a, a') (program_gfun_bods_for_type tn p))
  (DefuncCdt : forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn)
  (DefuncCdt2 : In tn (skeleton_cdts (program_skeleton p))),
  lookup_ctor_sig (defunctionalize_to_skeleton p tn) a = Some c ->
  lookup_dtor (program_skeleton p) a0 = Some d ->
  tn = fst (unscope a0) ->
  switch_indices_aux (defunctionalize_to_skeleton p tn) a0 (length (snd c)) tn
  (DefuncIII.switch_indices_aux (program_skeleton p) a (length (snd (fst d))) tn e) = e.
Proof with eauto.
intros. unfold switch_indices_aux. unfold DefuncIII.switch_indices_aux.
unfold switch_indices_cfun.
remember (lookup_cfun_sig_scoped (defunctionalize_to_skeleton p tn) a0) as csig.
destruct csig.
- cbn. unfold switch_indices. remember (lookup_gfun_sig_scoped (program_skeleton p) a) as gsig.
  destruct gsig.
  + cbn. replace (length (snd c)) with (length (snd g)).
    2:{ destruct InProg. apply (in_map fst) in H3. cbn in H3. eapply ctor_gsig_length... }
    replace (length (snd (fst c0))) with (length (snd (fst d))).
    2:{ eapply dtor_csig_length... unfold lookup_dtor in H0. apply find_some in H0.
      destruct H0. rewrite eq_ScopedName_eq in H2. subst...
    }
    rewrite switch_indices_helper_defunc_exchange.
    rewrite switch_indices_helper_inverse.
    2:{ intros. eapply E_Var_lt... }
    apply derefunc_exp_inverse with (p:=p)...
    clear - InProg. left. rewrite in_map_iff. exists (a0,e). split... rewrite in_flat_map.
    exists (a,a'). destruct InProg. split...
    unfold program_gfun_bods_for_type in H0. rewrite filter_In in H0. destruct H0...
  + exfalso. clear - H Heqgsig InProg. destruct InProg. symmetry in Heqgsig.
    apply (in_map fst) in H1. cbn in H1. rewrite no_gfun_no_ctor in H... discriminate.
- cbn. unfold switch_indices. remember (lookup_gfun_sig_scoped (program_skeleton p) a) as gsig.
  destruct gsig.
  + exfalso. clear - H0 Heqcsig H1. rename Heqcsig into H. unfold lookup_cfun_sig_scoped in H.
    destruct a0.
    * unfold lookup_cfun_sig_l in H. unfold lookup_cfun_sig_x in H. cbn in H.
      unfold DefuncI.new_cfunsigs_l in H. symmetry in H.
      apply find_none with (x:=(unscope (fst (fst d)), snd (fst d), snd d)) in H.
      2:{ apply in_or_app. left. rewrite in_map_iff. unfold cfunsigs_mapfun. exists d.
        split. { destruct d. destruct p0... }
        unfold lookup_dtor in H0. apply find_some in H0. rewrite filter_In. destruct H0.
        split... rewrite eq_ScopedName_eq in H2. unfold cfunsigs_filterfun_l. destruct d.
        destruct p0. cbn in H2. subst. cbn. apply eq_TypeName_refl.
      }
      cbn in H. unfold lookup_dtor in H0. apply find_some in H0. destruct H0.
      rewrite eq_ScopedName_eq in H2. rewrite <- H2 in H. cbn in H. rewrite eq_QName_refl in H.
      discriminate.
    * unfold lookup_cfun_sig_g in H. unfold lookup_cfun_sig_x in H. cbn in H.
      unfold DefuncI.new_cfunsigs_l in H. symmetry in H.
      apply find_none with (x:=(unscope (fst (fst d)), snd (fst d), snd d)) in H.
      2:{ apply in_or_app. left. rewrite in_map_iff. unfold cfunsigs_mapfun. exists d.
        split. { destruct d. destruct p0... }
        unfold lookup_dtor in H0. apply find_some in H0. rewrite filter_In. destruct H0.
        split... rewrite eq_ScopedName_eq in H2. unfold cfunsigs_filterfun_l. destruct d.
        destruct p0. cbn in H2. subst. cbn. apply eq_TypeName_refl.
      }
      cbn in H. unfold lookup_dtor in H0. apply find_some in H0. destruct H0.
      rewrite eq_ScopedName_eq in H2. rewrite <- H2 in H. cbn in H. rewrite eq_QName_refl in H.
      discriminate.
  + cbn. apply derefunc_exp_inverse with (p:=p)...
    destruct InProg. left. rewrite in_map_iff. eexists. split.
    2:{ rewrite in_flat_map. exists (a,a'). split... unfold program_gfun_bods_for_type in H3.
      rewrite filter_In in H3. destruct H3...
    }
    reflexivity.
Qed.

Lemma switch_indices_aux_inverse' : forall p tn a a0 e c d a'
  (InProg : In (a0, e) a' /\ In (a, a') (program_cfun_bods_for_type tn p))
  (RefuncDt : forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn)
  (RefuncDt2 : In tn (skeleton_dts (program_skeleton p))),
  lookup_dtor (refunctionalize_to_skeleton p tn) a = Some d ->
  lookup_ctor_sig (program_skeleton p) a0 = Some c ->
  tn = fst (unscope a0) ->
  DefuncIII.switch_indices_aux (refunctionalize_to_skeleton p tn) a0 (length (snd (fst d))) tn
  (switch_indices_aux (program_skeleton p) a (length (snd c)) tn e) = e.
Proof with eauto.
intros. unfold switch_indices_aux. unfold DefuncIII.switch_indices_aux.
unfold switch_indices.
remember (lookup_gfun_sig_scoped (refunctionalize_to_skeleton p tn) a0) as gsig.
destruct gsig.
- cbn. unfold switch_indices_cfun. remember (lookup_cfun_sig_scoped (program_skeleton p) a) as csig.
  destruct csig.
  + cbn. replace (length (snd (fst d))) with (length (snd (fst c0))).
    2:{ destruct InProg. apply (in_map fst) in H3. cbn in H3. eapply dtor_csig_length'... }
    replace (length (snd g)) with (length (snd c)).
    2:{ eapply ctor_gsig_length'... unfold lookup_ctor_sig in H0. apply find_some in H0.
      destruct H0. rewrite eq_ScopedName_eq in H2. subst...
    }
    rewrite switch_indices_helper_refunc_exchange.
    rewrite switch_indices_helper_inverse.
    2:{ intros. eapply E_Var_lt'... }
    apply redefunc_exp_inverse with (p:=p)...
    clear - InProg. left. rewrite in_map_iff. exists (a0,e). split... rewrite in_flat_map.
    exists (a,a'). destruct InProg. split...
    unfold program_cfun_bods_for_type in H0. rewrite filter_In in H0. destruct H0...
  + exfalso. clear - H Heqcsig InProg. destruct InProg. symmetry in Heqcsig.
    apply (in_map fst) in H1. cbn in H1. rewrite no_cfun_no_dtor in H... discriminate.
- cbn. unfold switch_indices_cfun. remember (lookup_cfun_sig_scoped (program_skeleton p) a) as csig.
  destruct csig.
  + exfalso. clear - H0 Heqgsig H1. rename Heqgsig into H. unfold lookup_gfun_sig_scoped in H.
    destruct a0.
    * unfold lookup_gfun_sig_l in H. unfold lookup_gfun_sig_x in H. cbn in H.
      unfold DefuncI.new_gfunsigs_l in H. symmetry in H.
      apply find_none with (x:=(unscope (fst c), snd c)) in H.
      2:{ apply in_or_app. left. rewrite in_map_iff. unfold gfunsigs_mapfun. exists c.
        split. { destruct c... }
        unfold lookup_ctor_sig in H0. apply find_some in H0. rewrite filter_In. destruct H0.
        split... rewrite eq_ScopedName_eq in H2. unfold gfunsigs_filterfun_l. destruct c.
        cbn in H2. subst. cbn. apply eq_TypeName_refl.
      }
      cbn in H. unfold lookup_ctor_sig in H0. apply find_some in H0. destruct H0.
      rewrite eq_ScopedName_eq in H2. rewrite <- H2 in H. cbn in H. rewrite eq_QName_refl in H.
      discriminate.
    * unfold lookup_gfun_sig_g in H. unfold lookup_gfun_sig_x in H. cbn in H.
      unfold DefuncI.new_gfunsigs_l in H. symmetry in H.
      apply find_none with (x:=(unscope (fst c), snd c)) in H.
      2:{ apply in_or_app. left. rewrite in_map_iff. unfold gfunsigs_mapfun. exists c.
        split. { destruct c... }
        unfold lookup_ctor_sig in H0. apply find_some in H0. rewrite filter_In. destruct H0.
        split... rewrite eq_ScopedName_eq in H2. unfold gfunsigs_filterfun_l. destruct c.
        cbn in H2. subst. cbn. apply eq_TypeName_refl.
      }
      cbn in H. unfold lookup_ctor_sig in H0. apply find_some in H0. destruct H0.
      rewrite eq_ScopedName_eq in H2. rewrite <- H2 in H. cbn in H. rewrite eq_QName_refl in H.
      discriminate.
  + cbn. apply redefunc_exp_inverse with (p:=p)...
    destruct InProg. left. rewrite in_map_iff. eexists. split.
    2:{ rewrite in_flat_map. exists (a,a'). split... unfold program_cfun_bods_for_type in H3.
      rewrite filter_In in H3. destruct H3... }
    reflexivity.
Qed.

Lemma in_gbods_tn : forall p tn a0 e a' a,
  In (a0, e) a' ->
  In (a, a') (program_gfun_bods_for_type tn p) ->
  tn = fst (unscope a0).
Proof with eauto.
intros. unfold program_gfun_bods_for_type in H0. rewrite filter_In in H0. destruct H0.
rewrite eq_TypeName_eq in H1. subst. cbn. apply in_app_or in H0. destruct H0.
- pose proof (program_gfun_bods_typecheck_g p). unfold gfun_bods_g_typecheck in H1.
  rewrite in_map_iff in H0. do 2 destruct H0. rewrite Forall_forall in H1.
  apply H1 in H2. destruct H2 as [qn [args [LookupSig Typ]]]. inversion Typ; subst.
  rewrite Forall_forall in H10. inversion H0; subst. cbn.
  assert (Len : length (snd x) = length dtorlist).
  { pose proof (listTypeDeriv'_lemma _ _ _ _ H11). rewrite Nat.eqb_eq in H2.
    repeat rewrite map_length in H2...
  }
  unfold lookup_dtors in H9.
  case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
    unfold gfun_bod in *; rewrite H2 in H9; try discriminate.
  inversion H9; subst. pose proof (combine_in H Len) as Comb. destruct Comb as [yComb Comb].
  apply in_combine_switch in Comb... pose proof Comb as Comb'.
  apply H10 in Comb. destruct yComb. destruct p0. subst.
  apply in_combine_r in Comb'. rewrite filter_In in Comb'. destruct Comb' as [_ Done].
  rewrite eq_TypeName_eq in Done...
- pose proof (program_gfun_bods_typecheck_l p). unfold gfun_bods_l_typecheck in H1.
  rewrite in_map_iff in H0. do 2 destruct H0. rewrite Forall_forall in H1.
  apply H1 in H2. destruct H2 as [qn [args [LookupSig Typ]]]. inversion Typ; subst.
  rewrite Forall_forall in H10. inversion H0; subst. cbn.
  assert (Len : length (snd x) = length dtorlist).
  { pose proof (listTypeDeriv'_lemma _ _ _ _ H11). rewrite Nat.eqb_eq in H2.
    repeat rewrite map_length in H2...
  }
  unfold lookup_dtors in H9.
  case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
    unfold gfun_bod in *; rewrite H2 in H9; try discriminate.
  inversion H9; subst. pose proof (combine_in H Len) as Comb. destruct Comb as [yComb Comb].
  apply in_combine_switch in Comb... pose proof Comb as Comb'.
  apply H10 in Comb. destruct yComb. destruct p0. subst.
  apply in_combine_r in Comb'. rewrite filter_In in Comb'. destruct Comb' as [_ Done].
  rewrite eq_TypeName_eq in Done...
Qed.

Lemma in_cbods_tn : forall p tn a0 e a' a,
  In (a0, e) a' ->
  In (a, a') (program_cfun_bods_for_type tn p) ->
  tn = fst (unscope a0).
Proof with eauto.
intros. unfold program_cfun_bods_for_type in H0. rewrite filter_In in H0. destruct H0.
rewrite eq_TypeName_eq in H1. subst. cbn. apply in_app_or in H0. destruct H0.
- pose proof (program_cfun_bods_typecheck_g p). unfold cfun_bods_g_typecheck in H1.
  rewrite in_map_iff in H0. do 2 destruct H0. rewrite Forall_forall in H1.
  apply H1 in H2. destruct H2 as [qn [args [t [LookupSig Typ]]]]. inversion Typ; subst.
  rewrite Forall_forall in H14. inversion H0; subst. cbn.
  assert (Len : length (snd x) = length ctorlist).
  { pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H15). rewrite Nat.eqb_eq in H2.
    repeat rewrite map_length in H2...
  }
  unfold lookup_ctors in H13.
  case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
    unfold cfun_bod in *; rewrite H2 in H13; try discriminate.
  inversion H13; subst. pose proof (combine_in H Len) as Comb. destruct Comb as [yComb Comb].
  apply in_combine_switch in Comb... pose proof Comb as Comb'.
  apply H14 in Comb. destruct yComb. subst.
  apply in_combine_r in Comb'. rewrite filter_In in Comb'. destruct Comb' as [_ Done].
  rewrite eq_TypeName_eq in Done...
- pose proof (program_cfun_bods_typecheck_l p). unfold cfun_bods_l_typecheck in H1.
  rewrite in_map_iff in H0. do 2 destruct H0. rewrite Forall_forall in H1.
  apply H1 in H2. destruct H2 as [qn [args [t [LookupSig Typ]]]]. inversion Typ; subst.
  rewrite Forall_forall in H14. inversion H0; subst. cbn.
  assert (Len : length (snd x) = length ctorlist).
  { pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H15). rewrite Nat.eqb_eq in H2.
    repeat rewrite map_length in H2...
  }
  unfold lookup_ctors in H13.
  case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
    unfold cfun_bod in *; rewrite H2 in H13; try discriminate.
  inversion H13; subst. pose proof (combine_in H Len) as Comb. destruct Comb as [yComb Comb].
  apply in_combine_switch in Comb... pose proof Comb as Comb'.
  apply H14 in Comb. destruct yComb. subst.
  apply in_combine_r in Comb'. rewrite filter_In in Comb'. destruct Comb' as [_ Done].
  rewrite eq_TypeName_eq in Done...
Qed.

Lemma derefunc_helper_inverse : forall p tn a a0 e a'
  (DefuncCdt : forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn)
  (DefuncCdt2 : In tn (skeleton_cdts (program_skeleton p))),
  In (a0,e) a' ->
  In (a,a') (program_gfun_bods_for_type tn p) ->
  refunc_term_helper (defunctionalize_to_skeleton p tn) tn a0
    a (defunc_term_helper (program_skeleton p) tn a0 a e) = e.
Proof with eauto.
intros. unfold refunc_term_helper. unfold defunc_term_helper.
case_eq (lookup_ctor_sig (defunctionalize_to_skeleton p tn) a); intros.
- cbn. case_eq (lookup_dtor (program_skeleton p) a0); intros.
  + cbn. apply switch_indices_aux_inverse with (a':=a')...
    clear - H H0. eapply in_gbods_tn...
  + exfalso. clear - H H0 H2. unfold lookup_dtor in H2. pose proof (find_none _ _ H2). cbn in H1. clear H2.
    unfold program_gfun_bods_for_type in H0. rewrite filter_app in H0. apply in_app_or in H0. destruct H0.
    * pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
      rewrite Forall_forall in TypG. rewrite filter_In in H0. destruct H0. rewrite in_map_iff in H0. do 2 destruct H0.
      apply TypG in H3. destruct H3 as  [qn [args [SigLookup Typ]]]. inversion Typ; subst.
      unfold lookup_dtors in H10. unfold QName in *. unfold gfun_bod in *.
      case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
        rewrite H3 in H10; try discriminate.
      inversion H10; subst. apply listTypeDeriv'_lemma in H12. repeat rewrite map_length in H12.
      rewrite Nat.eqb_eq in H12. inversion H0; subst.
      rewrite Forall_forall in H11. symmetry in H12. pose proof (combine_in H H12).
      destruct H4. apply in_combine_switch in H4... pose proof H4 as H4'. apply H11 in H4'.
      destruct x0. destruct p0. subst. apply in_combine_r in H4. rewrite filter_In in H4.
      destruct H4. apply H1 in H4. cbn in H4. rewrite eq_ScopedName_refl in H4. discriminate.
    * pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
      rewrite Forall_forall in TypL. rewrite filter_In in H0. destruct H0. rewrite in_map_iff in H0. do 2 destruct H0.
      apply TypL in H3. destruct H3 as  [qn [args [SigLookup Typ]]]. inversion Typ; subst.
      unfold lookup_dtors in H10. unfold QName in *. unfold gfun_bod in *.
      case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
        rewrite H3 in H10; try discriminate.
      inversion H10; subst. apply listTypeDeriv'_lemma in H12. repeat rewrite map_length in H12.
      rewrite Nat.eqb_eq in H12. inversion H0; subst.
      rewrite Forall_forall in H11. symmetry in H12. pose proof (combine_in H H12).
      destruct H4. apply in_combine_switch in H4... pose proof H4 as H4'. apply H11 in H4'.
      destruct x0. destruct p0. subst. apply in_combine_r in H4. rewrite filter_In in H4.
      destruct H4. apply H1 in H4. cbn in H4. rewrite eq_ScopedName_refl in H4. discriminate.
- cbn. case_eq (lookup_dtor (program_skeleton p) a0); intros...
  exfalso. clear - H H0 H1. unfold lookup_ctor_sig in H1.
  assert (find (fun x => eq_ScopedName a x) (map fst (skeleton_ctors (defunctionalize_to_skeleton p tn))) = None).
  { clear - H1. generalize dependent (skeleton_ctors (defunctionalize_to_skeleton p tn)).
    induction c; intros... cbn. cbn in H1. destruct (eq_ScopedName a (fst a0)); try discriminate...
  }
  pose proof (find_none _ _ H2). cbn in H3. clear H1 H2.
  unfold program_gfun_bods_for_type in H0. unfold computeNewDatatype in H3.
  repeat rewrite map_app in H3. repeat rewrite map_map in H3. cbn in H3.
  apply (in_map fst) in H0. cbn in H0. rewrite <- map_map in H3. rewrite <- map_map with (g:=local) in H3.
  erewrite filter_ext in H3.
  { rewrite filter_map in H3. erewrite filter_ext with (f:=fun x0 => eq_TypeName (fst (fst x0)) tn) in H3.
    { rewrite filter_map with (f:=fst) in H3. erewrite filter_ext in H0.
      { rewrite filter_map in H0. rewrite map_app in H0. repeat rewrite map_map in H0. cbn in H0.
        rewrite <- map_map in H0. rewrite <- (program_has_all_gfun_bods_g p) in H0.
        rewrite <- map_map with (f:=fst) in H0. rewrite <- (program_has_all_gfun_bods_l p) in H0.
        rewrite filter_app in H0. rewrite <- filter_map in H0. rewrite <- filter_map with (f:=local) in H0.
        assert (eq_ScopedName a a = false).
        { apply H3. apply in_or_app. left. apply H0. }
        rewrite eq_ScopedName_refl in H1. discriminate.
      }
      intros. cbn. instantiate (1:=fun x => eq_TypeName (fst (unscope x)) tn)...
    }
    intros...
  }
  intros...
Qed.

Lemma redefunc_helper_inverse : forall p tn a a0 e a'
  (RefuncDt : forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn)
  (RefuncDt2 : In tn (skeleton_dts (program_skeleton p))),
  In (a0,e) a' ->
  In (a,a') (program_cfun_bods_for_type tn p) ->
  defunc_term_helper (refunctionalize_to_skeleton p tn) tn a
    a0 (refunc_term_helper (program_skeleton p) tn a a0 e) = e.
Proof with eauto.
intros. unfold refunc_term_helper. unfold defunc_term_helper.
case_eq (lookup_dtor (refunctionalize_to_skeleton p tn) a); intros.
- cbn. case_eq (lookup_ctor_sig (program_skeleton p) a0); intros.
  + cbn. apply switch_indices_aux_inverse' with (a':=a')...
    clear - H H0. eapply in_cbods_tn...
  + exfalso. clear - H H0 H2. unfold lookup_ctor_sig in H2. pose proof (find_none _ _ H2). cbn in H1. clear H2.
    unfold program_cfun_bods_for_type in H0. rewrite filter_app in H0. apply in_app_or in H0. destruct H0.
    * pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
      rewrite Forall_forall in TypG. rewrite filter_In in H0. destruct H0. rewrite in_map_iff in H0. do 2 destruct H0.
      apply TypG in H3. destruct H3 as  [qn [args [t [SigLookup Typ]]]]. inversion Typ; subst.
      unfold lookup_ctors in H14. unfold QName in *. unfold cfun_bod in *.
      case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
        rewrite H3 in H14; try discriminate.
      inversion H14; subst. apply listTypeDeriv'_lemma_ctx in H16. repeat rewrite map_length in H16.
      rewrite Nat.eqb_eq in H16. inversion H0; subst.
      rewrite Forall_forall in H15. symmetry in H16. pose proof (combine_in H H16).
      destruct H4. apply in_combine_switch in H4... pose proof H4 as H4'. apply H15 in H4'.
      destruct x0. subst. apply in_combine_r in H4. rewrite filter_In in H4.
      destruct H4. apply H1 in H4. cbn in H4. rewrite eq_ScopedName_refl in H4. discriminate.
    * pose proof (program_cfun_bods_typecheck_l p) as TypL. unfold cfun_bods_l_typecheck in TypL.
      rewrite Forall_forall in TypL. rewrite filter_In in H0. destruct H0. rewrite in_map_iff in H0. do 2 destruct H0.
      apply TypL in H3. destruct H3 as  [qn [args [t [SigLookup Typ]]]]. inversion Typ; subst.
      unfold lookup_ctors in H14. unfold QName in *. unfold cfun_bod in *.
      case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
        rewrite H3 in H14; try discriminate.
      inversion H14; subst. apply listTypeDeriv'_lemma_ctx in H16. repeat rewrite map_length in H16.
      rewrite Nat.eqb_eq in H16. inversion H0; subst.
      rewrite Forall_forall in H15. symmetry in H16. pose proof (combine_in H H16).
      destruct H4. apply in_combine_switch in H4... pose proof H4 as H4'. apply H15 in H4'.
      destruct x0. subst. apply in_combine_r in H4. rewrite filter_In in H4.
      destruct H4. apply H1 in H4. cbn in H4. rewrite eq_ScopedName_refl in H4. discriminate.
- cbn. case_eq (lookup_ctor_sig (program_skeleton p) a0); intros...
  exfalso. clear - H H0 H1. unfold lookup_dtor in H1.
  assert (find (fun x => eq_ScopedName a x) (map fst (map fst (skeleton_dtors (refunctionalize_to_skeleton p tn)))) = None).
  { clear - H1. generalize dependent (skeleton_dtors (refunctionalize_to_skeleton p tn)).
    induction d; intros... cbn. cbn in H1. destruct (eq_ScopedName a (fst (fst a0))); try discriminate...
  }
  pose proof (find_none _ _ H2). cbn in H3. clear H1 H2.
  unfold program_cfun_bods_for_type in H0. unfold computeNewCoDatatype in H3.
  repeat rewrite map_app in H3. repeat rewrite map_map in H3. cbn in H3.
  apply (in_map fst) in H0. cbn in H0. rewrite <- map_map in H3. rewrite <- map_map with (g:=local) in H3.
  erewrite filter_ext in H3.
  { rewrite filter_map in H3. erewrite filter_ext with (f:=fun x0 => eq_TypeName (fst (fst (fst x0))) tn) in H3.
    { rewrite filter_map with (f:=fun x => fst (fst x)) in H3. erewrite filter_ext in H0.
      { rewrite filter_map in H0. rewrite map_app in H0. repeat rewrite map_map in H0. cbn in H0.
        rewrite <- map_map in H0. rewrite <- (program_has_all_cfun_bods_g p) in H0.
        do 2 rewrite <- map_map with (f:=fst) in H0. rewrite <- (program_has_all_cfun_bods_l p) in H0.
        rewrite filter_app in H0. rewrite <- filter_map in H0. rewrite <- filter_map with (f:=local) in H0.
        assert (eq_ScopedName a a = false).
        { apply H3. apply in_or_app. left. rewrite map_map in H0. apply H0. }
        rewrite eq_ScopedName_refl in H1. discriminate.
      }
      intros. cbn. instantiate (1:=fun x => eq_TypeName (fst (unscope x)) tn)...
    }
    intros...
  }
  intros...
Qed.


Fact map_skipn : forall {A B} (l : list A) (f : A -> B) n, map f (skipn n l) = skipn n (map f l).
Proof with auto.
intros. generalize n. induction l; intros; [destruct n0|]...
simpl. destruct n0... simpl. apply IHl.
Qed.

Fact length_firstn : forall {A} (l : list A) n, length (firstn n l) <= length l.
Proof with auto; try omega. intros. generalize l. induction n; intros; [simpl |]...
destruct l0... simpl. specialize IHn with (l:=l0)...
Qed.

Fact rev_map_rev : forall {A B} (l : list A) (f : A -> B), rev (map f (rev l)) = map f l.
Proof with auto. intros. induction l... simpl. rewrite map_app. rewrite rev_app_distr.
rewrite IHl...
Qed.

Fact firstn_In : forall {A} (l : list A) n x, In x (firstn (S n) l) -> In x l.
Proof with eauto. intros. generalize dependent n. induction l; intros...
simpl in H. destruct H; [left | right]... destruct n; try inversion H...
Qed.

Lemma nth_error_In_firstn {A} l n (x : A) : nth_error l n = Some x -> In x (firstn (S n) l).
Proof with eauto.
intros. pose proof H as H'.
rewrite <- firstn_skipn with (l:=l)(n:=S n) in H. rewrite nth_error_app1 in H; try eapply nth_error_In...
clear H. generalize dependent l. induction n; intros.
- destruct l; simpl in H'; try discriminate. simpl...
- destruct l; try discriminate. remember (S n) as m. simpl. subst. simpl in H'. apply IHn in H'. omega.
Qed.

Lemma nth_error_In_skipn {A} l n m (x : A) : m <= n -> nth_error l n = Some x -> In x (skipn m l).
Proof with eauto.
intros. pose proof H0 as H0'.
rewrite <- firstn_skipn with (l:=l)(n:=m) in H0. rewrite nth_error_app2 in H0; try eapply nth_error_In...
pose proof (firstn_le_length m l). omega.
Qed.

Lemma map_firstn : forall {A B} (l : list A) (f : A -> B) n, map f (firstn n l) = firstn n (map f l).
Proof with eauto.
intros. generalize dependent n. induction l; intros.
- rewrite firstn_nil. cbn. rewrite firstn_nil...
- cbn. destruct n... cbn. f_equal...
Qed.



(* These kinds of hypotheses are needed because there are separate lists for global and local g/cfuns,
   but not for xtors, thus the additional requirement of global before local is needed to keep the order
   the order the same when going from xtors to g/cfuns and back.
 *)
Definition global_before_local_dtors (dtorSigs : list (ScopedName * list TypeName * TypeName)) : Prop :=
  forall tn,
  filter (cfunsigs_filterfun_g tn) dtorSigs ++ filter (cfunsigs_filterfun_l tn) dtorSigs =
  filter
    (fun x : ScopedName * list TypeName * TypeName =>
     eq_TypeName (fst (unscope (fst (fst x)))) tn)
    dtorSigs.

Definition global_before_local_ctors (ctorSigs : list (ScopedName * list TypeName)) : Prop :=
  forall tn,
  filter (gfunsigs_filterfun_g tn) ctorSigs ++ filter (gfunsigs_filterfun_l tn) ctorSigs =
  filter
    (fun x : ScopedName * list TypeName =>
     eq_TypeName (fst (unscope (fst x))) tn)
    ctorSigs.

Lemma transpose_gfbods : forall p tn l l' (f : skeleton -> TypeName -> ScopedName -> ScopedName -> expr -> expr) d n
  (GL : global_before_local_dtors (skeleton_dtors (program_skeleton p))),
  l = map (fun x => map (fun y => f (program_skeleton p) tn (fst y) (fst x) (snd y)) (snd x)) l' ->
  l' = filter (fun x : ScopedName * gfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
              (DefuncIII.globalize_aux (program_gfun_bods_g p) ++
               DefuncIII.localize_aux (program_gfun_bods_l p)) ->
  n = length (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p)) ++
    filter (cfunsigs_filterfun_l tn) (skeleton_dtors (program_skeleton p))) ->
  transpose l n =
    map (map (fun x => snd (snd x)))
      (map
        (fun x0 => map (map_alternative_for_filter (unscope (fst (fst x0))) d)
                       (map (fun x => (unscope (fst x), snd x))
                         (map (fun x => (fst x, map (fun y => (fst y, f (program_skeleton p) tn (fst y) (fst x) (snd y))) (snd x))) l')))
        (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p)))) ++
    map (map (fun x => snd (snd x)))
      (map
        (fun x0 => map (map_alternative_for_filter_l (unscope (fst (fst x0))) d)
                       (map (fun x => (unscope (fst x), snd x))
                         (map (fun x => (fst x, map (fun y => (fst y, f (program_skeleton p) tn (fst y) (fst x) (snd y))) (snd x))) l')))
        (filter (cfunsigs_filterfun_l tn) (skeleton_dtors (program_skeleton p)))).
Proof with eauto.
intros.
generalize H.
replace l' with (rev (firstn (length l) (rev l'))).
2:{ rewrite H. rewrite map_length. clear. rewrite <- rev_length. rewrite firstn_all. rewrite rev_involutive... }
assert (length l <= length l') as Len.
{ subst. rewrite map_length... }
clear H.
induction l as [| l l0]; intros.
- simpl. rewrite H1. clear. do 2 rewrite map_map. simpl. rewrite <- map_app.
  match goal with [|- _ = map _ ?l] => generalize l end. intros. induction l...
  simpl. f_equal...
- simpl. destruct l.
  + subst l'. clear - H.
    match goal with [_ : _ = map _ (rev (firstn _ (rev ?x))) |- _] =>
      assert (In [] (map (map snd) (map snd x)))
    end.
    { pose proof (in_eq [] l0). rewrite H in H0. clear - H0. rewrite in_map_iff in H0. destruct H0. destruct H.
      apply in_rev in H0. apply firstn_In in H0. apply in_rev in H0.
      case_eq (snd x); intros; rewrite H1 in H; try discriminate. rewrite in_map_iff. exists (snd x). rewrite H1.
      simpl. split... rewrite in_map_iff. exists x. split...
    }
    clear - H0. rewrite map_map in H0. rewrite in_map_iff in H0. destruct H0. destruct H.
    rewrite filter_In in H0. destruct H0. apply in_app_or in H0. destruct H0.
    * pose proof (program_gfun_bods_typecheck_g p) as TypG.
      unfold gfun_bods_g_typecheck in TypG. rewrite Forall_forall in TypG.
      unfold DefuncIII.globalize_aux in H0. rewrite in_map_iff in H0. do 2 destruct H0.
      apply TypG in H2. clear TypG. destruct H2 as [qn [args [SigLookup Typ]]].
      inversion Typ; subst. unfold lookup_dtors in H9. unfold QName in *. unfold gfun_bod in *.
      case_eq (filter (eq_TypeName (fst (fst x0))) (skeleton_cdts (program_skeleton p))); intros;
        rewrite H0 in H9; try discriminate.
      inversion H9; subst. clear H9. simpl in H. rewrite H in H11. apply listTypeDeriv'_lemma in H11.
      rewrite Nat.eqb_eq in H11. simpl in H1. rewrite eq_TypeName_eq in H1. subst tn.
      clear - H11. unfold cfunsigs_filterfun_g. unfold cfunsigs_filterfun_l.
      erewrite filter_ext with (l:=skeleton_dtors (program_skeleton p))
        (g:=fun x => match fst (fst x) with global _ => true | local _ => false end
              && eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0))).
      2:{ intros. destruct a. destruct p0. destruct s... simpl. apply eq_TypeName_symm. }
      rewrite <- filter_compose.
      case_eq (filter (fun x : dtor => eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0)))
           (skeleton_dtors (program_skeleton p))); intros.
      2:{ erewrite filter_ext in H; [rewrite H in H11; discriminate |]. intros. destruct a. destruct p0... }
      simpl.
      erewrite filter_ext with (l:=skeleton_dtors (program_skeleton p))
        (g:=fun x => match fst (fst x) with global _ => false | local _ => true end
              && eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0))).
      2:{ intros. destruct a. destruct p0. destruct s... simpl. apply eq_TypeName_symm. }
      rewrite <- filter_compose. rewrite H...
    * pose proof (program_gfun_bods_typecheck_l p) as TypL.
      unfold gfun_bods_l_typecheck in TypL. rewrite Forall_forall in TypL.
      unfold DefuncIII.localize_aux in H0. rewrite in_map_iff in H0. do 2 destruct H0.
      apply TypL in H2. clear TypL. destruct H2 as [qn [args [SigLookup Typ]]].
      inversion Typ; subst. unfold lookup_dtors in H9. unfold QName in *. unfold gfun_bod in *.
      case_eq (filter (eq_TypeName (fst (fst x0))) (skeleton_cdts (program_skeleton p))); intros;
        rewrite H0 in H9; try discriminate.
      inversion H9; subst. clear H9. simpl in H. rewrite H in H11. apply listTypeDeriv'_lemma in H11.
      rewrite Nat.eqb_eq in H11. simpl in H1. rewrite eq_TypeName_eq in H1. subst tn.
      clear - H11. unfold cfunsigs_filterfun_g. unfold cfunsigs_filterfun_l.
      erewrite filter_ext with (l:=skeleton_dtors (program_skeleton p))
        (g:=fun x => match fst (fst x) with global _ => true | local _ => false end
              && eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0))).
      2:{ intros. destruct a. destruct p0. destruct s... simpl. apply eq_TypeName_symm. }
      rewrite <- filter_compose.
      case_eq (filter (fun x : dtor => eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0)))
           (skeleton_dtors (program_skeleton p))); intros.
      2:{ erewrite filter_ext in H; [rewrite H in H11; discriminate |]. intros. destruct a. destruct p0... }
      simpl.
      erewrite filter_ext with (l:=skeleton_dtors (program_skeleton p))
        (g:=fun x => match fst (fst x) with global _ => false | local _ => true end
              && eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0))).
      2:{ intros. destruct a. destruct p0. destruct s... simpl. apply eq_TypeName_symm. }
      rewrite <- filter_compose. rewrite H...
  + rewrite IHl0.
    2:{ simpl in Len. omega. }
    2:{ clear - H Len. match goal with [|- _ = map ?m _] => generalize dependent m end.
     clear - Len. intros. cbn - [firstn] in H. apply (f_equal (@rev _)) in H. cbn - [firstn] in H.
     case_eq (rev l'); intros; rewrite H0 in H.
     - rewrite firstn_nil in H. simpl in H. destruct (rev l0); discriminate.
     - cbn - [rev] in H. rewrite rev_map_rev in H. case_eq (length l0); intros.
       + simpl. destruct l0; try discriminate...
       + simpl. rewrite map_app. simpl in *. replace [e :: l] with (rev [e :: l]) in H...
         rewrite <- rev_app_distr in H. apply (f_equal (@rev _)) in H. rewrite rev_involutive in H.
         simpl in H. assert ((e :: l) :: l0 = (e :: l) :: map l1 (rev (firstn n l2)) ++ [l1 p] ->
          l0 = map l1 (rev (firstn n l2)) ++ [l1 p]) as Aux.
         { intros. inversion H2... }
         apply Aux. clear Aux. rewrite H. rewrite H1 in *.
         destruct l0; try discriminate.
         destruct l2. { simpl in *. discriminate. }
         assert (Aux: hd_error (rev (map l1 (firstn (S n) (p0::l2)))) = Some (e::l)).
         { match goal with [|- hd_error ?lhs = _] => case_eq lhs; intros end.
           - rewrite H2 in H. discriminate.
           - rewrite H2 in H. inversion H; subst...
         }
         assert (Len': length l' <= length l2 + 2).
         { rewrite <- rev_length. rewrite H0. simpl. omega. }
         clear - Aux Len Len'. rewrite app_comm_cons. f_equal. simpl in *.
         case_eq (rev (map l1 (firstn n l2)) ++ [l1 p0]); intros.
         * destruct (rev (map l1 (firstn n l2))); discriminate.
         * f_equal.
           -- rewrite H in Aux. unfold hd_error in Aux. inversion Aux; subst...
           -- apply (f_equal (@tl _)) in H. simpl in H. subst. clear - Len Len'.
              assert (n <= length l2).
              { intros. omega. }
              clear - H. generalize dependent n. generalize p0.
              induction l2; intros.
              ++ destruct n... simpl in H. omega.
              ++ destruct n... simpl. destruct n... unfold tl.
                 case_eq (rev (map l1 (firstn (S n) l2))); intros.
                 ** destruct l2.
                    --- simpl in H. omega.
                    --- simpl in H0. destruct (rev (map l1 (firstn n l2))); discriminate.
                 ** simpl. replace [a] with (rev [a])... rewrite <- rev_app_distr.
                    replace ([a] ++ firstn n l2) with (firstn (S n) (a::l2))...
                    rewrite map_app. simpl in H. rewrite <- IHl2; try omega.
                    cbn - [firstn]. f_equal.
                    assert (tl (rev (map l1 (firstn (S n) l2)) ++ [l1 a]) =
                      tl (rev (map l1 (firstn (S n) l2))) ++ [l1 a]).
                    { destruct l2; simpl in H; try omega. simpl.
                      case_eq (rev (map l1 (firstn n l2))); intros...
                    }
                    rewrite H1. f_equal. rewrite H0...
    }
    repeat rewrite map_with_index_map. repeat rewrite with_index_map_map.
    rewrite map_with_index_app. rewrite with_index'_map_map. rewrite with_index_map_map.
    clear IHl0.
    rewrite <- rev_length with (l:=l') in Len. unfold map_with_index.
    f_equal; apply map_with_index'_ext_in; intros a n0 H2 aEq.
    * case_eq (rev l'); intros; try (rewrite H3 in Len; simpl in Len; omega).
      simpl. case_eq (rev (firstn (length l0) l1) ++ [p0]); intros.
      -- destruct (rev (firstn (length l0) l1)); try discriminate.
      -- simpl. f_equal.
         ++ replace [p0] with (rev [p0]) in H4... rewrite <- rev_app_distr in H4.
            replace ([p0] ++ firstn (length l0) l1) with (firstn (S (length l0)) (p0::l1)) in H4...
            rewrite <- H3 in H4. cbn - [firstn] in H. rewrite H4 in H. simpl in H. inversion H.
            replace (n0+0) with n0...
            match goal with [|- ?lhs = _] => replace lhs with (nth n0 (e::l) e) end...
            rewrite H6.
            assert (Len': n0 < length (snd p1)).
            { pose proof (in_eq p1 l2). rewrite <- H4 in H5. rewrite H0 in H5. clear - H5 aEq.
              apply in_rev in H5. apply firstn_In in H5. apply in_rev in H5.
              assert (
                nth_error (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p))) n0 <> None).
              { rewrite <- aEq. unfold not. intros. discriminate. }
              apply nth_error_Some in H.
              assert (length (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p))) <= length (snd p1)).
              2:{ omega... }
              clear H aEq. rewrite filter_In in H5. destruct H5. apply in_app_or in H. destruct H.
              - unfold DefuncIII.globalize_aux in H. rewrite in_map_iff in H. do 2 destruct H. subst. simpl.
                pose proof (program_gfun_bods_typecheck_g p). unfold gfun_bods_g_typecheck in H.
                rewrite Forall_forall in H. apply H in H1. clear H. destruct H1 as [qn [args [LookupSig Typ]]].
                inversion Typ; subst. apply listTypeDeriv'_lemma in H9. rewrite Nat.eqb_eq in H9.
                repeat rewrite map_length in H9. unfold gfun_bod. rewrite <- H9.
                simpl in H0. rewrite eq_TypeName_eq in H0. subst. clear - H7.
                unfold lookup_dtors in H7. unfold cfunsigs_filterfun_g. unfold QName in *. unfold gfun_bod in *.
                case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
                  try (rewrite H in H7; discriminate).
                rewrite H in H7. inversion H7; subst. clear. generalize (skeleton_dtors (program_skeleton p)).
                induction d... simpl. destruct a. destruct p0. destruct s.
                + case_eq (eq_TypeName (fst (unscope (local q))) (fst (fst x))); intros; simpl; omega.
                + rewrite eq_TypeName_symm. simpl. case_eq (eq_TypeName (fst q) (fst (fst x))); intros; simpl; omega.
              - unfold DefuncIII.localize_aux in H. rewrite in_map_iff in H. do 2 destruct H. subst. simpl.
                pose proof (program_gfun_bods_typecheck_l p). unfold gfun_bods_l_typecheck in H.
                rewrite Forall_forall in H. apply H in H1. clear H. destruct H1 as [qn [args [LookupSig Typ]]].
                inversion Typ; subst. apply listTypeDeriv'_lemma in H9. rewrite Nat.eqb_eq in H9.
                repeat rewrite map_length in H9. unfold gfun_bod. rewrite <- H9.
                simpl in H0. rewrite eq_TypeName_eq in H0. subst. clear - H7.
                unfold lookup_dtors in H7. unfold cfunsigs_filterfun_g. unfold QName in *. unfold gfun_bod in *.
                case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
                  try (rewrite H in H7; discriminate).
                rewrite H in H7. inversion H7; subst. clear. generalize (skeleton_dtors (program_skeleton p)).
                induction d... simpl. destruct a. destruct p0. destruct s.
                + case_eq (eq_TypeName (fst (unscope (local q))) (fst (fst x))); intros; simpl; omega.
                + rewrite eq_TypeName_symm. simpl. case_eq (eq_TypeName (fst q) (fst (fst x))); intros; simpl; omega.
            }
            match goal with [|- _ = snd (_ _ (find ?rhsf (map ?rhsf' _)))] =>
              assert (find rhsf (map rhsf' (snd p1)) = nth_error (map rhsf' (snd p1)) n0)
            end.
            { rewrite filter_In in H2. destruct H2 as [_ H2]. unfold cfunsigs_filterfun_g in H2.
              assert (is_global (fst (fst a))). { destruct a. destruct p2. destruct s; try discriminate... constructor. }
              rename H2 into aGlob. clear - H0 H4 aEq aGlob GL. pose proof aEq as n0Some.
              rewrite <- nth_error_app1 with (l':=(filter (cfunsigs_filterfun_l tn)
                (skeleton_dtors (program_skeleton p)))) in aEq.
              2:{ rewrite <- nth_error_Some. rewrite <- aEq. unfold not. intros. discriminate. }
              clear n0Some. unfold global_before_local_dtors in GL.
              assert (filter (cfunsigs_filterfun_g tn)
                (skeleton_dtors (program_skeleton p)) ++
                filter (cfunsigs_filterfun_l tn)
                  (skeleton_dtors (program_skeleton p)) =
                filter (fun x => eq_TypeName (fst (unscope (fst (fst x)))) tn)
                  (skeleton_dtors (program_skeleton p))).
              { apply GL. }
              rewrite H in aEq. clear - aEq aGlob H0 H4.
              pose proof (in_eq p1 l2). rewrite <- H4 in H. rewrite H0 in H.
              apply in_rev in H. apply in_firstn in H. apply in_rev in H.
              rewrite filter_In in H. destruct H. apply in_app_or in H.
              pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)) as Uniq. destruct H.
              - pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
                rewrite Forall_forall in TypG. unfold DefuncIII.globalize_aux in H.
                rewrite in_map_iff in H. do 2 destruct H. apply TypG in H2.
                destruct H2 as [qn [args [LookupSig Typ]]]. inversion Typ; subst.
                simpl. unfold lookup_dtors in H10. unfold gfun_bod in *. case_eq (filter (eq_TypeName (fst (fst x)))
                  (skeleton_cdts (program_skeleton p))); intros; rewrite H in H10; try discriminate.
                inversion H10; subst. apply listTypeDeriv'_lemma in H12. rename H12 into Len.
                simpl in H1. rename H1 into tnEq.
                clear - aEq aGlob H11 Uniq Len tnEq.
                match goal with [|- ?lhs = _] => case_eq lhs; intros end.
                + apply find_some in H. unfold cdts_dtor_names_unique in Uniq.
                  assert (exists n0', nth_error
                    (map (fun y : ScopedName * expr =>
                      (fst y, f (program_skeleton p) tn (fst y) (global (fst x)) (snd y)))
                      (snd x)) n0' = Some p0).
                  { destruct H. apply In_nth_error... }
                  destruct H0. rewrite <- H0. case_eq (x0 =? n0); intros; try rewrite Nat.eqb_eq in H1...
                  apply Unique.filter_unique with (f:=fun y => eq_TypeName (fst (unscope y)) (*fst (fst x)*) tn) in Uniq.
                  rewrite <- filter_map in Uniq.
                  exfalso. case_eq (x0 <? n0); intros.
                  * rewrite <- firstn_skipn with (n:=S x0)(l:=filter _ (skeleton_dtors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. apply map_nth_error with (f:=fst) in H0.
                    rewrite map_map in H0. simpl in H0.
                    change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr) in H0.
                    match goal with [_ : Forall _ (combine _ ?rhs) |- _] =>
                      replace (map fst (snd x)) with (map fst (map fst rhs)) in H0
                    end.
                    2:{ clear - H11 Len. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [|- _ _ (_ _ ?l) = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct p0. destruct a. destruct p0...
                    }
                    apply nth_error_In_firstn in H0. rewrite map_map in H0. rewrite <- map_firstn in H0.
                    specialize Uniq with (fst p0). set (x0':=S x0) in *.
                    match goal with [_ : ?P -> ~In _ _ |- _] => replace (In _ _) with P in H0 end.
                    2:{ erewrite filter_ext... intros. simpl. destruct a0. destruct p1...
                      clear - H H0 aGlob. destruct a. destruct p1. destruct s0; try discriminate...
                      simpl. rewrite in_map_iff in H0. do 2 destruct H0. destruct H.
                      apply in_firstn in H1. rewrite filter_In in H1. destruct H1.
                      destruct x1. destruct p1. rewrite eq_TypeName_eq in H3. simpl in *. subst.
                      destruct p0. simpl in *. destruct s0; try discriminate.
                      rewrite eq_TypeName_eq in *. subst. rewrite eq_QName_eq in *. subst. simpl in *.
                      rewrite <- H3...
                    }
                    pose proof H0 as H0'. pose proof H as H'.
                    apply Uniq in H0. apply H0. destruct H. clear - aEq aGlob H2 H3 H' H0'. symmetry in aEq.
                    rewrite Nat.ltb_lt in H2. eapply nth_error_In_skipn in aEq...
                    destruct (fst p0); try discriminate... rewrite eq_QName_eq in H3. subst.
                    rewrite in_map_iff. exists a. destruct a. destruct p1. destruct s; try discriminate...
                  * rewrite <- firstn_skipn with (n:=S n0)(l:=filter _ (skeleton_dtors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. symmetry in aEq. apply nth_error_In_firstn in aEq.
                    do 2 apply in_map with (f:=fst) in aEq. rewrite map_map in aEq.
                    apply Uniq in aEq. apply aEq. rewrite Nat.eqb_neq in H1. rewrite Nat.ltb_ge in H2.
                    assert (n0 < x0). { omega. } apply nth_error_In_skipn with (m:=S n0) in H0...
                    apply in_map with (f:=fst) in H0. rewrite map_skipn. rewrite <- map_skipn in H0.
                    rewrite map_map in H0. cbn - [skipn] in H0. rewrite map_skipn in H0.
                    match goal with [|- In _ (_ _ ?m')] => replace m' with (map fst (snd x)) end.
                    2:{ symmetry.
                      clear - H11 Len tnEq. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [_ : length ?l' = _ |- _ _ ?l = _] => replace l' with l in * end.
                      2:{ apply filter_ext. intros. destruct a. destruct p0. simpl.
                        rewrite eq_TypeName_eq in tnEq. subst... }
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l0. induction l; intros.
                      - simpl. destruct l1... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct d. destruct a. destruct p0...
                    }
                    destruct H. destruct p0. simpl in *. destruct s; try discriminate.
                    rewrite eq_QName_eq in H4. subst. destruct a. destruct p0. simpl in *.
                    destruct s; try discriminate...
                + exfalso. symmetry in aEq. apply nth_error_In in aEq. do 2 apply in_map with (f:=fst) in aEq.
                  rewrite map_map in aEq.
                  match goal with [_ : In (fst (fst a)) ?l |- _] => replace l with (map fst (snd x)) in aEq end.
                  2:{ clear - H11 Len tnEq.
                      match goal with [_ : (_ (_ _ ?l) =? _) = _ |- _ = map _ ?l'] =>
                        replace l' with l
                      end.
                      2:{ apply filter_ext. intros. rewrite eq_TypeName_eq in tnEq. subst.
                        destruct a. destruct p0... }
                      match goal with [|- _ = _ _ ?l] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                    - simpl. destruct l0... discriminate.
                    - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                      destruct p0. destruct a. destruct p0...
                  }
                  rewrite in_map_iff in aEq. destruct aEq.
                  eapply find_none in H.
                  2:{ rewrite in_map_iff. exists x0. destruct H0. rewrite e. split... }
                  destruct a. destruct p0. simpl in *. destruct s; try discriminate. simpl in *.
                  rewrite eq_QName_refl in H. discriminate.
              - pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
                rewrite Forall_forall in TypL. unfold DefuncIII.localize_aux in H.
                rewrite in_map_iff in H. do 2 destruct H. apply TypL in H2.
                destruct H2 as [qn [args [LookupSig Typ]]]. inversion Typ; subst.
                simpl. unfold lookup_dtors in H10. unfold gfun_bod in *. case_eq (filter (eq_TypeName (fst (fst x)))
                  (skeleton_cdts (program_skeleton p))); intros; rewrite H in H10; try discriminate.
                inversion H10; subst. apply listTypeDeriv'_lemma in H12. rename H12 into Len.
                simpl in H1. rename H1 into tnEq.
                clear - aEq aGlob H11 Uniq Len tnEq.
                match goal with [|- ?lhs = _] => case_eq lhs; intros end.
                + apply find_some in H. unfold cdts_dtor_names_unique in Uniq.
                  assert (exists n0', nth_error
                    (map (fun y : ScopedName * expr =>
                      (fst y, f (program_skeleton p) tn (fst y) (local (fst x)) (snd y)))
                      (snd x)) n0' = Some p0).
                  { destruct H. apply In_nth_error... }
                  destruct H0. rewrite <- H0. case_eq (x0 =? n0); intros; try rewrite Nat.eqb_eq in H1...
                  apply Unique.filter_unique with (f:=fun y => eq_TypeName (fst (unscope y)) (*fst (fst x)*) tn) in Uniq.
                  rewrite <- filter_map in Uniq.
                  exfalso. case_eq (x0 <? n0); intros.
                  * rewrite <- firstn_skipn with (n:=S x0)(l:=filter _ (skeleton_dtors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. apply map_nth_error with (f:=fst) in H0.
                    rewrite map_map in H0. simpl in H0.
                    change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr) in H0.
                    match goal with [_ : Forall _ (combine _ ?rhs) |- _] =>
                      replace (map fst (snd x)) with (map fst (map fst rhs)) in H0
                    end.
                    2:{ clear - H11 Len. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [|- _ _ (_ _ ?l) = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct p0. destruct a. destruct p0...
                    }
                    apply nth_error_In_firstn in H0. rewrite map_map in H0. rewrite <- map_firstn in H0.
                    specialize Uniq with (fst p0). set (x0':=S x0) in *.
                    match goal with [_ : ?P -> ~In _ _ |- _] => replace (In _ _) with P in H0 end.
                    2:{ erewrite filter_ext... intros. simpl. destruct a0. destruct p1...
                      clear - H H0 aGlob. destruct a. destruct p1. destruct s0; try discriminate...
                      simpl. rewrite in_map_iff in H0. do 2 destruct H0. destruct H.
                      apply in_firstn in H1. rewrite filter_In in H1. destruct H1.
                      destruct x1. destruct p1. rewrite eq_TypeName_eq in H3. simpl in *. subst.
                      destruct p0. simpl in *. destruct s0; try discriminate.
                      rewrite eq_TypeName_eq in *. subst. rewrite eq_QName_eq in *. subst. simpl in *.
                      rewrite <- H3...
                    }
                    pose proof H0 as H0'. pose proof H as H'.
                    apply Uniq in H0. apply H0. destruct H. clear - aEq aGlob H2 H3 H' H0'. symmetry in aEq.
                    rewrite Nat.ltb_lt in H2. eapply nth_error_In_skipn in aEq...
                    destruct (fst p0); try discriminate... rewrite eq_QName_eq in H3. subst.
                    rewrite in_map_iff. exists a. destruct a. destruct p1. destruct s; try discriminate...
                  * rewrite <- firstn_skipn with (n:=S n0)(l:=filter _ (skeleton_dtors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. symmetry in aEq. apply nth_error_In_firstn in aEq.
                    do 2 apply in_map with (f:=fst) in aEq. rewrite map_map in aEq.
                    apply Uniq in aEq. apply aEq. rewrite Nat.eqb_neq in H1. rewrite Nat.ltb_ge in H2.
                    assert (n0 < x0). { omega. } apply nth_error_In_skipn with (m:=S n0) in H0...
                    apply in_map with (f:=fst) in H0. rewrite map_skipn. rewrite <- map_skipn in H0.
                    rewrite map_map in H0. cbn - [skipn] in H0. rewrite map_skipn in H0.
                    match goal with [|- In _ (_ _ ?m')] => replace m' with (map fst (snd x)) end.
                    2:{ symmetry.
                      clear - H11 Len tnEq. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [_ : length ?l' = _ |- _ _ ?l = _] => replace l' with l in * end.
                      2:{ apply filter_ext. intros. destruct a. destruct p0. simpl.
                        rewrite eq_TypeName_eq in tnEq. subst... }
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l0. induction l; intros.
                      - simpl. destruct l1... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct d. destruct a. destruct p0...
                    }
                    destruct H. destruct p0. simpl in *. destruct s; try discriminate.
                    rewrite eq_QName_eq in H4. subst. destruct a. destruct p0. simpl in *.
                    destruct s; try discriminate...
                + exfalso. symmetry in aEq. apply nth_error_In in aEq. do 2 apply in_map with (f:=fst) in aEq.
                  rewrite map_map in aEq.
                  match goal with [_ : In (fst (fst a)) ?l |- _] => replace l with (map fst (snd x)) in aEq end.
                  2:{ clear - H11 Len tnEq.
                      match goal with [_ : (_ (_ _ ?l) =? _) = _ |- _ = map _ ?l'] =>
                        replace l' with l
                      end.
                      2:{ apply filter_ext. intros. rewrite eq_TypeName_eq in tnEq. subst.
                        destruct a. destruct p0... }
                      match goal with [|- _ = _ _ ?l] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                    - simpl. destruct l0... discriminate.
                    - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                      destruct p0. destruct a. destruct p0...
                  }
                  rewrite in_map_iff in aEq. destruct aEq.
                  eapply find_none in H.
                  2:{ rewrite in_map_iff. exists x0. destruct H0. rewrite e. split... }
                  destruct a. destruct p0. simpl in *. destruct s; try discriminate. simpl in *.
                  rewrite eq_QName_refl in H. discriminate.
            }
            rewrite H5.
            match goal with [|- _ = snd (_ _ ?rhs)] => case_eq rhs end; intros...
            2:{ rewrite nth_error_None in H8. rewrite map_length in H8. omega. }
            simpl. clear - H8. apply map_nth_error with (f:=snd) in H8.
            rewrite map_map in H8. simpl in H8. apply nth_error_nth...
         ++ repeat rewrite map_with_index'_irrelevant. repeat f_equal.
            assert (length l0 <= length l1). { simpl in Len. rewrite H3 in Len. simpl in Len. omega. }
            replace [p0] with (rev [p0]) in H4... rewrite <- rev_app_distr in H4.
            destruct l0.
            ** simpl in *. destruct l2; try discriminate...
            ** simpl. cbn - [firstn] in H4. cut (forall {A} (a : A) l1 l2, a::l1 = a::l2 -> l1 = l2).
               2:{ intros. inversion H6... }
               intros. apply H6 with (a:=p1). rewrite <- H4. rewrite app_comm_cons. f_equal.
               clear - H4 H5. simpl in H5. generalize dependent (length l3). intros.
               assert (Aux: forall {A} (l l' : list A), rev l = rev l' <-> l = l').
               { clear. intros. split; intros; subst... apply (f_equal (@rev _)) in H. repeat rewrite rev_involutive in H... }
               rewrite <- rev_unit. rewrite Aux.
               erewrite firstn_nth. 2:{ apply firstn_length_le... }
               Unshelve. 2:{ repeat constructor. }
               f_equal. f_equal. case_eq (rev (firstn (S n) l1)); intros.
               --- destruct l1; simpl in H5; try omega. simpl in H. apply (f_equal (@length _)) in H. simpl in H.
                   rewrite app_length in H. simpl in H. omega.
               --- rewrite H in H4. simpl in H4. inversion H4; subst. clear - Aux H H5.
                   rewrite <- Aux in H. rewrite rev_involutive in H. cbn - [firstn] in H.
                   clear Aux. generalize dependent (rev l). intros. clear l.
                   destruct l1; simpl in H5; try omega.
                   simpl in H. rewrite <- firstn_skipn with (l:=l1)(n:=n). rewrite app_comm_cons. rewrite app_nth1.
                   2:{ simpl. rewrite firstn_length_le; omega. }
                   assert (length (firstn n l1) = n). { apply firstn_length_le. omega. }
                   clear - H H0. generalize dependent (firstn n l1). intros. subst.
                   pose proof H as H'. apply (f_equal (@length _)) in H'. rewrite app_length in H'. simpl in H'.
                   assert (length l = length l0); try omega. rewrite H0. rewrite H.
                   rewrite app_nth2; try omega. rewrite Nat.sub_diag...
    * case_eq (rev l'); intros; try (rewrite H3 in Len; simpl in Len; omega).
      simpl. case_eq (rev (firstn (length l0) l1) ++ [p0]); intros.
      -- destruct (rev (firstn (length l0) l1)); try discriminate.
      -- simpl. f_equal.
         ++ replace [p0] with (rev [p0]) in H4... rewrite <- rev_app_distr in H4.
            replace ([p0] ++ firstn (length l0) l1) with (firstn (S (length l0)) (p0::l1)) in H4...
            rewrite <- H3 in H4. cbn - [firstn] in H. rewrite H4 in H. simpl in H. inversion H.
            match goal with [|- match n0 + ?n'' with | _ => _ end = _] => set (n':=n'') end.
            match goal with [|- ?lhs = _] => replace lhs with (nth (n0+n') (e::l) e) end...
            rewrite H6.
            assert (Len': n0+n' < length (snd p1)).
            { pose proof (in_eq p1 l2). rewrite <- H4 in H5. rewrite H0 in H5. clear - H5 aEq GL.
              apply in_rev in H5. apply firstn_In in H5. apply in_rev in H5.
              assert (
                nth_error (filter (cfunsigs_filterfun_l tn) (skeleton_dtors (program_skeleton p))) n0 <> None).
              { rewrite <- aEq. unfold not. intros. discriminate. }
              apply nth_error_Some in H. rename H into Aux.
              clear aEq. rewrite filter_In in H5. destruct H5. apply in_app_or in H. destruct H.
              - unfold DefuncIII.globalize_aux in H. rewrite in_map_iff in H. do 2 destruct H. subst. simpl.
                pose proof (program_gfun_bods_typecheck_g p). unfold gfun_bods_g_typecheck in H.
                rewrite Forall_forall in H. apply H in H1. clear H. destruct H1 as [qn [args [LookupSig Typ]]].
                inversion Typ; subst. apply listTypeDeriv'_lemma in H9. rewrite Nat.eqb_eq in H9.
                repeat rewrite map_length in H9. unfold gfun_bod. rewrite <- H9.
                simpl in H0. rewrite eq_TypeName_eq in H0. subst. clear - H7 Aux GL.
                unfold lookup_dtors in H7. unfold cfunsigs_filterfun_g. unfold QName in *. unfold gfun_bod in *.
                case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
                  try (rewrite H in H7; discriminate).
                rewrite H in H7. inversion H7; subst. clear - Aux GL.
                unfold global_before_local_dtors in GL. erewrite filter_ext; [ rewrite <- (GL (fst (fst x))) |].
                2:{ intros. destruct a. destruct p0... }
                rewrite app_length. rewrite Nat.add_comm. apply Nat.add_le_lt_mono...
              - unfold DefuncIII.localize_aux in H. rewrite in_map_iff in H. do 2 destruct H. subst. simpl.
                pose proof (program_gfun_bods_typecheck_l p). unfold gfun_bods_l_typecheck in H.
                rewrite Forall_forall in H. apply H in H1. clear H. destruct H1 as [qn [args [LookupSig Typ]]].
                inversion Typ; subst. apply listTypeDeriv'_lemma in H9. rewrite Nat.eqb_eq in H9.
                repeat rewrite map_length in H9. unfold gfun_bod. rewrite <- H9.
                simpl in H0. rewrite eq_TypeName_eq in H0. subst. clear - H7 Aux GL.
                unfold lookup_dtors in H7. unfold cfunsigs_filterfun_g. unfold QName in *. unfold gfun_bod in *.
                case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_cdts (program_skeleton p))); intros;
                  try (rewrite H in H7; discriminate).
                rewrite H in H7. inversion H7; subst. clear - Aux GL.
                unfold global_before_local_dtors in GL. erewrite filter_ext; [ rewrite <- (GL (fst (fst x))) |].
                2:{ intros. destruct a. destruct p0... }
                rewrite app_length. rewrite Nat.add_comm. apply Nat.add_le_lt_mono...
            }
            match goal with [|- _ = snd (_ _ (find ?rhsf (map ?rhsf' _)))] =>
              assert (find rhsf (map rhsf' (snd p1)) = nth_error (map rhsf' (snd p1)) (n0+n'))
            end.
            { rewrite filter_In in H2. destruct H2 as [_ H2]. unfold cfunsigs_filterfun_l in H2.
              assert (is_local (fst (fst a))). { destruct a. destruct p2. destruct s; try discriminate... constructor. }
              rename H2 into aLoc. clear - H0 H4 aEq aLoc GL. pose proof aEq as n0Some.
              replace n0 with (n0+n'-n') in aEq... 2:{ omega. }
              rewrite <- nth_error_app2 with (l:=(filter (cfunsigs_filterfun_g tn)
                (skeleton_dtors (program_skeleton p)))) in aEq.
              2:{ unfold n'. omega. }
              unfold global_before_local_dtors in GL.
              assert (filter (cfunsigs_filterfun_g tn)
                (skeleton_dtors (program_skeleton p)) ++
                filter (cfunsigs_filterfun_l tn)
                  (skeleton_dtors (program_skeleton p)) =
                filter (fun x => eq_TypeName (fst (unscope (fst (fst x)))) tn)
                  (skeleton_dtors (program_skeleton p))).
              { apply GL. }
              rewrite H in aEq. clear - aEq aLoc H0 H4.
              pose proof (in_eq p1 l2). rewrite <- H4 in H. rewrite H0 in H.
              apply in_rev in H. apply in_firstn in H. apply in_rev in H.
              rewrite filter_In in H. destruct H. apply in_app_or in H.
              pose proof (skeleton_cdts_dtor_names_unique (program_skeleton p)) as Uniq. destruct H.
              - pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
                rewrite Forall_forall in TypG. unfold DefuncIII.globalize_aux in H.
                rewrite in_map_iff in H. do 2 destruct H. apply TypG in H2.
                destruct H2 as [qn [args [LookupSig Typ]]]. inversion Typ; subst.
                simpl. unfold lookup_dtors in H10. unfold gfun_bod in *. case_eq (filter (eq_TypeName (fst (fst x)))
                  (skeleton_cdts (program_skeleton p))); intros; rewrite H in H10; try discriminate.
                inversion H10; subst. apply listTypeDeriv'_lemma in H12. rename H12 into Len.
                simpl in H1. rename H1 into tnEq.
                clear - aEq aLoc H11 Uniq Len tnEq.
                match goal with [|- ?lhs = _] => case_eq lhs; intros end.
                + apply find_some in H. unfold cdts_dtor_names_unique in Uniq.
                  assert (exists n0', nth_error
                    (map (fun y : ScopedName * expr =>
                      (fst y, f (program_skeleton p) tn (fst y) (global (fst x)) (snd y)))
                      (snd x)) n0' = Some p0).
                  { destruct H. apply In_nth_error... }
                  destruct H0. rewrite <- H0. case_eq (x0 =? n0+n'); intros; try rewrite Nat.eqb_eq in H1...
                  apply Unique.filter_unique with (f:=fun y => eq_TypeName (fst (unscope y)) (*fst (fst x)*) tn) in Uniq.
                  rewrite <- filter_map in Uniq.
                  exfalso. case_eq (x0 <? n0+n'); intros.
                  * rewrite <- firstn_skipn with (n:=S x0)(l:=filter _ (skeleton_dtors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. apply map_nth_error with (f:=fst) in H0.
                    rewrite map_map in H0. simpl in H0.
                    change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr) in H0.
                    match goal with [_ : Forall _ (combine _ ?rhs) |- _] =>
                      replace (map fst (snd x)) with (map fst (map fst rhs)) in H0
                    end.
                    2:{ clear - H11 Len. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [|- _ _ (_ _ ?l) = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct p0. destruct a. destruct p0...
                    }
                    apply nth_error_In_firstn in H0. rewrite map_map in H0. rewrite <- map_firstn in H0.
                    specialize Uniq with (fst p0). set (x0':=S x0) in *.
                    match goal with [_ : ?P -> ~In _ _ |- _] => replace (In _ _) with P in H0 end.
                    2:{ erewrite filter_ext... intros. simpl. destruct a0. destruct p1...
                      clear - H H0 aLoc. destruct a. destruct p1. destruct s0; try discriminate...
                      simpl. rewrite in_map_iff in H0. do 2 destruct H0. destruct H.
                      apply in_firstn in H1. rewrite filter_In in H1. destruct H1.
                      destruct x1. destruct p1. rewrite eq_TypeName_eq in H3. simpl in *. subst.
                      destruct p0. simpl in *. destruct s0; try discriminate.
                      rewrite eq_TypeName_eq in *. subst. rewrite eq_QName_eq in *. subst. simpl in *.
                      rewrite <- H3...
                    }
                    pose proof H0 as H0'. pose proof H as H'.
                    apply Uniq in H0. apply H0. destruct H. clear - aEq aLoc H2 H3 H' H0'. symmetry in aEq.
                    rewrite Nat.ltb_lt in H2. eapply nth_error_In_skipn in aEq...
                    destruct (fst p0); try discriminate... rewrite eq_QName_eq in H3. subst.
                    rewrite in_map_iff. exists a. destruct a. destruct p1. destruct s; try discriminate...
                  * rewrite <- firstn_skipn with (n:=S (n0+n'))(l:=filter _ (skeleton_dtors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. symmetry in aEq. apply nth_error_In_firstn in aEq.
                    do 2 apply in_map with (f:=fst) in aEq. rewrite map_map in aEq.
                    apply Uniq in aEq. apply aEq. rewrite Nat.eqb_neq in H1. rewrite Nat.ltb_ge in H2.
                    assert (n0+n' < x0). { omega. } apply nth_error_In_skipn with (m:=S (n0+n')) in H0...
                    apply in_map with (f:=fst) in H0. rewrite map_skipn. rewrite <- map_skipn in H0.
                    rewrite map_map in H0. cbn - [skipn] in H0. rewrite map_skipn in H0.
                    match goal with [|- In _ (_ _ ?m')] => replace m' with (map fst (snd x)) end.
                    2:{ symmetry.
                      clear - H11 Len tnEq. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [_ : length ?l' = _ |- _ _ ?l = _] => replace l' with l in * end.
                      2:{ apply filter_ext. intros. destruct a. destruct p0. simpl.
                        rewrite eq_TypeName_eq in tnEq. subst... }
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l0. induction l; intros.
                      - simpl. destruct l1... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct d. destruct a. destruct p0...
                    }
                    destruct H. destruct p0. simpl in *. destruct s; try discriminate.
                    rewrite eq_QName_eq in H4. subst. destruct a. destruct p0. simpl in *.
                    destruct s; try discriminate...
                + exfalso. symmetry in aEq. apply nth_error_In in aEq. do 2 apply in_map with (f:=fst) in aEq.
                    rewrite map_map in aEq.
                    match goal with [_ : In (fst (fst a)) ?l |- _] => replace l with (map fst (snd x)) in aEq end.
                    2:{ clear - H11 Len tnEq.
                      match goal with [_ : (_ (_ _ ?l) =? _) = _ |- _ = map _ ?l'] =>
                        replace l' with l
                      end.
                      2:{ apply filter_ext. intros. rewrite eq_TypeName_eq in tnEq. subst.
                        destruct a. destruct p0... }
                        match goal with [|- _ = _ _ ?l] => generalize dependent l end.
                        generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                      destruct p0. destruct a. destruct p0...
                  }
                  rewrite in_map_iff in aEq. destruct aEq.
                  eapply find_none in H.
                  2:{ rewrite in_map_iff. exists x0. destruct H0. rewrite e. split... }
                  destruct a. destruct p0. simpl in *. destruct s; try discriminate. simpl in *.
                  rewrite eq_QName_refl in H. discriminate.
              - pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
                rewrite Forall_forall in TypL. unfold DefuncIII.localize_aux in H.
                rewrite in_map_iff in H. do 2 destruct H. apply TypL in H2.
                destruct H2 as [qn [args [LookupSig Typ]]]. inversion Typ; subst.
                simpl. unfold lookup_dtors in H10. unfold gfun_bod in *. case_eq (filter (eq_TypeName (fst (fst x)))
                  (skeleton_cdts (program_skeleton p))); intros; rewrite H in H10; try discriminate.
                inversion H10; subst. apply listTypeDeriv'_lemma in H12. rename H12 into Len.
                simpl in H1. rename H1 into tnEq.
                clear - aEq aLoc H11 Uniq Len tnEq.
                match goal with [|- ?lhs = _] => case_eq lhs; intros end.
                + apply find_some in H. unfold cdts_dtor_names_unique in Uniq.
                  assert (exists n0', nth_error
                    (map (fun y : ScopedName * expr =>
                      (fst y, f (program_skeleton p) tn (fst y) (local (fst x)) (snd y)))
                      (snd x)) n0' = Some p0).
                  { destruct H. apply In_nth_error... }
                  destruct H0. rewrite <- H0. case_eq (x0 =? n0+n'); intros; try rewrite Nat.eqb_eq in H1...
                  apply Unique.filter_unique with (f:=fun y => eq_TypeName (fst (unscope y)) (*fst (fst x)*) tn) in Uniq.
                  rewrite <- filter_map in Uniq.
                  exfalso. case_eq (x0 <? n0+n'); intros.
                  * rewrite <- firstn_skipn with (n:=S x0)(l:=filter _ (skeleton_dtors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. apply map_nth_error with (f:=fst) in H0.
                    rewrite map_map in H0. simpl in H0.
                    change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr) in H0.
                    match goal with [_ : Forall _ (combine _ ?rhs) |- _] =>
                      replace (map fst (snd x)) with (map fst (map fst rhs)) in H0
                    end.
                    2:{ clear - H11 Len. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [|- _ _ (_ _ ?l) = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct p0. destruct a. destruct p0...
                    }
                    apply nth_error_In_firstn in H0. rewrite map_map in H0. rewrite <- map_firstn in H0.
                    specialize Uniq with (fst p0). set (x0':=S x0) in *.
                    match goal with [_ : ?P -> ~In _ _ |- _] => replace (In _ _) with P in H0 end.
                    2:{ erewrite filter_ext... intros. simpl. destruct a0. destruct p1...
                      clear - H H0 aLoc. destruct a. destruct p1. destruct s0; try discriminate...
                      simpl. rewrite in_map_iff in H0. do 2 destruct H0. destruct H.
                      apply in_firstn in H1. rewrite filter_In in H1. destruct H1.
                      destruct x1. destruct p1. rewrite eq_TypeName_eq in H3. simpl in *. subst.
                      destruct p0. simpl in *. destruct s0; try discriminate.
                      rewrite eq_TypeName_eq in *. subst. rewrite eq_QName_eq in *. subst. simpl in *.
                      rewrite <- H3...
                    }
                    pose proof H0 as H0'. pose proof H as H'.
                    apply Uniq in H0. apply H0. destruct H. clear - aEq aLoc H2 H3 H' H0'. symmetry in aEq.
                    rewrite Nat.ltb_lt in H2. eapply nth_error_In_skipn in aEq...
                    destruct (fst p0); try discriminate... rewrite eq_QName_eq in H3. subst.
                    rewrite in_map_iff. exists a. destruct a. destruct p1. destruct s; try discriminate...
                  * rewrite <- firstn_skipn with (n:=S (n0+n'))(l:=filter _ (skeleton_dtors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. symmetry in aEq. apply nth_error_In_firstn in aEq.
                    do 2 apply in_map with (f:=fst) in aEq. rewrite map_map in aEq.
                    apply Uniq in aEq. apply aEq. rewrite Nat.eqb_neq in H1. rewrite Nat.ltb_ge in H2.
                    assert (n0+n' < x0). { omega. } apply nth_error_In_skipn with (m:=S (n0+n')) in H0...
                    apply in_map with (f:=fst) in H0. rewrite map_skipn. rewrite <- map_skipn in H0.
                    rewrite map_map in H0. cbn - [skipn] in H0. rewrite map_skipn in H0.
                    match goal with [|- In _ (_ _ ?m')] => replace m' with (map fst (snd x)) end.
                    2:{ symmetry.
                      clear - H11 Len tnEq. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [_ : length ?l' = _ |- _ _ ?l = _] => replace l' with l in * end.
                      2:{ apply filter_ext. intros. destruct a. destruct p0. simpl.
                        rewrite eq_TypeName_eq in tnEq. subst... }
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l0. induction l; intros.
                      - simpl. destruct l1... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct d. destruct a. destruct p0...
                    }
                    destruct H. destruct p0. simpl in *. destruct s; try discriminate.
                    rewrite eq_QName_eq in H4. subst. destruct a. destruct p0. simpl in *.
                    destruct s; try discriminate...
                + exfalso. symmetry in aEq. apply nth_error_In in aEq. do 2 apply in_map with (f:=fst) in aEq.
                    rewrite map_map in aEq.
                    match goal with [_ : In (fst (fst a)) ?l |- _] => replace l with (map fst (snd x)) in aEq end.
                    2:{ clear - H11 Len tnEq.
                      match goal with [_ : (_ (_ _ ?l) =? _) = _ |- _ = map _ ?l'] =>
                        replace l' with l
                      end.
                      2:{ apply filter_ext. intros. rewrite eq_TypeName_eq in tnEq. subst.
                        destruct a. destruct p0... }
                        match goal with [|- _ = _ _ ?l] => generalize dependent l end.
                        generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                      destruct p0. destruct a. destruct p0...
                  }
                  rewrite in_map_iff in aEq. destruct aEq.
                  eapply find_none in H.
                  2:{ rewrite in_map_iff. exists x0. destruct H0. rewrite e. split... }
                  destruct a. destruct p0. simpl in *. destruct s; try discriminate. simpl in *.
                  rewrite eq_QName_refl in H. discriminate.
            }
            rewrite H5.
            match goal with [|- _ = snd (_ _ ?rhs)] => case_eq rhs end; intros...
            2:{ rewrite nth_error_None in H8. rewrite map_length in H8. omega. }
            simpl. clear - H8. apply map_nth_error with (f:=snd) in H8.
            rewrite map_map in H8. simpl in H8. apply nth_error_nth...
         ++ repeat rewrite map_with_index'_irrelevant. repeat f_equal.
            assert (length l0 <= length l1). { simpl in Len. rewrite H3 in Len. simpl in Len. omega. }
            replace [p0] with (rev [p0]) in H4... rewrite <- rev_app_distr in H4.
            destruct l0.
            ** simpl in *. destruct l2; try discriminate...
            ** simpl. cbn - [firstn] in H4. cut (forall {A} (a : A) l1 l2, a::l1 = a::l2 -> l1 = l2).
               2:{ intros. inversion H6... }
               intros. apply H6 with (a:=p1). rewrite <- H4. rewrite app_comm_cons. f_equal.
               clear - H4 H5. simpl in H5. generalize dependent (length l3). intros.
               assert (Aux: forall {A} (l l' : list A), rev l = rev l' <-> l = l').
               { clear. intros. split; intros; subst... apply (f_equal (@rev _)) in H. repeat rewrite rev_involutive in H... }
               rewrite <- rev_unit. rewrite Aux.
               erewrite firstn_nth. 2:{ apply firstn_length_le... }
               Unshelve. 2:{ repeat constructor. }
               f_equal. f_equal. case_eq (rev (firstn (S n) l1)); intros.
               --- destruct l1; simpl in H5; try omega. simpl in H. apply (f_equal (@length _)) in H. simpl in H.
                   rewrite app_length in H. simpl in H. omega.
               --- rewrite H in H4. simpl in H4. inversion H4; subst. clear - Aux H H5.
                   rewrite <- Aux in H. rewrite rev_involutive in H. cbn - [firstn] in H.
                   clear Aux. generalize dependent (rev l). intros. clear l.
                   destruct l1; simpl in H5; try omega.
                   simpl in H. rewrite <- firstn_skipn with (l:=l1)(n:=n). rewrite app_comm_cons. rewrite app_nth1.
                   2:{ simpl. rewrite firstn_length_le; omega. }
                   assert (length (firstn n l1) = n). { apply firstn_length_le. omega. }
                   clear - H H0. generalize dependent (firstn n l1). intros. subst.
                   pose proof H as H'. apply (f_equal (@length _)) in H'. rewrite app_length in H'. simpl in H'.
                   assert (length l = length l0); try omega. rewrite H0. rewrite H.
                   rewrite app_nth2; try omega. rewrite Nat.sub_diag...
Qed.

Lemma transpose_cfbods : forall p tn l l' (f : skeleton -> TypeName -> ScopedName -> ScopedName -> expr -> expr) c n
  (GL : global_before_local_ctors (skeleton_ctors (program_skeleton p))),
  l = map (fun x => map (fun y => f (program_skeleton p) tn (fst x) (fst y) (snd y)) (snd x)) l' ->
  l' = filter (fun x : ScopedName * gfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
              (RefuncIII.globalize_aux (program_cfun_bods_g p) ++
               RefuncIII.localize_aux (program_cfun_bods_l p)) ->
  n = length (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p)) ++
    filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))) ->
  transpose l n =
    map (map (fun x => snd (snd x)))
      (map
        (fun x0 => map (RefuncIII.map_alternative_for_filter (unscope (fst x0)) c)
                       (map (fun x => (unscope (fst x), snd x))
                         (map (fun x => (fst x, map (fun y => (fst y, f (program_skeleton p) tn (fst x) (fst y) (snd y))) (snd x))) l')))
        (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p)))) ++
    map (map (fun x => snd (snd x)))
      (map
        (fun x0 => map (RefuncIII.map_alternative_for_filter_l (unscope (fst x0)) c)
                       (map (fun x => (unscope (fst x), snd x))
                         (map (fun x => (fst x, map (fun y => (fst y, f (program_skeleton p) tn (fst x) (fst y) (snd y))) (snd x))) l')))
        (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p)))).
Proof with eauto.
intros.
generalize H.
replace l' with (rev (firstn (length l) (rev l'))).
2:{ rewrite H. rewrite map_length. clear. rewrite <- rev_length. rewrite firstn_all. rewrite rev_involutive... }
assert (length l <= length l') as Len.
{ subst. rewrite map_length... }
clear H.
induction l as [| l l0]; intros.
- simpl. rewrite H1. clear. do 2 rewrite map_map. simpl. rewrite <- map_app.
  match goal with [|- _ = map _ ?l] => generalize l end. intros. induction l...
  simpl. f_equal...
- simpl. destruct l.
  + subst l'. clear - H.
    match goal with [_ : _ = map _ (rev (firstn _ (rev ?x))) |- _] =>
      assert (In [] (map (map snd) (map snd x)))
    end.
    { pose proof (in_eq [] l0). rewrite H in H0. clear - H0. rewrite in_map_iff in H0. destruct H0. destruct H.
      apply in_rev in H0. apply firstn_In in H0. apply in_rev in H0.
      case_eq (snd x); intros; rewrite H1 in H; try discriminate. rewrite in_map_iff. exists (snd x). rewrite H1.
      simpl. split... rewrite in_map_iff. exists x. split...
    }
    clear - H0. rewrite map_map in H0. rewrite in_map_iff in H0. destruct H0. destruct H.
    rewrite filter_In in H0. destruct H0. apply in_app_or in H0. destruct H0.
    * pose proof (program_cfun_bods_typecheck_g p) as TypG.
      unfold cfun_bods_g_typecheck in TypG. rewrite Forall_forall in TypG.
      unfold RefuncIII.globalize_aux in H0. rewrite in_map_iff in H0. do 2 destruct H0.
      apply TypG in H2. clear TypG. destruct H2 as [qn [args [t [SigLookup Typ]]]].
      inversion Typ; subst.
      (**)
      clear H11. rename H13 into H9. rename H15 into H11.
      (**)
      unfold lookup_ctors in H9. unfold QName in *. unfold cfun_bod in *.
      case_eq (filter (eq_TypeName (fst (fst x0))) (skeleton_dts (program_skeleton p))); intros;
        rewrite H0 in H9; try discriminate.
      inversion H9; subst. clear H9. simpl in H. rewrite H in H11. apply listTypeDeriv'_lemma_ctx in H11.
      rewrite Nat.eqb_eq in H11. simpl in H1. rewrite eq_TypeName_eq in H1. subst tn.
      clear - H11. unfold gfunsigs_filterfun_g. unfold gfunsigs_filterfun_l.
      erewrite filter_ext with (l:=skeleton_ctors (program_skeleton p))
        (g:=fun x => match fst x with global _ => true | local _ => false end
              && eq_TypeName (fst (unscope (fst x))) (fst (fst x0))).
      2:{ intros. destruct a. destruct s... simpl. apply eq_TypeName_symm. }
      rewrite <- filter_compose.
      case_eq (filter (fun x : ctor => eq_TypeName (fst (unscope (fst x))) (fst (fst x0)))
           (skeleton_ctors (program_skeleton p))); intros.
      2:{ erewrite filter_ext in H; [rewrite H in H11; discriminate |]. intros. destruct a... }
      simpl.
      erewrite filter_ext with (l:=skeleton_ctors (program_skeleton p))
        (g:=fun x => match fst x with global _ => false | local _ => true end
              && eq_TypeName (fst (unscope (fst x))) (fst (fst x0))).
      2:{ intros. destruct a. destruct s... simpl. apply eq_TypeName_symm. }
      rewrite <- filter_compose. rewrite H...
    * pose proof (program_cfun_bods_typecheck_l p) as TypL.
      unfold cfun_bods_l_typecheck in TypL. rewrite Forall_forall in TypL.
      unfold RefuncIII.localize_aux in H0. rewrite in_map_iff in H0. do 2 destruct H0.
      apply TypL in H2. clear TypL. destruct H2 as [qn [args [t [SigLookup Typ]]]].
      inversion Typ; subst.
      (**)
      clear H11. rename H13 into H9. rename H15 into H11.
      (**)
      unfold lookup_ctors in H9. unfold QName in *. unfold cfun_bod in *.
      case_eq (filter (eq_TypeName (fst (fst x0))) (skeleton_dts (program_skeleton p))); intros;
        rewrite H0 in H9; try discriminate.
      inversion H9; subst. clear H9. simpl in H. rewrite H in H11. apply listTypeDeriv'_lemma_ctx in H11.
      rewrite Nat.eqb_eq in H11. simpl in H1. rewrite eq_TypeName_eq in H1. subst tn.
      clear - H11. unfold gfunsigs_filterfun_g. unfold gfunsigs_filterfun_l.
      erewrite filter_ext with (l:=skeleton_ctors (program_skeleton p))
        (g:=fun x => match fst x with global _ => true | local _ => false end
              && eq_TypeName (fst (unscope (fst x))) (fst (fst x0))).
      2:{ intros. destruct a. destruct s... simpl. apply eq_TypeName_symm. }
      rewrite <- filter_compose.
      case_eq (filter (fun x : ctor => eq_TypeName (fst (unscope (fst x))) (fst (fst x0)))
           (skeleton_ctors (program_skeleton p))); intros.
      2:{ erewrite filter_ext in H; [rewrite H in H11; discriminate |]. intros. destruct a... }
      simpl.
      erewrite filter_ext with (l:=skeleton_ctors (program_skeleton p))
        (g:=fun x => match fst x with global _ => false | local _ => true end
              && eq_TypeName (fst (unscope (fst x))) (fst (fst x0))).
      2:{ intros. destruct a.  destruct s... simpl. apply eq_TypeName_symm. }
      rewrite <- filter_compose. rewrite H...
  + rewrite IHl0.
    2:{ simpl in Len. omega. }
    2:{ clear - H Len. match goal with [|- _ = map ?m _] => generalize dependent m end.
     clear - Len. intros. cbn - [firstn] in H. apply (f_equal (@rev _)) in H. cbn - [firstn] in H.
     case_eq (rev l'); intros; rewrite H0 in H.
     - rewrite firstn_nil in H. simpl in H. destruct (rev l0); discriminate.
     - cbn - [rev] in H. rewrite rev_map_rev in H. case_eq (length l0); intros.
       + simpl. destruct l0; try discriminate...
       + simpl. rewrite map_app. simpl in *. replace [e :: l] with (rev [e :: l]) in H...
         rewrite <- rev_app_distr in H. apply (f_equal (@rev _)) in H. rewrite rev_involutive in H.
         simpl in H. assert ((e :: l) :: l0 = (e :: l) :: map l1 (rev (firstn n l2)) ++ [l1 p] ->
          l0 = map l1 (rev (firstn n l2)) ++ [l1 p]) as Aux.
         { intros. inversion H2... }
         apply Aux. clear Aux. rewrite H. rewrite H1 in *.
         destruct l0; try discriminate.
         destruct l2. { simpl in *. discriminate. }
         assert (Aux: hd_error (rev (map l1 (firstn (S n) (p0::l2)))) = Some (e::l)).
         { match goal with [|- hd_error ?lhs = _] => case_eq lhs; intros end.
           - rewrite H2 in H. discriminate.
           - rewrite H2 in H. inversion H; subst...
         }
         assert (Len': length l' <= length l2 + 2).
         { rewrite <- rev_length. rewrite H0. simpl. omega. }
         clear - Aux Len Len'. rewrite app_comm_cons. f_equal. simpl in *.
         case_eq (rev (map l1 (firstn n l2)) ++ [l1 p0]); intros.
         * destruct (rev (map l1 (firstn n l2))); discriminate.
         * f_equal.
           -- rewrite H in Aux. unfold hd_error in Aux. inversion Aux; subst...
           -- apply (f_equal (@tl _)) in H. simpl in H. subst. clear - Len Len'.
              assert (n <= length l2).
              { intros. omega. }
              clear - H. generalize dependent n. generalize p0.
              induction l2; intros.
              ++ destruct n... simpl in H. omega.
              ++ destruct n... simpl. destruct n... unfold tl.
                 case_eq (rev (map l1 (firstn (S n) l2))); intros.
                 ** destruct l2.
                    --- simpl in H. omega.
                    --- simpl in H0. destruct (rev (map l1 (firstn n l2))); discriminate.
                 ** simpl. replace [a] with (rev [a])... rewrite <- rev_app_distr.
                    replace ([a] ++ firstn n l2) with (firstn (S n) (a::l2))...
                    rewrite map_app. simpl in H. rewrite <- IHl2; try omega.
                    cbn - [firstn]. f_equal.
                    assert (tl (rev (map l1 (firstn (S n) l2)) ++ [l1 a]) =
                      tl (rev (map l1 (firstn (S n) l2))) ++ [l1 a]).
                    { destruct l2; simpl in H; try omega. simpl.
                      case_eq (rev (map l1 (firstn n l2))); intros...
                    }
                    rewrite H1. f_equal. rewrite H0...
    }
    repeat rewrite map_with_index_map. repeat rewrite with_index_map_map.
    rewrite map_with_index_app. rewrite with_index'_map_map. rewrite with_index_map_map.
    clear IHl0.
    rewrite <- rev_length with (l:=l') in Len. unfold map_with_index.
    f_equal; apply map_with_index'_ext_in; intros a n0 H2 aEq.
    * case_eq (rev l'); intros; try (rewrite H3 in Len; simpl in Len; omega).
      simpl. case_eq (rev (firstn (length l0) l1) ++ [p0]); intros.
      -- destruct (rev (firstn (length l0) l1)); try discriminate.
      -- simpl. f_equal.
         ++ replace [p0] with (rev [p0]) in H4... rewrite <- rev_app_distr in H4.
            replace ([p0] ++ firstn (length l0) l1) with (firstn (S (length l0)) (p0::l1)) in H4...
            rewrite <- H3 in H4. cbn - [firstn] in H. rewrite H4 in H. simpl in H. inversion H.
            replace (n0+0) with n0...
            match goal with [|- ?lhs = _] => replace lhs with (nth n0 (e::l) e) end...
            rewrite H6.
            assert (Len': n0 < length (snd p1)).
            { pose proof (in_eq p1 l2). rewrite <- H4 in H5. rewrite H0 in H5. clear - H5 aEq.
              apply in_rev in H5. apply firstn_In in H5. apply in_rev in H5.
              assert (
                nth_error (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))) n0 <> None).
              { rewrite <- aEq. unfold not. intros. discriminate. }
              apply nth_error_Some in H.
              assert (length (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))) <= length (snd p1)).
              2:{ omega... }
              clear H aEq. rewrite filter_In in H5. destruct H5. apply in_app_or in H. destruct H.
              - unfold RefuncIII.globalize_aux in H. rewrite in_map_iff in H. do 2 destruct H. subst. simpl.
                pose proof (program_cfun_bods_typecheck_g p). unfold cfun_bods_g_typecheck in H.
                rewrite Forall_forall in H. apply H in H1. clear H. destruct H1 as [qn [args [t [LookupSig Typ]]]].
                inversion Typ; subst.
                (**)
                clear H9. rename H13 into H9. rename H11 into H7.
                (**)
                apply listTypeDeriv'_lemma_ctx in H9. rewrite Nat.eqb_eq in H9.
                repeat rewrite map_length in H9. unfold cfun_bod. rewrite <- H9.
                simpl in H0. rewrite eq_TypeName_eq in H0. subst. clear - H7.
                unfold lookup_ctors in H7. unfold gfunsigs_filterfun_g. unfold QName in *. unfold cfun_bod in *.
                case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
                  try (rewrite H in H7; discriminate).
                rewrite H in H7. inversion H7; subst. clear. generalize (skeleton_ctors (program_skeleton p)).
                induction c... simpl. destruct a. destruct s.
                + case_eq (eq_TypeName (fst (unscope (local q))) (fst (fst x))); intros; simpl; omega.
                + rewrite eq_TypeName_symm. simpl. case_eq (eq_TypeName (fst q) (fst (fst x))); intros; simpl; omega.
              - unfold RefuncIII.localize_aux in H. rewrite in_map_iff in H. do 2 destruct H. subst. simpl.
                pose proof (program_cfun_bods_typecheck_l p). unfold cfun_bods_l_typecheck in H.
                rewrite Forall_forall in H. apply H in H1. clear H. destruct H1 as [qn [args [t [LookupSig Typ]]]].
                inversion Typ; subst.
                (**)
                clear H9. rename H13 into H9. rename H11 into H7.
                (**)
                apply listTypeDeriv'_lemma_ctx in H9. rewrite Nat.eqb_eq in H9.
                repeat rewrite map_length in H9. unfold cfun_bod. rewrite <- H9.
                simpl in H0. rewrite eq_TypeName_eq in H0. subst. clear - H7.
                unfold lookup_ctors in H7. unfold gfunsigs_filterfun_g. unfold QName in *. unfold cfun_bod in *.
                case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
                  try (rewrite H in H7; discriminate).
                rewrite H in H7. inversion H7; subst. clear. generalize (skeleton_ctors (program_skeleton p)).
                induction c... simpl. destruct a. destruct s.
                + case_eq (eq_TypeName (fst (unscope (local q))) (fst (fst x))); intros; simpl; omega.
                + rewrite eq_TypeName_symm. simpl. case_eq (eq_TypeName (fst q) (fst (fst x))); intros; simpl; omega.
            }
            match goal with [|- _ = snd (_ _ (find ?rhsf (map ?rhsf' _)))] =>
              assert (find rhsf (map rhsf' (snd p1)) = nth_error (map rhsf' (snd p1)) n0)
            end.
            { rewrite filter_In in H2. destruct H2 as [_ H2]. unfold gfunsigs_filterfun_g in H2.
              assert (is_global (fst a)). { destruct a. destruct s; try discriminate... constructor. }
              rename H2 into aGlob. clear - H0 H4 aEq aGlob GL. pose proof aEq as n0Some.
              rewrite <- nth_error_app1 with (l':=(filter (gfunsigs_filterfun_l tn)
                (skeleton_ctors (program_skeleton p)))) in aEq.
              2:{ rewrite <- nth_error_Some. rewrite <- aEq. unfold not. intros. discriminate. }
              clear n0Some. unfold global_before_local_ctors in GL.
              assert (filter (gfunsigs_filterfun_g tn)
                (skeleton_ctors (program_skeleton p)) ++
                filter (gfunsigs_filterfun_l tn)
                  (skeleton_ctors (program_skeleton p)) =
                filter (fun x => eq_TypeName (fst (unscope (fst x))) tn)
                  (skeleton_ctors (program_skeleton p))).
              { apply GL. }
              rewrite H in aEq. clear - aEq aGlob H0 H4.
              pose proof (in_eq p1 l2). rewrite <- H4 in H. rewrite H0 in H.
              apply in_rev in H. apply in_firstn in H. apply in_rev in H.
              rewrite filter_In in H. destruct H. apply in_app_or in H.
              pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq. destruct H.
              - pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
                rewrite Forall_forall in TypG. unfold RefuncIII.globalize_aux in H.
                rewrite in_map_iff in H. do 2 destruct H. apply TypG in H2.
                destruct H2 as [qn [args [t [LookupSig Typ]]]].
                inversion Typ; subst.
                (**)
                clear H12. rename H14 into H10. clear H11. rename H15 into H11. rename H16 into H12.
                (**)
                simpl. unfold lookup_ctors in H10. unfold cfun_bod in *. case_eq (filter (eq_TypeName (fst (fst x)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H in H10; try discriminate.
                inversion H10; subst. apply listTypeDeriv'_lemma_ctx in H12. rename H12 into Len.
                simpl in H1. rename H1 into tnEq.
                clear - aEq aGlob H11 Uniq Len tnEq.
                match goal with [|- ?lhs = _] => case_eq lhs; intros end.
                + apply find_some in H. unfold dts_ctor_names_unique in Uniq.
                  assert (exists n0', nth_error
                    (map (fun y : ScopedName * expr =>
                      (fst y, f (program_skeleton p) tn (global (fst x)) (fst y) (snd y)))
                      (snd x)) n0' = Some p0).
                  { destruct H. apply In_nth_error... }
                  destruct H0. rewrite <- H0. case_eq (x0 =? n0); intros; try rewrite Nat.eqb_eq in H1...
                  apply Unique.filter_unique with (f:=fun y => eq_TypeName (fst (unscope y)) (*fst (fst x)*) tn) in Uniq.
                  rewrite <- filter_map in Uniq.
                  exfalso. case_eq (x0 <? n0); intros.
                  * rewrite <- firstn_skipn with (n:=S x0)(l:=filter _ (skeleton_ctors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. apply map_nth_error with (f:=fst) in H0.
                    rewrite map_map in H0. simpl in H0.
                    change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr) in H0.
                    match goal with [_ : Forall _ (combine _ ?rhs) |- _] =>
                      replace (map fst (snd x)) with (map fst rhs) in H0
                    end.
                    2:{ clear - H11 Len. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct p0. destruct a...
                    }
                    apply nth_error_In_firstn in H0. (*rewrite map_map in H0.*) rewrite <- map_firstn in H0.
                    specialize Uniq with (fst p0). set (x0':=S x0) in *.
                    match goal with [_ : ?P -> ~In _ _ |- _] => replace (In _ _) with P in H0 end.
                    2:{ erewrite filter_ext... intros. simpl. destruct a0.
                      clear - H H0 aGlob. destruct a. destruct s0; try discriminate...
                      simpl. rewrite in_map_iff in H0. do 2 destruct H0. destruct H.
                      apply in_firstn in H1. rewrite filter_In in H1. destruct H1.
                      destruct x1. rewrite eq_TypeName_eq in H3. simpl in *. subst.
                      destruct p0. simpl in *. destruct s0; try discriminate.
                      rewrite eq_TypeName_eq in *. subst. rewrite eq_QName_eq in *. subst. simpl in *.
                      rewrite <- H3...
                    }
                    pose proof H0 as H0'. pose proof H as H'.
                    apply Uniq in H0. apply H0. destruct H. clear - aEq aGlob H2 H3 H' H0'. symmetry in aEq.
                    rewrite Nat.ltb_lt in H2. eapply nth_error_In_skipn in aEq...
                    destruct (fst p0); try discriminate... rewrite eq_QName_eq in H3. subst.
                    rewrite in_map_iff. exists a. destruct a. destruct s; try discriminate...
                  * rewrite <- firstn_skipn with (n:=S n0)(l:=filter _ (skeleton_ctors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. symmetry in aEq. apply nth_error_In_firstn in aEq.
                    (**)apply in_map with (f:=fst) in aEq. (*rewrite map_map in aEq.*)
                    apply Uniq in aEq. apply aEq. rewrite Nat.eqb_neq in H1. rewrite Nat.ltb_ge in H2.
                    assert (n0 < x0). { omega. } apply nth_error_In_skipn with (m:=S n0) in H0...
                    apply in_map with (f:=fst) in H0. rewrite map_skipn. rewrite <- map_skipn in H0.
                    rewrite map_map in H0. cbn - [skipn] in H0. rewrite map_skipn in H0.
                    match goal with [|- In _ (_ _ ?m')] => replace m' with (map fst (snd x)) end.
                    2:{ symmetry.
                      clear - H11 Len tnEq. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [_ : length ?l' = _ |- _ _ ?l = _] => replace l' with l in * end.
                      2:{ apply filter_ext. intros. destruct a. simpl.
                        rewrite eq_TypeName_eq in tnEq. subst... }
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l0. induction l; intros.
                      - simpl. destruct l1... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct c. destruct a...
                    }
                    destruct H. destruct p0. simpl in *. destruct s; try discriminate.
                    rewrite eq_QName_eq in H4. subst. destruct a. simpl in *.
                    destruct s; try discriminate...
                + exfalso. symmetry in aEq. apply nth_error_In in aEq. (**)apply in_map with (f:=fst) in aEq.
                  (*rewrite map_map in aEq.*)
                  match goal with [_ : In (fst a) ?l |- _] => replace l with (map fst (snd x)) in aEq end.
                  2:{ clear - H11 Len tnEq.
                      match goal with [_ : (_ (_ _ ?l) =? _) = _ |- _ = map _ ?l'] =>
                        replace l' with l
                      end.
                      2:{ apply filter_ext. intros. rewrite eq_TypeName_eq in tnEq. subst.
                        destruct a... }
                      match goal with [|- _ = _ _ ?l] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                    - simpl. destruct l0... discriminate.
                    - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                      destruct p0. destruct a...
                  }
                  rewrite in_map_iff in aEq. destruct aEq.
                  eapply find_none in H.
                  2:{ rewrite in_map_iff. exists x0. destruct H0. rewrite e. split... }
                  destruct a. simpl in *. destruct s; try discriminate. simpl in *.
                  rewrite eq_QName_refl in H. discriminate.
              - pose proof (program_cfun_bods_typecheck_l p) as TypL. unfold cfun_bods_l_typecheck in TypL.
                rewrite Forall_forall in TypL. unfold RefuncIII.localize_aux in H.
                rewrite in_map_iff in H. do 2 destruct H. apply TypL in H2.
                destruct H2 as [qn [args [t [LookupSig Typ]]]].
                inversion Typ; subst.
                (**)
                clear H12. rename H14 into H10. clear H11. rename H15 into H11. rename H16 into H12.
                (**)
                simpl. unfold lookup_ctors in H10. unfold cfun_bod in *. case_eq (filter (eq_TypeName (fst (fst x)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H in H10; try discriminate.
                inversion H10; subst. apply listTypeDeriv'_lemma_ctx in H12. rename H12 into Len.
                simpl in H1. rename H1 into tnEq.
                clear - aEq aGlob H11 Uniq Len tnEq.
                match goal with [|- ?lhs = _] => case_eq lhs; intros end.
                + apply find_some in H. unfold dts_ctor_names_unique in Uniq.
                  assert (exists n0', nth_error
                    (map (fun y : ScopedName * expr =>
                      (fst y, f (program_skeleton p) tn (local (fst x)) (fst y) (snd y)))
                      (snd x)) n0' = Some p0).
                  { destruct H. apply In_nth_error... }
                  destruct H0. rewrite <- H0. case_eq (x0 =? n0); intros; try rewrite Nat.eqb_eq in H1...
                  apply Unique.filter_unique with (f:=fun y => eq_TypeName (fst (unscope y)) (*fst (fst x)*) tn) in Uniq.
                  rewrite <- filter_map in Uniq.
                  exfalso. case_eq (x0 <? n0); intros.
                  * rewrite <- firstn_skipn with (n:=S x0)(l:=filter _ (skeleton_ctors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. apply map_nth_error with (f:=fst) in H0.
                    rewrite map_map in H0. simpl in H0.
                    change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr) in H0.
                    match goal with [_ : Forall _ (combine _ ?rhs) |- _] =>
                      replace (map fst (snd x)) with (map fst rhs) in H0
                    end.
                    2:{ clear - H11 Len. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct p0. destruct a...
                    }
                    apply nth_error_In_firstn in H0. (*rewrite map_map in H0.*) rewrite <- map_firstn in H0.
                    specialize Uniq with (fst p0). set (x0':=S x0) in *.
                    match goal with [_ : ?P -> ~In _ _ |- _] => replace (In _ _) with P in H0 end.
                    2:{ erewrite filter_ext... intros. simpl. destruct a0.
                      clear - H H0 aGlob. destruct a. destruct s0; try discriminate...
                      simpl. rewrite in_map_iff in H0. do 2 destruct H0. destruct H.
                      apply in_firstn in H1. rewrite filter_In in H1. destruct H1.
                      destruct x1. rewrite eq_TypeName_eq in H3. simpl in *. subst.
                      destruct p0. simpl in *. destruct s0; try discriminate.
                      rewrite eq_TypeName_eq in *. subst. rewrite eq_QName_eq in *. subst. simpl in *.
                      rewrite <- H3...
                    }
                    pose proof H0 as H0'. pose proof H as H'.
                    apply Uniq in H0. apply H0. destruct H. clear - aEq aGlob H2 H3 H' H0'. symmetry in aEq.
                    rewrite Nat.ltb_lt in H2. eapply nth_error_In_skipn in aEq...
                    destruct (fst p0); try discriminate... rewrite eq_QName_eq in H3. subst.
                    rewrite in_map_iff. exists a. destruct a. destruct s; try discriminate...
                  * rewrite <- firstn_skipn with (n:=S n0)(l:=filter _ (skeleton_ctors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. symmetry in aEq. apply nth_error_In_firstn in aEq.
                    (**)apply in_map with (f:=fst) in aEq. (*rewrite map_map in aEq.*)
                    apply Uniq in aEq. apply aEq. rewrite Nat.eqb_neq in H1. rewrite Nat.ltb_ge in H2.
                    assert (n0 < x0). { omega. } apply nth_error_In_skipn with (m:=S n0) in H0...
                    apply in_map with (f:=fst) in H0. rewrite map_skipn. rewrite <- map_skipn in H0.
                    rewrite map_map in H0. cbn - [skipn] in H0. rewrite map_skipn in H0.
                    match goal with [|- In _ (_ _ ?m')] => replace m' with (map fst (snd x)) end.
                    2:{ symmetry.
                      clear - H11 Len tnEq. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [_ : length ?l' = _ |- _ _ ?l = _] => replace l' with l in * end.
                      2:{ apply filter_ext. intros. destruct a. simpl.
                        rewrite eq_TypeName_eq in tnEq. subst... }
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l0. induction l; intros.
                      - simpl. destruct l1... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct c. destruct a...
                    }
                    destruct H. destruct p0. simpl in *. destruct s; try discriminate.
                    rewrite eq_QName_eq in H4. subst. destruct a. simpl in *.
                    destruct s; try discriminate...
                + exfalso. symmetry in aEq. apply nth_error_In in aEq. (**)apply in_map with (f:=fst) in aEq.
                  (*rewrite map_map in aEq.*)
                  match goal with [_ : In (fst a) ?l |- _] => replace l with (map fst (snd x)) in aEq end.
                  2:{ clear - H11 Len tnEq.
                      match goal with [_ : (_ (_ _ ?l) =? _) = _ |- _ = map _ ?l'] =>
                        replace l' with l
                      end.
                      2:{ apply filter_ext. intros. rewrite eq_TypeName_eq in tnEq. subst.
                        destruct a... }
                      match goal with [|- _ = _ _ ?l] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                    - simpl. destruct l0... discriminate.
                    - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                      destruct p0. destruct a...
                  }
                  rewrite in_map_iff in aEq. destruct aEq.
                  eapply find_none in H.
                  2:{ rewrite in_map_iff. exists x0. destruct H0. rewrite e. split... }
                  destruct a. simpl in *. destruct s; try discriminate. simpl in *.
                  rewrite eq_QName_refl in H. discriminate.
            }
            rewrite H5.
            match goal with [|- _ = snd (_ _ ?rhs)] => case_eq rhs end; intros...
            2:{ rewrite nth_error_None in H8. rewrite map_length in H8. omega. }
            simpl. clear - H8. apply map_nth_error with (f:=snd) in H8.
            rewrite map_map in H8. simpl in H8. apply nth_error_nth...
         ++ repeat rewrite map_with_index'_irrelevant. repeat f_equal.
            assert (length l0 <= length l1). { simpl in Len. rewrite H3 in Len. simpl in Len. omega. }
            replace [p0] with (rev [p0]) in H4... rewrite <- rev_app_distr in H4.
            destruct l0.
            ** simpl in *. destruct l2; try discriminate...
            ** simpl. cbn - [firstn] in H4. cut (forall {A} (a : A) l1 l2, a::l1 = a::l2 -> l1 = l2).
               2:{ intros. inversion H6... }
               intros. apply H6 with (a:=p1). rewrite <- H4. rewrite app_comm_cons. f_equal.
               clear - H4 H5. simpl in H5. generalize dependent (length l3). intros.
               assert (Aux: forall {A} (l l' : list A), rev l = rev l' <-> l = l').
               { clear. intros. split; intros; subst... apply (f_equal (@rev _)) in H. repeat rewrite rev_involutive in H... }
               rewrite <- rev_unit. rewrite Aux.
               erewrite firstn_nth. 2:{ apply firstn_length_le... }
               Unshelve. 2:{ repeat constructor. }
               f_equal. f_equal. case_eq (rev (firstn (S n) l1)); intros.
               --- destruct l1; simpl in H5; try omega. simpl in H. apply (f_equal (@length _)) in H. simpl in H.
                   rewrite app_length in H. simpl in H. omega.
               --- rewrite H in H4. simpl in H4. inversion H4; subst. clear - Aux H H5.
                   rewrite <- Aux in H. rewrite rev_involutive in H. cbn - [firstn] in H.
                   clear Aux. generalize dependent (rev l). intros. clear l.
                   destruct l1; simpl in H5; try omega.
                   simpl in H. rewrite <- firstn_skipn with (l:=l1)(n:=n). rewrite app_comm_cons. rewrite app_nth1.
                   2:{ simpl. rewrite firstn_length_le; omega. }
                   assert (length (firstn n l1) = n). { apply firstn_length_le. omega. }
                   clear - H H0. generalize dependent (firstn n l1). intros. subst.
                   pose proof H as H'. apply (f_equal (@length _)) in H'. rewrite app_length in H'. simpl in H'.
                   assert (length l = length l0); try omega. rewrite H0. rewrite H.
                   rewrite app_nth2; try omega. rewrite Nat.sub_diag...
    * case_eq (rev l'); intros; try (rewrite H3 in Len; simpl in Len; omega).
      simpl. case_eq (rev (firstn (length l0) l1) ++ [p0]); intros.
      -- destruct (rev (firstn (length l0) l1)); try discriminate.
      -- simpl. f_equal.
         ++ replace [p0] with (rev [p0]) in H4... rewrite <- rev_app_distr in H4.
            replace ([p0] ++ firstn (length l0) l1) with (firstn (S (length l0)) (p0::l1)) in H4...
            rewrite <- H3 in H4. cbn - [firstn] in H. rewrite H4 in H. simpl in H. inversion H.
            match goal with [|- match n0 + ?n'' with | _ => _ end = _] => set (n':=n'') end.
            match goal with [|- ?lhs = _] => replace lhs with (nth (n0+n') (e::l) e) end...
            rewrite H6.
            assert (Len': n0+n' < length (snd p1)).
            { pose proof (in_eq p1 l2). rewrite <- H4 in H5. rewrite H0 in H5. clear - H5 aEq GL.
              apply in_rev in H5. apply firstn_In in H5. apply in_rev in H5.
              assert (
                nth_error (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))) n0 <> None).
              { rewrite <- aEq. unfold not. intros. discriminate. }
              apply nth_error_Some in H. rename H into Aux.
              clear aEq. rewrite filter_In in H5. destruct H5. apply in_app_or in H. destruct H.
              - unfold RefuncIII.globalize_aux in H. rewrite in_map_iff in H. do 2 destruct H. subst. simpl.
                pose proof (program_cfun_bods_typecheck_g p). unfold cfun_bods_g_typecheck in H.
                rewrite Forall_forall in H. apply H in H1. clear H. destruct H1 as [qn [args [t [LookupSig Typ]]]].
                inversion Typ; subst.
                (**)
                clear H9. rename H13 into H9. rename H11 into H7.
                (**)
                apply listTypeDeriv'_lemma_ctx in H9. rewrite Nat.eqb_eq in H9.
                repeat rewrite map_length in H9. unfold cfun_bod. rewrite <- H9.
                simpl in H0. rewrite eq_TypeName_eq in H0. subst. clear - H7 Aux GL.
                unfold lookup_ctors in H7. unfold gfunsigs_filterfun_g. unfold QName in *. unfold cfun_bod in *.
                case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
                  try (rewrite H in H7; discriminate).
                rewrite H in H7. inversion H7; subst. clear - Aux GL.
                unfold global_before_local_ctors in GL. erewrite filter_ext; [ rewrite <- (GL (fst (fst x))) |].
                2:{ intros. destruct a... }
                rewrite app_length. rewrite Nat.add_comm. apply Nat.add_le_lt_mono...
              - unfold RefuncIII.localize_aux in H. rewrite in_map_iff in H. do 2 destruct H. subst. simpl.
                pose proof (program_cfun_bods_typecheck_l p). unfold cfun_bods_l_typecheck in H.
                rewrite Forall_forall in H. apply H in H1. clear H. destruct H1 as [qn [args [t [LookupSig Typ]]]].
                inversion Typ; subst.
                (**)
                clear H9. rename H13 into H9. rename H11 into H7.
                (**)
                apply listTypeDeriv'_lemma_ctx in H9. rewrite Nat.eqb_eq in H9.
                repeat rewrite map_length in H9. unfold cfun_bod. rewrite <- H9.
                simpl in H0. rewrite eq_TypeName_eq in H0. subst. clear - H7 Aux GL.
                unfold lookup_ctors in H7. unfold gfunsigs_filterfun_g. unfold QName in *. unfold cfun_bod in *.
                case_eq (filter (eq_TypeName (fst (fst x))) (skeleton_dts (program_skeleton p))); intros;
                  try (rewrite H in H7; discriminate).
                rewrite H in H7. inversion H7; subst. clear - Aux GL.
                unfold global_before_local_dtors in GL. erewrite filter_ext; [ rewrite <- (GL (fst (fst x))) |].
                2:{ intros. destruct a... }
                rewrite app_length. rewrite Nat.add_comm. apply Nat.add_le_lt_mono...
            }
            match goal with [|- _ = snd (_ _ (find ?rhsf (map ?rhsf' _)))] =>
              assert (find rhsf (map rhsf' (snd p1)) = nth_error (map rhsf' (snd p1)) (n0+n'))
            end.
            { rewrite filter_In in H2. destruct H2 as [_ H2]. unfold gfunsigs_filterfun_l in H2.
              assert (is_local (fst a)). { destruct a. destruct s; try discriminate... constructor. }
              rename H2 into aLoc. clear - H0 H4 aEq aLoc GL. pose proof aEq as n0Some.
              replace n0 with (n0+n'-n') in aEq... 2:{ omega. }
              rewrite <- nth_error_app2 with (l:=(filter (gfunsigs_filterfun_g tn)
                (skeleton_ctors (program_skeleton p)))) in aEq.
              2:{ unfold n'. omega. }
              unfold global_before_local_ctors in GL.
              assert (filter (gfunsigs_filterfun_g tn)
                (skeleton_ctors (program_skeleton p)) ++
                filter (gfunsigs_filterfun_l tn)
                  (skeleton_ctors (program_skeleton p)) =
                filter (fun x => eq_TypeName (fst (unscope (fst x))) tn)
                  (skeleton_ctors (program_skeleton p))).
              { apply GL. }
              rewrite H in aEq. clear - aEq aLoc H0 H4.
              pose proof (in_eq p1 l2). rewrite <- H4 in H. rewrite H0 in H.
              apply in_rev in H. apply in_firstn in H. apply in_rev in H.
              rewrite filter_In in H. destruct H. apply in_app_or in H.
              pose proof (skeleton_dts_ctor_names_unique (program_skeleton p)) as Uniq. destruct H.
              - pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
                rewrite Forall_forall in TypG. unfold RefuncIII.globalize_aux in H.
                rewrite in_map_iff in H. do 2 destruct H. apply TypG in H2.
                destruct H2 as [qn [args [t [LookupSig Typ]]]].
                inversion Typ; subst.
                (**)
                clear H12. rename H16 into H12. clear H11. rename H15 into H11. rename H14 into H10.
                (**)
                simpl. unfold lookup_ctors in H10. unfold cfun_bod in *. case_eq (filter (eq_TypeName (fst (fst x)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H in H10; try discriminate.
                inversion H10; subst. apply listTypeDeriv'_lemma_ctx in H12. rename H12 into Len.
                simpl in H1. rename H1 into tnEq.
                clear - aEq aLoc H11 Uniq Len tnEq.
                match goal with [|- ?lhs = _] => case_eq lhs; intros end.
                + apply find_some in H. unfold dts_ctor_names_unique in Uniq.
                  assert (exists n0', nth_error
                    (map (fun y : ScopedName * expr =>
                      (fst y, f (program_skeleton p) tn (global (fst x)) (fst y) (snd y)))
                      (snd x)) n0' = Some p0).
                  { destruct H. apply In_nth_error... }
                  destruct H0. rewrite <- H0. case_eq (x0 =? n0+n'); intros; try rewrite Nat.eqb_eq in H1...
                  apply Unique.filter_unique with (f:=fun y => eq_TypeName (fst (unscope y)) (*fst (fst x)*) tn) in Uniq.
                  rewrite <- filter_map in Uniq.
                  exfalso. case_eq (x0 <? n0+n'); intros.
                  * rewrite <- firstn_skipn with (n:=S x0)(l:=filter _ (skeleton_ctors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. apply map_nth_error with (f:=fst) in H0.
                    rewrite map_map in H0. simpl in H0.
                    change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr) in H0.
                    match goal with [_ : Forall _ (combine _ ?rhs) |- _] =>
                      replace (map fst (snd x)) with (map fst rhs) in H0
                    end.
                    2:{ clear - H11 Len. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct p0. destruct a...
                    }
                    apply nth_error_In_firstn in H0. (*rewrite map_map in H0.*) rewrite <- map_firstn in H0.
                    specialize Uniq with (fst p0). set (x0':=S x0) in *.
                    match goal with [_ : ?P -> ~In _ _ |- _] => replace (In _ _) with P in H0 end.
                    2:{ erewrite filter_ext... intros. simpl. destruct a0...
                      clear - H H0 aLoc. destruct a. destruct s0; try discriminate...
                      simpl. rewrite in_map_iff in H0. do 2 destruct H0. destruct H.
                      apply in_firstn in H1. rewrite filter_In in H1. destruct H1.
                      destruct x1. rewrite eq_TypeName_eq in H3. simpl in *. subst.
                      destruct p0. simpl in *. destruct s0; try discriminate.
                      rewrite eq_TypeName_eq in *. subst. rewrite eq_QName_eq in *. subst. simpl in *.
                      rewrite <- H3...
                    }
                    pose proof H0 as H0'. pose proof H as H'.
                    apply Uniq in H0. apply H0. destruct H. clear - aEq aLoc H2 H3 H' H0'. symmetry in aEq.
                    rewrite Nat.ltb_lt in H2. eapply nth_error_In_skipn in aEq...
                    destruct (fst p0); try discriminate... rewrite eq_QName_eq in H3. subst.
                    rewrite in_map_iff. exists a. destruct a. destruct s; try discriminate...
                  * rewrite <- firstn_skipn with (n:=S (n0+n'))(l:=filter _ (skeleton_ctors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. symmetry in aEq. apply nth_error_In_firstn in aEq.
                    (**)apply in_map with (f:=fst) in aEq. (*rewrite map_map in aEq.*)
                    apply Uniq in aEq. apply aEq. rewrite Nat.eqb_neq in H1. rewrite Nat.ltb_ge in H2.
                    assert (n0+n' < x0). { omega. } apply nth_error_In_skipn with (m:=S (n0+n')) in H0...
                    apply in_map with (f:=fst) in H0. rewrite map_skipn. rewrite <- map_skipn in H0.
                    rewrite map_map in H0. cbn - [skipn] in H0. rewrite map_skipn in H0.
                    match goal with [|- In _ (_ _ ?m')] => replace m' with (map fst (snd x)) end.
                    2:{ symmetry.
                      clear - H11 Len tnEq. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [_ : length ?l' = _ |- _ _ ?l = _] => replace l' with l in * end.
                      2:{ apply filter_ext. intros. destruct a. simpl.
                        rewrite eq_TypeName_eq in tnEq. subst... }
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l0. induction l; intros.
                      - simpl. destruct l1... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct c. destruct a...
                    }
                    destruct H. destruct p0. simpl in *. destruct s; try discriminate.
                    rewrite eq_QName_eq in H4. subst. destruct a. simpl in *.
                    destruct s; try discriminate...
                + exfalso. symmetry in aEq. apply nth_error_In in aEq. (**)apply in_map with (f:=fst) in aEq.
                    (*rewrite map_map in aEq.*)
                    match goal with [_ : In (fst a) ?l |- _] => replace l with (map fst (snd x)) in aEq end.
                    2:{ clear - H11 Len tnEq.
                      match goal with [_ : (_ (_ _ ?l) =? _) = _ |- _ = map _ ?l'] =>
                        replace l' with l
                      end.
                      2:{ apply filter_ext. intros. rewrite eq_TypeName_eq in tnEq. subst.
                        destruct a... }
                        match goal with [|- _ = _ _ ?l] => generalize dependent l end.
                        generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                      destruct p0. destruct a...
                  }
                  rewrite in_map_iff in aEq. destruct aEq.
                  eapply find_none in H.
                  2:{ rewrite in_map_iff. exists x0. destruct H0. rewrite e. split... }
                  destruct a. simpl in *. destruct s; try discriminate. simpl in *.
                  rewrite eq_QName_refl in H. discriminate.
              - pose proof (program_cfun_bods_typecheck_l p) as TypL. unfold cfun_bods_l_typecheck in TypL.
                rewrite Forall_forall in TypL. unfold RefuncIII.localize_aux in H.
                rewrite in_map_iff in H. do 2 destruct H. apply TypL in H2.
                destruct H2 as [qn [args [t [LookupSig Typ]]]].
                inversion Typ; subst.
                (**)
                clear H12. rename H16 into H12. clear H11. rename H15 into H11. rename H14 into H10.
                (**)
                simpl. unfold lookup_ctors in H10. unfold cfun_bod in *. case_eq (filter (eq_TypeName (fst (fst x)))
                  (skeleton_dts (program_skeleton p))); intros; rewrite H in H10; try discriminate.
                inversion H10; subst. apply listTypeDeriv'_lemma_ctx in H12. rename H12 into Len.
                simpl in H1. rename H1 into tnEq.
                clear - aEq aLoc H11 Uniq Len tnEq.
                match goal with [|- ?lhs = _] => case_eq lhs; intros end.
                + apply find_some in H. unfold dts_ctor_names_unique in Uniq.
                  assert (exists n0', nth_error
                    (map (fun y : ScopedName * expr =>
                      (fst y, f (program_skeleton p) tn (local (fst x)) (fst y) (snd y)))
                      (snd x)) n0' = Some p0).
                  { destruct H. apply In_nth_error... }
                  destruct H0. rewrite <- H0. case_eq (x0 =? n0+n'); intros; try rewrite Nat.eqb_eq in H1...
                  apply Unique.filter_unique with (f:=fun y => eq_TypeName (fst (unscope y)) (*fst (fst x)*) tn) in Uniq.
                  rewrite <- filter_map in Uniq.
                  exfalso. case_eq (x0 <? n0+n'); intros.
                  * rewrite <- firstn_skipn with (n:=S x0)(l:=filter _ (skeleton_ctors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. apply map_nth_error with (f:=fst) in H0.
                    rewrite map_map in H0. simpl in H0.
                    change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr) in H0.
                    match goal with [_ : Forall _ (combine _ ?rhs) |- _] =>
                      replace (map fst (snd x)) with (map fst rhs) in H0
                    end.
                    2:{ clear - H11 Len. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct p0. destruct a...
                    }
                    apply nth_error_In_firstn in H0. (*rewrite map_map in H0.*) rewrite <- map_firstn in H0.
                    specialize Uniq with (fst p0). set (x0':=S x0) in *.
                    match goal with [_ : ?P -> ~In _ _ |- _] => replace (In _ _) with P in H0 end.
                    2:{ erewrite filter_ext... intros. simpl. destruct a0...
                      clear - H H0 aLoc. destruct a. destruct s0; try discriminate...
                      simpl. rewrite in_map_iff in H0. do 2 destruct H0. destruct H.
                      apply in_firstn in H1. rewrite filter_In in H1. destruct H1.
                      destruct x1. rewrite eq_TypeName_eq in H3. simpl in *. subst.
                      destruct p0. simpl in *. destruct s0; try discriminate.
                      rewrite eq_TypeName_eq in *. subst. rewrite eq_QName_eq in *. subst. simpl in *.
                      rewrite <- H3...
                    }
                    pose proof H0 as H0'. pose proof H as H'.
                    apply Uniq in H0. apply H0. destruct H. clear - aEq aLoc H2 H3 H' H0'. symmetry in aEq.
                    rewrite Nat.ltb_lt in H2. eapply nth_error_In_skipn in aEq...
                    destruct (fst p0); try discriminate... rewrite eq_QName_eq in H3. subst.
                    rewrite in_map_iff. exists a. destruct a. destruct s; try discriminate...
                  * rewrite <- firstn_skipn with (n:=S (n0+n'))(l:=filter _ (skeleton_ctors (program_skeleton p))) in Uniq.
                    rewrite map_app in Uniq. apply Unique.uniqueness_app_not_in in Uniq.
                    rewrite Forall_forall in Uniq. symmetry in aEq. apply nth_error_In_firstn in aEq.
                    (**)apply in_map with (f:=fst) in aEq. (*rewrite map_map in aEq.*)
                    apply Uniq in aEq. apply aEq. rewrite Nat.eqb_neq in H1. rewrite Nat.ltb_ge in H2.
                    assert (n0+n' < x0). { omega. } apply nth_error_In_skipn with (m:=S (n0+n')) in H0...
                    apply in_map with (f:=fst) in H0. rewrite map_skipn. rewrite <- map_skipn in H0.
                    rewrite map_map in H0. cbn - [skipn] in H0. rewrite map_skipn in H0.
                    match goal with [|- In _ (_ _ ?m')] => replace m' with (map fst (snd x)) end.
                    2:{ symmetry.
                      clear - H11 Len tnEq. repeat rewrite map_length in Len. rewrite Nat.eqb_eq in Len.
                      match goal with [_ : length ?l' = _ |- _ _ ?l = _] => replace l' with l in * end.
                      2:{ apply filter_ext. intros. destruct a. simpl.
                        rewrite eq_TypeName_eq in tnEq. subst... }
                      match goal with [|- _ _ ?l = _] => generalize dependent l end.
                      generalize (snd x). intros l l0. generalize l0. induction l; intros.
                      - simpl. destruct l1... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                        destruct c. destruct a...
                    }
                    destruct H. destruct p0. simpl in *. destruct s; try discriminate.
                    rewrite eq_QName_eq in H4. subst. destruct a. simpl in *.
                    destruct s; try discriminate...
                + exfalso. symmetry in aEq. apply nth_error_In in aEq. (**)apply in_map with (f:=fst) in aEq.
                    (*rewrite map_map in aEq.*)
                    match goal with [_ : In (fst a) ?l |- _] => replace l with (map fst (snd x)) in aEq end.
                    2:{ clear - H11 Len tnEq.
                      match goal with [_ : (_ (_ _ ?l) =? _) = _ |- _ = map _ ?l'] =>
                        replace l' with l
                      end.
                      2:{ apply filter_ext. intros. rewrite eq_TypeName_eq in tnEq. subst.
                        destruct a... }
                        match goal with [|- _ = _ _ ?l] => generalize dependent l end.
                        generalize (snd x). intros l l0. generalize l. induction l0; intros.
                      - simpl. destruct l0... discriminate.
                      - simpl. destruct l1; try discriminate. simpl. inversion H11; subst. f_equal...
                      destruct p0. destruct a...
                  }
                  rewrite in_map_iff in aEq. destruct aEq.
                  eapply find_none in H.
                  2:{ rewrite in_map_iff. exists x0. destruct H0. rewrite e. split... }
                  destruct a. simpl in *. destruct s; try discriminate. simpl in *.
                  rewrite eq_QName_refl in H. discriminate.
            }
            rewrite H5.
            match goal with [|- _ = snd (_ _ ?rhs)] => case_eq rhs end; intros...
            2:{ rewrite nth_error_None in H8. rewrite map_length in H8. omega. }
            simpl. clear - H8. apply map_nth_error with (f:=snd) in H8.
            rewrite map_map in H8. simpl in H8. apply nth_error_nth...
         ++ repeat rewrite map_with_index'_irrelevant. repeat f_equal.
            assert (length l0 <= length l1). { simpl in Len. rewrite H3 in Len. simpl in Len. omega. }
            replace [p0] with (rev [p0]) in H4... rewrite <- rev_app_distr in H4.
            destruct l0.
            ** simpl in *. destruct l2; try discriminate...
            ** simpl. cbn - [firstn] in H4. cut (forall {A} (a : A) l1 l2, a::l1 = a::l2 -> l1 = l2).
               2:{ intros. inversion H6... }
               intros. apply H6 with (a:=p1). rewrite <- H4. rewrite app_comm_cons. f_equal.
               clear - H4 H5. simpl in H5. generalize dependent (length l3). intros.
               assert (Aux: forall {A} (l l' : list A), rev l = rev l' <-> l = l').
               { clear. intros. split; intros; subst... apply (f_equal (@rev _)) in H. repeat rewrite rev_involutive in H... }
               rewrite <- rev_unit. rewrite Aux.
               erewrite firstn_nth. 2:{ apply firstn_length_le... }
               Unshelve. 2:{ repeat constructor. }
               f_equal. f_equal. case_eq (rev (firstn (S n) l1)); intros.
               --- destruct l1; simpl in H5; try omega. simpl in H. apply (f_equal (@length _)) in H. simpl in H.
                   rewrite app_length in H. simpl in H. omega.
               --- rewrite H in H4. simpl in H4. inversion H4; subst. clear - Aux H H5.
                   rewrite <- Aux in H. rewrite rev_involutive in H. cbn - [firstn] in H.
                   clear Aux. generalize dependent (rev l). intros. clear l.
                   destruct l1; simpl in H5; try omega.
                   simpl in H. rewrite <- firstn_skipn with (l:=l1)(n:=n). rewrite app_comm_cons. rewrite app_nth1.
                   2:{ simpl. rewrite firstn_length_le; omega. }
                   assert (length (firstn n l1) = n). { apply firstn_length_le. omega. }
                   clear - H H0. generalize dependent (firstn n l1). intros. subst.
                   pose proof H as H'. apply (f_equal (@length _)) in H'. rewrite app_length in H'. simpl in H'.
                   assert (length l = length l0); try omega. rewrite H0. rewrite H.
                   rewrite app_nth2; try omega. rewrite Nat.sub_diag...
Qed.



Lemma defunc_is_matrix_transpose : forall p tn P1 P2 P3 P4 P5 pr
  (GL : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (Nonempty : program_gfun_bods_for_type tn p <> []),
  pr = defunctionalize_program p tn P1 P2 P3 P4 P5 ->
  program_cfun_bods_for_type tn pr =
    (read_cfuns_from_matrix (transpose_matrix (read_gfuns_into_matrix
      (map (fun x => (fst x, map (fun y => (fst y, defunc_term_helper (program_skeleton p) tn (fst y) (fst x) (snd y))) (snd x)))
         (program_gfun_bods_for_type tn p))))).
Proof with eauto.
intros. subst. unfold program_cfun_bods_for_type. simpl. clear - GL Nonempty.
unfold DefuncIII.new_cfun_bods_g. unfold DefuncIII.new_cfun_bods_l.
rewrite map_app. rewrite map_app. repeat rewrite filter_app.
match goal with [|- (_ ++ ?l1) ++ (_ ++ ?l2) = _] => assert (l1 = [] /\ l2 = []) end.
- pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
  unfold dts_cdts_disjoint in Disj.
  clear GL. split.
  + match goal with [|- ?l = _] => case_eq l; intros end...
    exfalso. apply Nonempty. clear Nonempty. pose proof (program_has_all_cfun_bods_g p) as HasSigs.
    pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as SigsDts.
    unfold has_all_cfun_bods in HasSigs. unfold cfun_sigs_in_dts in SigsDts.
    case_eq (program_gfun_bods_for_type tn p); intros... exfalso.
    unfold program_gfun_bods_for_type in H0.
    rewrite combine_fst_snd with (ps:=map _ _) in H. repeat rewrite map_map in H. simpl in H.
    rewrite <- map_map in H. unfold cfun_bod in *. rewrite <- HasSigs in H.
    pose proof (in_eq p0 l) as p0In. rewrite <- H in p0In.
    rewrite filter_In in p0In. destruct p0In as [p0In p0Eq]. destruct p0. apply in_combine_l in p0In.
    rename p0In into sIn. simpl in p0Eq. rename p0Eq into sEq.
    rewrite Forall_forall in SigsDts. rewrite map_map in sIn. rewrite in_map_iff in sIn.
    destruct sIn as [x [xEq xIn]]. apply SigsDts in xIn.
    pose proof (in_eq p1 l0) as p1In. rewrite <- H0 in p1In.
    rewrite filter_In in p1In. destruct p1In as [p1In p1Eq]. apply in_app_or in p1In. destruct p1In.
    * clear - xEq xIn sEq H1 p1Eq Disj. pose proof (program_has_all_gfun_bods_g p) as HasSigs.
      pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as SigsCdts.
      unfold has_all_gfun_bods in HasSigs. unfold gfun_sigs_in_cdts in SigsCdts.
      destruct p1. rewrite in_map_iff in H1. destruct H1 as [x' [x'Eq x'In]].
      rewrite Forall_forall in SigsCdts. destruct x'. inversion x'Eq; subst.
      eapply (in_map fst) in x'In. rewrite <- HasSigs in x'In. rewrite in_map_iff in x'In.
      destruct x'In. destruct H. apply SigsCdts in H0. simpl in *. rewrite eq_TypeName_eq in *. subst.
      unfold QName in *. rewrite <- p1Eq in xIn. clear - xIn H0 Disj.
      specialize Disj with (t:=fst (fst x0)). apply Disj...
    * clear - xEq xIn sEq H1 p1Eq Disj. pose proof (program_has_all_gfun_bods_l p) as HasSigs.
      pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as SigsCdts.
      unfold has_all_gfun_bods in HasSigs. unfold gfun_sigs_in_cdts in SigsCdts.
      destruct p1. rewrite in_map_iff in H1. destruct H1 as [x' [x'Eq x'In]].
      rewrite Forall_forall in SigsCdts. destruct x'. inversion x'Eq; subst.
      eapply (in_map fst) in x'In. rewrite <- HasSigs in x'In. rewrite in_map_iff in x'In.
      destruct x'In. destruct H. apply SigsCdts in H0. simpl in *. rewrite eq_TypeName_eq in *. subst.
      unfold QName in *. rewrite <- p1Eq in xIn. clear - xIn H0 Disj.
      specialize Disj with (t:=fst (fst x0)). apply Disj...
  + match goal with [|- ?l = _] => case_eq l; intros end...
    exfalso. apply Nonempty. clear Nonempty. pose proof (program_has_all_cfun_bods_l p) as HasSigs.
    pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as SigsDts.
    unfold has_all_cfun_bods in HasSigs. unfold cfun_sigs_in_dts in SigsDts.
    case_eq (program_gfun_bods_for_type tn p); intros... exfalso.
    unfold program_gfun_bods_for_type in H0.
    rewrite combine_fst_snd with (ps:=map _ _) in H. repeat rewrite map_map in H. simpl in H.
    rewrite <- map_map in H. unfold cfun_bod in *. rewrite <- HasSigs in H.
    pose proof (in_eq p0 l) as p0In. rewrite <- H in p0In.
    rewrite filter_In in p0In. destruct p0In as [p0In p0Eq]. destruct p0. apply in_combine_l in p0In.
    rename p0In into sIn. simpl in p0Eq. rename p0Eq into sEq.
    rewrite Forall_forall in SigsDts. rewrite map_map in sIn. rewrite in_map_iff in sIn.
    destruct sIn as [x [xEq xIn]]. apply SigsDts in xIn.
    pose proof (in_eq p1 l0) as p1In. rewrite <- H0 in p1In.
    rewrite filter_In in p1In. destruct p1In as [p1In p1Eq]. apply in_app_or in p1In. destruct p1In.
    * clear - xEq xIn sEq H1 p1Eq Disj. pose proof (program_has_all_gfun_bods_g p) as HasSigs.
      pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as SigsCdts.
      unfold has_all_gfun_bods in HasSigs. unfold gfun_sigs_in_cdts in SigsCdts.
      destruct p1. rewrite in_map_iff in H1. destruct H1 as [x' [x'Eq x'In]].
      rewrite Forall_forall in SigsCdts. destruct x'. inversion x'Eq; subst.
      eapply (in_map fst) in x'In. rewrite <- HasSigs in x'In. rewrite in_map_iff in x'In.
      destruct x'In. destruct H. apply SigsCdts in H0. simpl in *. rewrite eq_TypeName_eq in *. subst.
      unfold QName in *. rewrite <- p1Eq in xIn. clear - xIn H0 Disj.
      specialize Disj with (t:=fst (fst x0)). apply Disj...
    * clear - xEq xIn sEq H1 p1Eq Disj. pose proof (program_has_all_gfun_bods_l p) as HasSigs.
      pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as SigsCdts.
      unfold has_all_gfun_bods in HasSigs. unfold gfun_sigs_in_cdts in SigsCdts.
      destruct p1. rewrite in_map_iff in H1. destruct H1 as [x' [x'Eq x'In]].
      rewrite Forall_forall in SigsCdts. destruct x'. inversion x'Eq; subst.
      eapply (in_map fst) in x'In. rewrite <- HasSigs in x'In. rewrite in_map_iff in x'In.
      destruct x'In. destruct H. apply SigsCdts in H0. simpl in *. rewrite eq_TypeName_eq in *. subst.
      unfold QName in *. rewrite <- p1Eq in xIn. clear - xIn H0 Disj.
      specialize Disj with (t:=fst (fst x0)). apply Disj...
- destruct H as [H_1 H_2]. rewrite H_1. rewrite H_2. repeat rewrite app_nil_r. clear H_1 H_2.
  match goal with [|- ?lhs' = _] => set (lhs:=lhs') end.
  unfold program_gfun_bods_for_type.
  unfold read_gfuns_into_matrix.
  match goal with [|- _ = combine ?rhs1' (map ?rhs2' (transpose ?rhs3' ?len'))] =>
    set (rhs1:=rhs1'); set (rhs2:=rhs2'); set (rhs3:=rhs3'); set (len:=len')
  end.
  rewrite combine_fst_snd with (ps:=lhs).
  remember rhs1 as rhs1Eq. unfold rhs1 in Heqrhs1Eq.
  match goal with [_ : _ = match ?m with | [] => [] | l :: _ => map fst (snd l) end |- _] => case_eq m; intros end.
  { unfold program_gfun_bods_for_type in Nonempty. exfalso. apply Nonempty.
    match goal with [|- ?m = []] => destruct m end... discriminate.
  }
  rewrite Heqrhs1Eq. rewrite H.
  clear rhs1 rhs1Eq Heqrhs1Eq. f_equal.
  + unfold lhs. clear - H GL. rewrite map_app.
    repeat (rewrite <- filter_map; rewrite map_map). simpl.
    apply (f_equal (map (fun x => map fst (snd x)))) in H.
    rewrite map_map in H. simpl in H. generalize H. clear H. unfold gfun_bod.
    generalize (snd p0). clear p0. intros.
    match goal with [_ : _ = ?x::?r |- _] => assert (In x (x::r)) end.
    { apply in_eq. }
    rewrite <- H in H0. clear H. rewrite in_map_iff in H0. destruct H0 as [x [H0Eq H0In]].
    inversion H0Eq; subst. rewrite map_map. simpl. clear - H0In GL.
    pose proof (program_gfun_bods_typecheck_g p) as TypG.
    pose proof (program_gfun_bods_typecheck_l p) as TypL.
    rewrite filter_app in H0In. apply in_app_or in H0In. destruct H0In.
    * clear TypL. unfold gfun_bods_g_typecheck in TypG.
      rewrite filter_In in H. destruct H. rewrite in_map_iff in H. do 2 destruct H.
      rewrite Forall_forall in TypG. apply TypG in H1. clear TypG. destruct H1 as [qn [args [Lookup Typ]]].
      rename H0 into TypName. inversion Typ; subst. simpl in *.
      match goal with [|- _ = ?rhs] => replace rhs with (map fst (map fst dtorlist)) end.
      2: { generalize H8. generalize H9. generalize dtorlist. generalize (snd x0). clear. induction l; intros.
        - destruct dtorlist... apply listTypeDeriv'_lemma in H9. rewrite Nat.eqb_eq in H9. discriminate.
        - destruct dtorlist.
          + apply listTypeDeriv'_lemma in H9. rewrite Nat.eqb_eq in H9. discriminate.
          + simpl. f_equal.
            * simpl in H8. inversion H8. destruct a. do 2 destruct p0...
            * inversion H9. inversion H8. rewrite IHl with (dtorlist:=dtorlist)...
      }
      rewrite eq_TypeName_eq in TypName. subst tn.
      clear - H7 GL. unfold lookup_dtors in H7.
      destruct (filter (eq_TypeName (fst (fst x0))) (skeleton_cdts (program_skeleton p)));
        try discriminate.
      inversion H7; subst. clear H7.
      repeat rewrite filter_compose. unfold cfunsigs_filterfun_g. unfold cfunsigs_filterfun_l.
      rewrite filter_ext with (g:=(fun x : ScopedName * list TypeName * TypeName =>
        eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0)) &&
        match fst (fst x) with local _ => false | global _ => true end)).
      2:{ intros. destruct a. destruct p0. destruct s.
       - simpl. rewrite andb_false_r...
       - simpl. rewrite andb_true_r. rewrite eq_TypeName_symm. rewrite andb_diag...
      }
      match goal with [|- ?lhs1' ++ _ = _] => set (lhs1:=lhs1') end.
      rewrite filter_ext with (g:=(fun x : ScopedName * list TypeName * TypeName =>
        eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0)) &&
        match fst (fst x) with local _ => true | global _ => false end)).
      2:{ intros. destruct a. destruct p0. destruct s.
       - simpl. rewrite andb_true_r. rewrite eq_TypeName_symm. rewrite andb_diag...
       - simpl. rewrite andb_false_r...
      }
      unfold lhs1. clear lhs1. repeat rewrite <- filter_compose.
      unfold global_before_local_dtors in GL.
      match goal with [|- _ = _ _ (_ _ (_ ?f' _))] => erewrite filter_ext with (f:=f') end;
        [rewrite <- (GL (fst (fst x0)))|].
      2:{ intros. destruct a. destruct p0... }
      clear GL. rewrite map_map. rewrite map_app.
      f_equal.
      -- unfold cfunsigs_filterfun_g.
         match goal with [|- _ = ?l''] => remember l'' as l' end.
         assert (Aux: Forall (fun x => is_global x) l').
         { rewrite Forall_forall. intros. subst l'.
           rewrite in_map_iff in H. do 2 destruct H. rewrite filter_In in H0. destruct H0.
           destruct x1. destruct p0. destruct s; try discriminate. cbn in H. subst. constructor.
         }
         rewrite <- map_map. rewrite <- map_map with (g:=unscope).
         assert (Aux': l' = map global (map unscope l')).
         { clear - Aux. induction l'... cbn. inversion Aux; subst. rewrite <- IHl'... f_equal.
           inversion H1; subst...
         }
         rewrite Aux'. f_equal. f_equal. subst. clear. f_equal. rewrite filter_compose. apply filter_ext.
         intros. destruct a. destruct p0. cbn. destruct s.
         ++ rewrite andb_false_r...
         ++ cbn. rewrite andb_true_r. apply eq_TypeName_symm.
      -- unfold cfunsigs_filterfun_l.
         match goal with [|- _ = ?l''] => remember l'' as l' end.
         assert (Aux: Forall (fun x => is_local x) l').
         { rewrite Forall_forall. intros. subst l'.
           rewrite in_map_iff in H. do 2 destruct H. rewrite filter_In in H0. destruct H0.
           destruct x1. destruct p0. destruct s; try discriminate. cbn in H. subst. constructor.
         }
         rewrite <- map_map. rewrite <- map_map with (g:=unscope).
         assert (Aux': l' = map local (map unscope l')).
         { clear - Aux. induction l'... cbn. inversion Aux; subst. rewrite <- IHl'... f_equal.
           inversion H1; subst...
         }
         rewrite Aux'. f_equal. f_equal. subst. clear. f_equal. rewrite filter_compose. apply filter_ext.
         intros. destruct a. destruct p0. cbn. destruct s.
         ++ cbn. rewrite andb_true_r. apply eq_TypeName_symm.
         ++ rewrite andb_false_r...
    * clear TypG. unfold gfun_bods_l_typecheck in TypL.
      rewrite filter_In in H. destruct H. rewrite in_map_iff in H. do 2 destruct H.
      rewrite Forall_forall in TypL. apply TypL in H1. clear TypL. destruct H1 as [qn [args [Lookup Typ]]].
      rename H0 into TypName. inversion Typ; subst. simpl in *.
      match goal with [|- _ = ?rhs] => replace rhs with (map fst (map fst dtorlist)) end.
      2: { generalize H8. generalize H9. generalize dtorlist. generalize (snd x0). clear. induction l; intros.
        - destruct dtorlist... apply listTypeDeriv'_lemma in H9. rewrite Nat.eqb_eq in H9. discriminate.
        - destruct dtorlist.
          + apply listTypeDeriv'_lemma in H9. rewrite Nat.eqb_eq in H9. discriminate.
          + simpl. f_equal.
            * simpl in H8. inversion H8. destruct a. do 2 destruct p0...
            * inversion H9. inversion H8. rewrite IHl with (dtorlist:=dtorlist)...
      }
      rewrite eq_TypeName_eq in TypName. subst tn.
      clear - H7 GL. unfold lookup_dtors in H7.
      destruct (filter (eq_TypeName (fst (fst x0))) (skeleton_cdts (program_skeleton p)));
        try discriminate.
      inversion H7; subst. clear H7.
      repeat rewrite filter_compose. unfold cfunsigs_filterfun_g. unfold cfunsigs_filterfun_l.
      rewrite filter_ext with (g:=(fun x : ScopedName * list TypeName * TypeName =>
        eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0)) &&
        match fst (fst x) with local _ => false | global _ => true end)).
      2:{ intros. destruct a. destruct p0. destruct s.
       - simpl. rewrite andb_false_r...
       - simpl. rewrite andb_true_r. rewrite eq_TypeName_symm. rewrite andb_diag...
      }
      match goal with [|- ?lhs1' ++ _ = _] => set (lhs1:=lhs1') end.
      rewrite filter_ext with (g:=(fun x : ScopedName * list TypeName * TypeName =>
        eq_TypeName (fst (unscope (fst (fst x)))) (fst (fst x0)) &&
        match fst (fst x) with local _ => true | global _ => false end)).
      2:{ intros. destruct a. destruct p0. destruct s.
       - simpl. rewrite andb_true_r. rewrite eq_TypeName_symm. rewrite andb_diag...
       - simpl. rewrite andb_false_r...
      }
      unfold lhs1. clear lhs1. repeat rewrite <- filter_compose.
      unfold global_before_local_dtors in GL.
      match goal with [|- _ = _ _ (_ _ (_ ?f' _))] => erewrite filter_ext with (f:=f') end;
        [rewrite <- (GL (fst (fst x0)))|].
      2:{ intros. destruct a. destruct p0... }
      clear GL. rewrite map_map. rewrite map_app.
      f_equal.
      -- unfold cfunsigs_filterfun_g.
         match goal with [|- _ = ?l''] => remember l'' as l' end.
         assert (Aux: Forall (fun x => is_global x) l').
         { rewrite Forall_forall. intros. subst l'.
           rewrite in_map_iff in H. do 2 destruct H. rewrite filter_In in H0. destruct H0.
           destruct x1. destruct p0. destruct s; try discriminate. cbn in H. subst. constructor.
         }
         rewrite <- map_map. rewrite <- map_map with (g:=unscope).
         assert (Aux': l' = map global (map unscope l')).
         { clear - Aux. induction l'... cbn. inversion Aux; subst. rewrite <- IHl'... f_equal.
           inversion H1; subst...
         }
         rewrite Aux'. f_equal. f_equal. subst. clear. f_equal. rewrite filter_compose. apply filter_ext.
         intros. destruct a. destruct p0. cbn. destruct s.
         ++ rewrite andb_false_r...
         ++ cbn. rewrite andb_true_r. apply eq_TypeName_symm.
      -- unfold cfunsigs_filterfun_l.
         match goal with [|- _ = ?l''] => remember l'' as l' end.
         assert (Aux: Forall (fun x => is_local x) l').
         { rewrite Forall_forall. intros. subst l'.
           rewrite in_map_iff in H. do 2 destruct H. rewrite filter_In in H0. destruct H0.
           destruct x1. destruct p0. destruct s; try discriminate. cbn in H. subst. constructor.
         }
         rewrite <- map_map. rewrite <- map_map with (g:=unscope).
         assert (Aux': l' = map local (map unscope l')).
         { clear - Aux. induction l'... cbn. inversion Aux; subst. rewrite <- IHl'... f_equal.
           inversion H1; subst...
         }
         rewrite Aux'. f_equal. f_equal. subst. clear. f_equal. rewrite filter_compose. apply filter_ext.
         intros. destruct a. destruct p0. cbn. destruct s.
         ++ cbn. rewrite andb_true_r. apply eq_TypeName_symm.
         ++ rewrite andb_false_r...
  + unfold lhs. clear lhs. rewrite <- filter_app.
    match goal with [|- map _ (filter ?f' ?lhs1') = _] =>
      set (lhs1:=lhs1'); set (f:=f')
    end.
    assert (Flt: filter f lhs1 = lhs1).
    { clear. assert (H: exists l, l ++ lhs1 = lhs1). { exists []... }
      generalize H. generalize lhs1 at - 2. clear H. induction lhs0; intros...
      simpl. rewrite IHlhs0. 2:{ destruct H. exists (x++[a]). rewrite <- app_assoc... }
      assert (H0: f a = true); try rewrite H0...
      assert (In a lhs1).
      - destruct H. rewrite <- H. apply in_or_app. right. apply in_eq.
      - clear - H0. unfold lhs1 in H0. clear lhs1. apply in_app_or in H0. destruct H0.
        + rewrite map_map in H. rewrite in_map_iff in H. do 2 destruct H. simpl in H.
          unfold f. subst a. simpl. rewrite filter_In in H0. destruct H0 as [_ H0].
          unfold cfunsigs_filterfun_g in H0. destruct x. destruct p0. destruct s; try discriminate.
          rewrite eq_TypeName_symm...
        + rewrite map_map in H. rewrite in_map_iff in H. do 2 destruct H. simpl in H.
          unfold f. subst a. simpl. rewrite filter_In in H0. destruct H0 as [_ H0].
          unfold cfunsigs_filterfun_g in H0. destruct x. destruct p0. destruct s; try discriminate.
          rewrite eq_TypeName_symm...
    }
    rewrite Flt. unfold lhs1. clear Flt f lhs1.
    rewrite map_app. repeat rewrite map_map. simpl.

    remember rhs3 as rhs3InEq. unfold rhs3 in *.
    repeat rewrite map_map in Heqrhs3InEq. simpl in Heqrhs3InEq.
    erewrite map_ext in Heqrhs3InEq.
    2:{ intros. rewrite map_map. simpl. reflexivity. }

    remember rhs2 as rhs2InEq. unfold rhs2 in *.
    repeat rewrite map_map in Heqrhs2InEq. simpl in Heqrhs2InEq.
    rewrite map_ext with (g:=fst) in Heqrhs2InEq...

    erewrite map_ext.
    2:{ intros. rewrite <- map_app. reflexivity. }
    match goal with [|- _ ++ map ?f' _ = _] => erewrite map_ext with (f:=f') end.
    2:{ intros. rewrite <- map_app. reflexivity. }

    subst rhs3InEq. subst rhs2InEq. evar (sn : ScopedName). erewrite transpose_gfbods with (d:=(sn,E_Constr sn []))...
    2:{ clear - H GL. pose proof (in_eq p0 l). rewrite <- H in H0. clear H. rewrite filter_app in H0.
      rewrite in_map_iff in H0. destruct H0. destruct H. apply in_app_or in H0. destruct H0.
      - pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
        rewrite Forall_forall in TypG. rewrite filter_In in H0. destruct H0. rewrite in_map_iff in H0.
        do 2 destruct H0. apply TypG in H2. destruct H2 as [qn [args [LookupSig Typ]]].
        inversion Typ; subst. cbn. rewrite map_map. rewrite map_length.
        apply listTypeDeriv'_lemma in H11. rewrite Nat.eqb_eq in H11.
        repeat rewrite map_length in H11. unfold QName in *. unfold gfun_bod in *. rewrite <- H11.
        unfold lookup_dtors in H9.
        case_eq (filter (eq_TypeName (fst (fst x0))) (skeleton_cdts (program_skeleton p))); intros;
          rewrite H in H9; try discriminate.
        inversion H9; subst.
        evar (g1 : (ScopedName * list TypeName * TypeName) -> bool).
        rewrite filter_ext with (f:=cfunsigs_filterfun_g tn)(g:=g1).
        { evar (g2 : (ScopedName * list TypeName * TypeName) -> bool).
          rewrite filter_ext with (f:=cfunsigs_filterfun_l tn)(g:=g2).
          - unfold g1. evar (g1_1 : (ScopedName * list TypeName * TypeName) -> bool).
            evar (g1_2 : (ScopedName * list TypeName * TypeName) -> bool).
            rewrite <- filter_compose with (f:=g1_1)(g:=g1_2).
            unfold g2. evar (g2_1 : (ScopedName * list TypeName * TypeName) -> bool).
            evar (g2_2 : (ScopedName * list TypeName * TypeName) -> bool).
            rewrite <- filter_compose with (f:=g2_1)(g:=g2_2).
            unfold g1_1. unfold g2_1. rewrite <- filter_app.
            unfold g1_2.
            instantiate (1:=fun x => match fst (fst x) with global _ => true | _ => false end).
            unfold g2_2.
            instantiate (1:=fun x => match fst (fst x) with local _ => true | _ => false end).
            match goal with [|- _ (_ ?f _) = _] => instantiate (1:=f) end.
            unfold global_before_local_dtors in GL. f_equal. rewrite filter_app.
            do 2 rewrite filter_compose. erewrite filter_ext; [ rewrite <- (GL (fst (fst x0))) |].
            { f_equal; erewrite filter_ext; [reflexivity| | reflexivity |].
              { intros. unfold cfunsigs_filterfun_g. destruct a. destruct p0. destruct s; cbn.
                - rewrite andb_false_r...
                - rewrite andb_true_r. rewrite eq_TypeName_symm...
              }
              { intros. unfold cfunsigs_filterfun_g. destruct a. destruct p0. destruct s; cbn.
                - rewrite andb_true_r. rewrite eq_TypeName_symm...
                - rewrite andb_false_r...
              }
            }
            intros. destruct a. destruct p0...
          - unfold g2. intros. unfold cfunsigs_filterfun_l. destruct a. destruct p0.
            rewrite eq_TypeName_eq in H1. subst tn. destruct s.
            + cbn. rewrite andb_true_r. apply eq_TypeName_symm.
            + cbn. rewrite andb_false_r...
        }
        intros. unfold g1. unfold cfunsigs_filterfun_g. destruct a. destruct p0.
        rewrite eq_TypeName_eq in H1. subst tn. destruct s.
        + cbn. rewrite andb_false_r...
        + cbn. rewrite andb_true_r. apply eq_TypeName_symm.
      - pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
        rewrite Forall_forall in TypL. rewrite filter_In in H0. destruct H0. rewrite in_map_iff in H0.
        do 2 destruct H0. apply TypL in H2. destruct H2 as [qn [args [LookupSig Typ]]].
        inversion Typ; subst. cbn. rewrite map_map. rewrite map_length.
        apply listTypeDeriv'_lemma in H11. rewrite Nat.eqb_eq in H11.
        repeat rewrite map_length in H11. unfold QName in *. unfold gfun_bod in *. rewrite <- H11.
        unfold lookup_dtors in H9.
        case_eq (filter (eq_TypeName (fst (fst x0))) (skeleton_cdts (program_skeleton p))); intros;
          rewrite H in H9; try discriminate.
        inversion H9; subst.
        evar (g1 : (ScopedName * list TypeName * TypeName) -> bool).
        rewrite filter_ext with (f:=cfunsigs_filterfun_g tn)(g:=g1).
        { evar (g2 : (ScopedName * list TypeName * TypeName) -> bool).
          rewrite filter_ext with (f:=cfunsigs_filterfun_l tn)(g:=g2).
          - unfold g1. evar (g1_1 : (ScopedName * list TypeName * TypeName) -> bool).
            evar (g1_2 : (ScopedName * list TypeName * TypeName) -> bool).
            rewrite <- filter_compose with (f:=g1_1)(g:=g1_2).
            unfold g2. evar (g2_1 : (ScopedName * list TypeName * TypeName) -> bool).
            evar (g2_2 : (ScopedName * list TypeName * TypeName) -> bool).
            rewrite <- filter_compose with (f:=g2_1)(g:=g2_2).
            unfold g1_1. unfold g2_1. rewrite <- filter_app.
            unfold g1_2.
            instantiate (1:=fun x => match fst (fst x) with global _ => true | _ => false end).
            unfold g2_2.
            instantiate (1:=fun x => match fst (fst x) with local _ => true | _ => false end).
            match goal with [|- _ (_ ?f _) = _] => instantiate (1:=f) end.
            unfold global_before_local_dtors in GL. f_equal. rewrite filter_app.
            do 2 rewrite filter_compose. erewrite filter_ext; [ rewrite <- (GL (fst (fst x0))) |].
            { f_equal; erewrite filter_ext; [reflexivity| | reflexivity |].
              { intros. unfold cfunsigs_filterfun_g. destruct a. destruct p0. destruct s; cbn.
                - rewrite andb_false_r...
                - rewrite andb_true_r. rewrite eq_TypeName_symm...
              }
              { intros. unfold cfunsigs_filterfun_g. destruct a. destruct p0. destruct s; cbn.
                - rewrite andb_true_r. rewrite eq_TypeName_symm...
                - rewrite andb_false_r...
              }
            }
            intros. destruct a. destruct p0...
          - unfold g2. intros. unfold cfunsigs_filterfun_l. destruct a. destruct p0.
            rewrite eq_TypeName_eq in H1. subst tn. destruct s.
            + cbn. rewrite andb_true_r. apply eq_TypeName_symm.
            + cbn. rewrite andb_false_r...
        }
        intros. unfold g1. unfold cfunsigs_filterfun_g. destruct a. destruct p0.
        rewrite eq_TypeName_eq in H1. subst tn. destruct s.
        + cbn. rewrite andb_false_r...
        + cbn. rewrite andb_true_r. apply eq_TypeName_symm.
    }
    rewrite map_app. f_equal.
    * repeat rewrite map_map. apply map_ext_in. intros.
      unfold DefuncIII.globalize_aux. unfold DefuncIII.localize_aux.
      match goal with [|- ?lhs' = _] => set (lhs:=lhs') end.
      rewrite combine_fst_snd with (ps:=lhs).
      clear p0 l H. rename H0 into H.
      f_equal.
      -- unfold lhs. rewrite map_map. simpl. rewrite map_app. repeat rewrite map_map. simpl.
         erewrite filter_ext with (f:=fun x => eq_TypeName (fst (unscope (fst x))) tn).
         ++ rewrite filter_map. rewrite map_app. repeat rewrite map_map. simpl.
            rewrite filter_app.

            erewrite gfun_bods_g_map_filter.
            2:{ rewrite filter_In in H. destruct H... }
            2:{ rewrite filter_In in H. destruct H as [_ H]. unfold cfunsigs_filterfun_g in H.
                destruct a. destruct p0. destruct s; try discriminate. apply Is_global_global.
            }
            erewrite gfun_bods_l_map_filter.
            2:{ rewrite filter_In in H. destruct H... }
            2:{ rewrite filter_In in H. destruct H as [_ H]. unfold cfunsigs_filterfun_g in H.
                destruct a. destruct p0. destruct s; try discriminate. apply Is_global_global.
            }
            repeat rewrite map_map. simpl. f_equal.
            ** generalize (program_gfun_bods_g p). induction g...
               simpl. case_eq (eq_TypeName (fst (unscope (fst (fst a)))) (fst (fst a0))); intros.
               --- unfold QName in *. rewrite H0. simpl.
                   instantiate (1:=fun x => eq_TypeName (fst (unscope (fst (fst a)))) (fst (unscope x))).
                   simpl. rewrite H0. f_equal...
               --- simpl. unfold QName in *. rewrite H0...
            ** generalize (program_gfun_bods_l p). induction g...
               simpl. case_eq (eq_TypeName (fst (unscope (fst (fst a)))) (fst (fst a0))); intros.
               --- unfold QName in *. rewrite H0. simpl. f_equal...
               --- simpl. unfold QName in *. rewrite H0...
         ++ intros. simpl. rewrite eq_TypeName_symm.
            clear - H. rewrite filter_In in H. destruct H as [_ H].
            unfold cfunsigs_filterfun_g in H. destruct a. destruct p0. destruct s; try discriminate. simpl.
            rewrite eq_TypeName_eq in H. subst tn...
      -- unfold lhs. erewrite gfun_bods_g_map_filter with (d:=(sn,E_Constr sn []))...
         2:{ apply filter_In in H. destruct H... }
         2:{ apply filter_In in H. destruct H. unfold cfunsigs_filterfun_g in H0. destruct a. destruct p0.
             destruct s; try discriminate. constructor.
         }
         rewrite map_map. simpl. repeat rewrite map_map. simpl.
         erewrite gfun_bods_l_map_filter with (d:=(sn,E_Constr sn []))...
         2:{ apply filter_In in H. destruct H... }
         2:{ apply filter_In in H. destruct H. unfold cfunsigs_filterfun_g in H0. destruct a. destruct p0.
             destruct s; try discriminate. constructor.
         }
         rewrite map_map. simpl. rewrite filter_app. repeat rewrite map_app. f_equal.
         ++ rewrite map_map. simpl.

            apply filter_In in H. destruct H. unfold cfunsigs_filterfun_g in H0. destruct a. destruct p0.
            destruct s; try discriminate. rewrite eq_TypeName_eq in H0. simpl. subst tn.

            erewrite filter_ext.
            2:{ intros. rewrite eq_TypeName_symm. reflexivity. }

            rewrite <- filter_map. simpl. rewrite map_map. simpl.
            apply map_ext. intros. generalize (snd a). induction g.
            ** simpl. unfold DefuncIII.switch_indices_aux. unfold switch_indices.
               destruct (lookup_gfun_sig_scoped (program_skeleton p) (global (fst a)))...
            ** simpl. unfold defunc_term_helper. destruct a0. simpl. destruct s.
               --- rewrite IHg...
               --- case_eq (eq_QName q q0); intros...
                   simpl. rewrite eq_QName_eq in H0. subst.
                   change (global q0) with (fst (fst (global q0, l, t))).
                   rewrite in_dtors_lookup_dtor...
         ++ rewrite map_map. simpl.

            apply filter_In in H. destruct H. unfold cfunsigs_filterfun_g in H0. destruct a. destruct p0.
            destruct s; try discriminate. rewrite eq_TypeName_eq in H0. simpl. subst tn.

            erewrite filter_ext.
            2:{ intros. rewrite eq_TypeName_symm. reflexivity. }

            rewrite <- filter_map. simpl. rewrite map_map. simpl.
            apply map_ext. intros. generalize (snd a). induction g.
            ** simpl. unfold DefuncIII.switch_indices_aux. unfold switch_indices.
               destruct (lookup_gfun_sig_scoped (program_skeleton p) (local (fst a)))...
            ** simpl. unfold defunc_term_helper. destruct a0. simpl. destruct s.
               --- rewrite IHg...
               --- case_eq (eq_QName q q0); intros...
                   simpl. rewrite eq_QName_eq in H0. subst.
                   change (global q0) with (fst (fst (global q0, l, t))).
                   rewrite in_dtors_lookup_dtor...
    * repeat rewrite map_map. apply map_ext_in. intros.
      unfold DefuncIII.globalize_aux. unfold DefuncIII.localize_aux.
      match goal with [|- ?lhs' = _] => set (lhs:=lhs') end.
      rewrite combine_fst_snd with (ps:=lhs).
      clear p0 l H. rename H0 into H.
      f_equal.
      -- unfold lhs. rewrite map_map. simpl. rewrite map_app. repeat rewrite map_map. simpl.
         erewrite filter_ext with (f:=fun x => eq_TypeName (fst (unscope (fst x))) tn).
         ++ rewrite filter_map. rewrite map_app. repeat rewrite map_map. simpl.
            rewrite filter_app.

            erewrite gfun_bods_g_map_filter_l.
            2:{ rewrite filter_In in H. destruct H... }
            2:{ rewrite filter_In in H. destruct H as [_ H]. unfold cfunsigs_filterfun_l in H.
                destruct a. destruct p0. destruct s; try discriminate. apply Is_local_local.
            }
            erewrite gfun_bods_l_map_filter_l.
            2:{ rewrite filter_In in H. destruct H... }
            2:{ rewrite filter_In in H. destruct H as [_ H]. unfold cfunsigs_filterfun_l in H.
                destruct a. destruct p0. destruct s; try discriminate. apply Is_local_local.
            }
            repeat rewrite map_map. simpl. f_equal.
            ** generalize (program_gfun_bods_g p). induction g...
               simpl. case_eq (eq_TypeName (fst (unscope (fst (fst a)))) (fst (fst a0))); intros.
               --- unfold QName in *. rewrite H0. simpl.
                   instantiate (1:=fun x => eq_TypeName (fst (unscope (fst (fst a)))) (fst (unscope x))).
                   simpl. rewrite H0. f_equal...
               --- simpl. unfold QName in *. rewrite H0...
            ** generalize (program_gfun_bods_l p). induction g...
               simpl. case_eq (eq_TypeName (fst (unscope (fst (fst a)))) (fst (fst a0))); intros.
               --- unfold QName in *. rewrite H0. simpl. f_equal...
               --- simpl. unfold QName in *. rewrite H0...
         ++ intros. simpl. rewrite eq_TypeName_symm.
            clear - H. rewrite filter_In in H. destruct H as [_ H].
            unfold cfunsigs_filterfun_l in H. destruct a. destruct p0. destruct s; try discriminate. simpl.
            rewrite eq_TypeName_eq in H. subst tn...
      -- unfold lhs. erewrite gfun_bods_g_map_filter_l with (d:=(sn,E_Constr sn []))...
         2:{ apply filter_In in H. destruct H... }
         2:{ apply filter_In in H. destruct H. unfold cfunsigs_filterfun_l in H0. destruct a. destruct p0.
             destruct s; try discriminate. constructor.
         }
         rewrite map_map. simpl. repeat rewrite map_map. simpl.
         erewrite gfun_bods_l_map_filter_l with (d:=(sn,E_Constr sn []))...
         2:{ apply filter_In in H. destruct H... }
         2:{ apply filter_In in H. destruct H. unfold cfunsigs_filterfun_l in H0. destruct a. destruct p0.
             destruct s; try discriminate. constructor.
         }
         rewrite map_map. simpl. rewrite filter_app. repeat rewrite map_app. f_equal.
         ++ rewrite map_map. simpl.

            apply filter_In in H. destruct H. unfold cfunsigs_filterfun_l in H0. destruct a. destruct p0.
            destruct s; try discriminate. rewrite eq_TypeName_eq in H0. simpl. subst tn.

            erewrite filter_ext.
            2:{ intros. rewrite eq_TypeName_symm. reflexivity. }

            rewrite <- filter_map. simpl. rewrite map_map. simpl.
            apply map_ext. intros. generalize (snd a). induction g.
            ** simpl. unfold DefuncIII.switch_indices_aux. unfold switch_indices.
               destruct (lookup_gfun_sig_scoped (program_skeleton p) (global (fst a)))...
            ** simpl. unfold defunc_term_helper. destruct a0. simpl. destruct s.
               --- case_eq (eq_QName q q0); intros...
                   simpl. rewrite eq_QName_eq in H0. subst.
                   change (local q0) with (fst (fst (local q0, l, t))).
                   rewrite in_dtors_lookup_dtor...
               --- rewrite IHg...

         ++ rewrite map_map. simpl.

            apply filter_In in H. destruct H. unfold cfunsigs_filterfun_l in H0. destruct a. destruct p0.
            destruct s; try discriminate. rewrite eq_TypeName_eq in H0. simpl. subst tn.

            erewrite filter_ext.
            2:{ intros. rewrite eq_TypeName_symm. reflexivity. }

            rewrite <- filter_map. simpl. rewrite map_map. simpl.
            apply map_ext. intros. generalize (snd a). induction g.
            ** simpl. unfold DefuncIII.switch_indices_aux. unfold switch_indices.
               destruct (lookup_gfun_sig_scoped (program_skeleton p) (local (fst a)))...
            ** simpl. unfold defunc_term_helper. destruct a0. simpl. destruct s.
               --- case_eq (eq_QName q q0); intros...
                   simpl. rewrite eq_QName_eq in H0. subst.
                   change (local q0) with (fst (fst (local q0, l, t))).
                   rewrite in_dtors_lookup_dtor...
               --- rewrite IHg...
Unshelve. all:repeat constructor.
Qed.

Lemma same_dtors : forall (p : program) (tn : TypeName) (gfd1 gfd2 : list ScopedName),
  In gfd1 (map (map fst) (map snd (program_gfun_bods_for_type tn p))) ->
  In gfd2 (map (map fst) (map snd (program_gfun_bods_for_type tn p))) ->
  gfd1 = gfd2.
Proof with eauto.
intros. rewrite in_map_iff in *. do 2 destruct H. do 2 destruct H0. subst.
rewrite in_map_iff in *. destruct H1. destruct H. destruct H2. destruct H1. subst.
unfold program_gfun_bods_for_type in *. rewrite filter_In in *.
destruct H0. destruct H2. apply in_app_or in H. apply in_app_or in H1.
pose proof (program_gfun_bods_typecheck_g p) as TypG. unfold gfun_bods_g_typecheck in TypG.
rewrite Forall_forall in TypG.
pose proof (program_gfun_bods_typecheck_l p) as TypL. unfold gfun_bods_l_typecheck in TypL.
rewrite Forall_forall in TypL;
destruct H; destruct H1;
  rewrite in_map_iff in *; do 2 destruct H; do 2 destruct H1; destruct x1; destruct x2;
  inversion H; subst; inversion H1; subst; cbn in *;
  try apply TypG in H3; try apply TypG in H4; try apply TypL in H3; try apply TypL in H4;
  rename H0 into tnEq1; rename H2 into tnEq2;
  clear - H3 H4 tnEq1 tnEq2;
  destruct H3 as [qn1 [args1 [_ Typ1]]]; destruct H4 as [qn2 [args2 [_ Typ2]]];
  inversion Typ1; subst; inversion Typ2; subst; rewrite eq_TypeName_eq in *;
  unfold gfun_bod in *; rewrite tnEq1 in H6; rewrite tnEq2 in H11;
  rewrite H11 in H6; inversion H6; subst;
  pose proof (listTypeDeriv'_lemma _ _ _ _ H8) as Len1;
  pose proof (listTypeDeriv'_lemma _ _ _ _ H13) as Len2;
  clear - H7 H12 Len1 Len2; rewrite Nat.eqb_eq in *; repeat rewrite map_length in *;
  generalize dependent dtorlist; generalize dependent (snd x); generalize dependent (snd x0);
  clear; induction l; intros;
    try solve [ rewrite Len1 in Len2; destruct l; eauto; discriminate ];
    try solve [
      rewrite Len1 in Len2; destruct l0; try discriminate; cbn;
      destruct dtorlist; try discriminate; cbn in *;
      inversion H7; subst; inversion H12; subst; destruct p; destruct a; destruct p0; destruct p;
      subst; f_equal; eapply IHl; eauto; omega
    ].
Qed.

Lemma firstn_combine : forall {A B} (l1 : list A) (l2 : list B) n,
  firstn n (combine l1 l2) = combine (firstn n l1) (firstn n l2).
Proof with eauto.
intros. generalize dependent l2. generalize dependent n. induction l1; intros.
- cbn. repeat rewrite firstn_nil...
- destruct n... destruct l2... cbn. f_equal...
Qed.

Lemma defunc_is_matrix_transpose' : forall p tn P1 P2 P3 P4 P5 pr
  (GL : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (Nonempty : program_gfun_bods_for_type tn p <> []),
  pr = defunctionalize_program p tn P1 P2 P3 P4 P5 ->
  program_cfun_bods_for_type tn pr =
    map (fun x => (fst x, map (fun y => (fst y, defunc_term_helper (program_skeleton p) tn (fst x) (fst y) (snd y))) (snd x)))
      (read_cfuns_from_matrix (transpose_matrix (read_gfuns_into_matrix
        (program_gfun_bods_for_type tn p)))).
Proof with eauto.
intros. erewrite defunc_is_matrix_transpose... clear.
remember (program_gfun_bods_for_type tn p) as l. intros. cbn.
rewrite map_map. cbn. destruct l...
repeat rewrite map_map. cbn [snd]. cbn [map]. cbn [snd].
rewrite map_map. cbn [fst]. rewrite map_map. cbn [snd].
change (fun x : ScopedName * list (ScopedName * expr) => fst x) with (@fst ScopedName (list (ScopedName * expr))).
erewrite map_ext with (f:=fun x => map snd _).
2:{ intros. rewrite map_map. cbn. reflexivity. }
change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr).
rewrite <- map_map with (f:=snd). unfold gfun_bod in *.
replace (map snd (snd p0) :: map (map snd) (map snd l)) with
  (map (map snd) (snd p0 :: map snd l))...
replace (snd p0 :: map snd l) with (map snd (p0::l))...
generalize (length (map fst (snd p0))). intros.
replace (fst p0 :: map fst l) with (map fst (p0::l))...
remember (map fst (snd p0)) as l0.
match goal with [|- _ (_ _ (_ ((map ?f' (snd p0)) :: map ?f ?l) _)) = _] =>
  replace (map f' (snd p0) :: map f l) with (map f (p0::l)) end...
remember (p0::l) as l1.
assert (exists l', l'++l1 = p0::l /\ l'++l1 = program_gfun_bods_for_type tn p).
{ exists []... }
clear Heql1 Heql. rename H into Heql1.
clear - Heql0 Heql1.
generalize (defunc_term_helper (program_skeleton p) tn) as f. intros.
pose proof (eq_refl (length l1)). generalize dependent H. generalize dependent Heql1.
generalize (length l1) at 2. intros. generalize dependent l1.
induction n0; intros...
- destruct l1; try discriminate. cbn. clear.
  generalize dependent n. induction l0... destruct n... cbn. f_equal...
- destruct l1; try discriminate. cbn [map]. cbn [transpose].
  case_eq (snd p1); intros.
  + cbn. destruct l0...
  + cbn [map]. repeat rewrite map_with_index_map. repeat rewrite with_index_map_map.
    cbn [combine].
    match goal with [|- _ _ (_ (fun n1 x => ?lhs :: (?rhs x)) _) = _] =>
      change (fun n1 x => lhs :: (rhs x)) with (fun n x => (fun n1 y1 => lhs :: y1) n ((fun (_:nat) y2 => rhs y2) n x))
    end.
    rewrite <- with_index_map_map. repeat rewrite <- map_with_index_map.
    rewrite <- map_with_index_snd_f_combine. rewrite IHn0...
    2:{ destruct Heql1. exists (x++[p1]). rewrite <- app_assoc... }
    rewrite map_map.
    match goal with [|- _ _ (_ _ (_ _ (_ _ ?t))) = _] => generalize t end.
    clear - H0 Heql0 Heql1 H. rename H into Len. intros.
    repeat rewrite map_with_index_map. rewrite with_index_map_map. cbn - [nth].
    match goal with [|- _ = _ _ (_ _ (_ ?f' _))] =>
      rewrite <- map_with_index_snd_f_combine with (f0:=f')
    end.
    rewrite <- map_with_index_snd_f_combine. repeat rewrite with_index_map_map.
    apply map_with_index_ext_in. intros. cbn - [nth]. f_equal. f_equal. f_equal.
    repeat rewrite <- map_with_index_map.
    destruct p2. cbn - [nth].
    match goal with [|- _ _ (f s (fst p1) e :: (map ?f' l2)) _ = _] =>
      replace (f s (fst p1) e :: map f' l2) with (map f' ((s,e)::l2)) end...
    set (f':=fun x => f (fst x) (fst p1) (snd x)).
    replace (f s (fst p1) e) with (f' (s,e))...
    replace (f (fst a) (fst p1) (nth n (e :: map snd l2) e)) with
      (f' (fst a, nth n (e :: map snd l2) e))...
    replace e with (snd (s,e)) at 3 4...
    replace (snd (s, e) :: map snd l2) with (map snd ((s,e)::l2))...
    rewrite map_nth. rewrite map_nth.
    assert (fst a = fst (nth n ((s, e) :: l2) (s, e))).
    { assert (fst a = nth n l0 s).
      { symmetry in H1. pose proof H1 as H1'.
        apply nth_error_nth with (d:=(s,[e])) in H1. subst.
        assert (n < length (combine (map fst (snd p0)) l3)).
        { apply nth_error_Some. unfold not. intros. rewrite H1 in H1'. discriminate. }
        rewrite <- firstn_skipn with (l:=combine (map fst (snd p0)) l3)
         (n:=Nat.min (length (snd p0)) (length l3)).
        rewrite <- map_nth with (f:=fst). rewrite combine_length in H1.
        rewrite map_length in H1. rewrite map_app. rewrite app_nth1...
        2:{ rewrite map_length. rewrite firstn_length. rewrite combine_length.
          rewrite map_length. rewrite Nat.min_id... }
        rewrite firstn_combine. rewrite map_fst_combine.
        2:{ repeat rewrite firstn_length. rewrite Nat.min_comm. rewrite Nat.min_assoc.
          rewrite map_length. rewrite Nat.min_id. rewrite <- Nat.min_assoc.
          rewrite Nat.min_id... }
        rewrite <- firstn_skipn with (l:=map fst (snd p0))
          (n:=Nat.min (length (snd p0)) (length l3)) at 2.
        rewrite app_nth1... rewrite firstn_length.
        rewrite Nat.min_comm. rewrite Nat.min_assoc.
        rewrite map_length. rewrite Nat.min_id...
      }
      rewrite H2. rewrite <- H0. subst l0. replace s with (fst (s,e))...
      rewrite map_nth... cbn. rewrite <- map_nth.
      rewrite <- map_nth with (f:=fst). f_equal.
      destruct Heql1. destruct H3. pose proof (in_eq p0 l).
      rewrite <- H3 in H5. rewrite H4 in H5.
      assert (In p1 (program_gfun_bods_for_type tn p)).
      { rewrite <- H4. apply in_or_app. right. left... }
      clear - H5 H6. apply (in_map snd) in H5. apply (in_map snd) in H6.
      apply (in_map (map fst)) in H5. apply (in_map (map fst)) in H6.
      eapply same_dtors...
    }
    rewrite H2. rewrite <- surjective_pairing...
Qed.

Lemma refunc_is_matrix_transpose' : forall p tn P1 P2 P3 P4 P5 pr
  (GL : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (Nonempty : program_cfun_bods_for_type tn p <> []),
  pr = refunctionalize_program p tn P1 P2 P3 P4 P5 ->
  program_gfun_bods_for_type tn pr =
    read_gfuns_from_matrix (transpose_matrix (read_cfuns_into_matrix
      (map (fun x => (fst x, map (fun y => (fst y, refunc_term_helper (program_skeleton p) tn (fst x) (fst y) (snd y))) (snd x)))
        (program_cfun_bods_for_type tn p)))).
Proof with eauto.
intros. subst. unfold program_gfun_bods_for_type. simpl. clear - GL Nonempty.
unfold RefuncIII.new_gfun_bods_g. unfold RefuncIII.new_gfun_bods_l.
rewrite map_app. rewrite map_app. repeat rewrite filter_app.
match goal with [|- (_ ++ ?l1) ++ (_ ++ ?l2) = _] => assert (l1 = [] /\ l2 = []) end.
- pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
  unfold dts_cdts_disjoint in Disj.
  clear GL. split.
  + match goal with [|- ?l = _] => case_eq l; intros end...
    exfalso. apply Nonempty. clear Nonempty. pose proof (program_has_all_gfun_bods_g p) as HasSigs.
    pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)) as SigsCdts.
    unfold has_all_gfun_bods in HasSigs. unfold gfun_sigs_in_cdts in SigsCdts.
    case_eq (program_cfun_bods_for_type tn p); intros... exfalso.
    unfold program_cfun_bods_for_type in H0.
    rewrite combine_fst_snd with (ps:=map _ _) in H. repeat rewrite map_map in H. simpl in H.
    rewrite <- map_map in H. unfold gfun_bod in *. rewrite <- HasSigs in H.
    pose proof (in_eq p0 l) as p0In. rewrite <- H in p0In.
    rewrite filter_In in p0In. destruct p0In as [p0In p0Eq]. destruct p0. apply in_combine_l in p0In.
    rename p0In into sIn. simpl in p0Eq. rename p0Eq into sEq.
    rewrite Forall_forall in SigsCdts. rewrite map_map in sIn. rewrite in_map_iff in sIn.
    destruct sIn as [x [xEq xIn]]. apply SigsCdts in xIn.
    pose proof (in_eq p1 l0) as p1In. rewrite <- H0 in p1In.
    rewrite filter_In in p1In. destruct p1In as [p1In p1Eq]. apply in_app_or in p1In. destruct p1In.
    * clear - xEq xIn sEq H1 p1Eq Disj. pose proof (program_has_all_cfun_bods_g p) as HasSigs.
      pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as SigsDts.
      unfold has_all_cfun_bods in HasSigs. unfold cfun_sigs_in_dts in SigsDts.
      destruct p1. rewrite in_map_iff in H1. destruct H1 as [x' [x'Eq x'In]].
      rewrite Forall_forall in SigsDts. destruct x'. inversion x'Eq; subst.
      eapply (in_map fst) in x'In. rewrite <- HasSigs in x'In. rewrite in_map_iff in x'In.
      destruct x'In. destruct H. apply SigsDts in H0. simpl in *. rewrite eq_TypeName_eq in *. subst.
      unfold QName in *. rewrite <- p1Eq in xIn. clear - xIn H0 Disj.
      specialize Disj with (t:=fst (fst (fst x0))). apply Disj...
    * clear - xEq xIn sEq H1 p1Eq Disj. pose proof (program_has_all_cfun_bods_l p) as HasSigs.
      pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as SigsDts.
      unfold has_all_cfun_bods in HasSigs. unfold cfun_sigs_in_dts in SigsDts.
      destruct p1. rewrite in_map_iff in H1. destruct H1 as [x' [x'Eq x'In]].
      rewrite Forall_forall in SigsDts. destruct x'. inversion x'Eq; subst.
      eapply (in_map fst) in x'In. rewrite <- HasSigs in x'In. rewrite in_map_iff in x'In.
      destruct x'In. destruct H. apply SigsDts in H0. simpl in *. rewrite eq_TypeName_eq in *. subst.
      unfold QName in *. rewrite <- p1Eq in xIn. clear - xIn H0 Disj.
      specialize Disj with (t:=fst (fst (fst x0))). apply Disj...
  + match goal with [|- ?l = _] => case_eq l; intros end...
    exfalso. apply Nonempty. clear Nonempty. pose proof (program_has_all_gfun_bods_l p) as HasSigs.
    pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)) as SigsCdts.
    unfold has_all_gfun_bods in HasSigs. unfold gfun_sigs_in_cdts in SigsCdts.
    case_eq (program_cfun_bods_for_type tn p); intros... exfalso.
    unfold program_cfun_bods_for_type in H0.
    rewrite combine_fst_snd with (ps:=map _ _) in H. repeat rewrite map_map in H. simpl in H.
    rewrite <- map_map in H. unfold gfun_bod in *. rewrite <- HasSigs in H.
    pose proof (in_eq p0 l) as p0In. rewrite <- H in p0In.
    rewrite filter_In in p0In. destruct p0In as [p0In p0Eq]. destruct p0. apply in_combine_l in p0In.
    rename p0In into sIn. simpl in p0Eq. rename p0Eq into sEq.
    rewrite Forall_forall in SigsCdts. rewrite map_map in sIn. rewrite in_map_iff in sIn.
    destruct sIn as [x [xEq xIn]]. apply SigsCdts in xIn.
    pose proof (in_eq p1 l0) as p1In. rewrite <- H0 in p1In.
    rewrite filter_In in p1In. destruct p1In as [p1In p1Eq]. apply in_app_or in p1In. destruct p1In.
    * clear - xEq xIn sEq H1 p1Eq Disj. pose proof (program_has_all_cfun_bods_g p) as HasSigs.
      pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)) as SigsDts.
      unfold has_all_cfun_bods in HasSigs. unfold cfun_sigs_in_dts in SigsDts.
      destruct p1. rewrite in_map_iff in H1. destruct H1 as [x' [x'Eq x'In]].
      rewrite Forall_forall in SigsDts. destruct x'. inversion x'Eq; subst.
      eapply (in_map fst) in x'In. rewrite <- HasSigs in x'In. rewrite in_map_iff in x'In.
      destruct x'In. destruct H. apply SigsDts in H0. simpl in *. rewrite eq_TypeName_eq in *. subst.
      unfold QName in *. rewrite <- p1Eq in xIn. clear - xIn H0 Disj.
      specialize Disj with (t:=fst (fst (fst x0))). apply Disj...
    * clear - xEq xIn sEq H1 p1Eq Disj. pose proof (program_has_all_cfun_bods_l p) as HasSigs.
      pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)) as SigsDts.
      unfold has_all_cfun_bods in HasSigs. unfold cfun_sigs_in_dts in SigsDts.
      destruct p1. rewrite in_map_iff in H1. destruct H1 as [x' [x'Eq x'In]].
      rewrite Forall_forall in SigsDts. destruct x'. inversion x'Eq; subst.
      eapply (in_map fst) in x'In. rewrite <- HasSigs in x'In. rewrite in_map_iff in x'In.
      destruct x'In. destruct H. apply SigsDts in H0. simpl in *. rewrite eq_TypeName_eq in *. subst.
      unfold QName in *. rewrite <- p1Eq in xIn. clear - xIn H0 Disj.
      specialize Disj with (t:=fst (fst (fst x0))). apply Disj...
- destruct H as [H_1 H_2]. rewrite H_1. rewrite H_2. repeat rewrite app_nil_r. clear H_1 H_2.
  match goal with [|- ?lhs' = _] => set (lhs:=lhs') end.
  unfold program_cfun_bods_for_type.
  unfold read_cfuns_into_matrix.
  match goal with [|- _ = combine ?rhs1' (map ?rhs2' (transpose ?rhs3' ?len'))] =>
    set (rhs1:=rhs1'); set (rhs2:=rhs2'); set (rhs3:=rhs3'); set (len:=len')
  end.
  rewrite combine_fst_snd with (ps:=lhs).
  remember rhs1 as rhs1Eq. unfold rhs1 in Heqrhs1Eq.
  match goal with [_ : _ = match ?m with | [] => [] | l :: _ => map fst (snd l) end |- _] => case_eq m; intros end.
  { unfold program_cfun_bods_for_type in Nonempty. exfalso. apply Nonempty.
    match goal with [|- ?m = []] => destruct m end... discriminate.
  }
  rewrite Heqrhs1Eq. rewrite H.
  clear rhs1 rhs1Eq Heqrhs1Eq. f_equal.
  + unfold lhs. clear - H GL. rewrite map_app.
    repeat (rewrite <- filter_map; rewrite map_map). simpl.
    apply (f_equal (map (fun x => map fst (snd x)))) in H.
    rewrite map_map in H. simpl in H. generalize H. clear H. unfold cfun_bod.
    generalize (snd p0). clear p0. intros.
    match goal with [_ : _ = ?x::?r |- _] => assert (In x (x::r)) end.
    { apply in_eq. }
    rewrite <- H in H0. clear H. rewrite in_map_iff in H0. destruct H0 as [x [H0Eq H0In]].
    inversion H0Eq; subst. rewrite map_map. simpl. clear - H0In GL.
    pose proof (program_cfun_bods_typecheck_g p) as TypG.
    pose proof (program_cfun_bods_typecheck_l p) as TypL.
    rewrite filter_app in H0In. apply in_app_or in H0In. destruct H0In.
    * clear TypL. unfold cfun_bods_g_typecheck in TypG.
      rewrite filter_In in H. destruct H. rewrite in_map_iff in H. do 2 destruct H.
      rewrite Forall_forall in TypG. apply TypG in H1. clear TypG. destruct H1 as [qn [args [t [Lookup Typ]]]].
      rename H0 into TypName. inversion Typ; subst. simpl in *.
      (**)
      clear H9. rename H13 into H9. clear H8. rename H12 into H8.
      (**)
      match goal with [|- _ = ?rhs] => replace rhs with (map fst ctorlist) end.
      2: { generalize H8. generalize H9. generalize ctorlist. generalize (snd x0). clear. induction l; intros.
        - destruct ctorlist... apply listTypeDeriv'_lemma_ctx in H9. rewrite Nat.eqb_eq in H9. discriminate.
        - destruct ctorlist.
          + apply listTypeDeriv'_lemma_ctx in H9. rewrite Nat.eqb_eq in H9. discriminate.
          + simpl. f_equal.
            * simpl in H8. inversion H8. destruct a. destruct p0...
            * inversion H9. inversion H8. rewrite IHl with (ctorlist:=ctorlist)...
      }
      rewrite eq_TypeName_eq in TypName. subst tn.
      (**)
      rename H11 into H7.
      (**)
      clear - H7 GL. unfold lookup_ctors in H7.
      destruct (filter (eq_TypeName (fst (fst x0))) (skeleton_dts (program_skeleton p)));
        try discriminate.
      inversion H7; subst. clear H7.
      repeat rewrite filter_compose. unfold gfunsigs_filterfun_g. unfold gfunsigs_filterfun_l.
      rewrite filter_ext with (g:=(fun x : ScopedName * list TypeName =>
        eq_TypeName (fst (unscope (fst x))) (fst (fst x0)) &&
        match fst x with local _ => false | global _ => true end)).
      2:{ intros. destruct a. destruct s.
       - simpl. rewrite andb_false_r...
       - simpl. rewrite andb_true_r. rewrite eq_TypeName_symm. rewrite andb_diag...
      }
      match goal with [|- ?lhs1' ++ _ = _] => set (lhs1:=lhs1') end.
      rewrite filter_ext with (g:=(fun x : ScopedName * list TypeName =>
        eq_TypeName (fst (unscope (fst x))) (fst (fst x0)) &&
        match fst x with local _ => true | global _ => false end)).
      2:{ intros. destruct a. destruct s.
       - simpl. rewrite andb_true_r. rewrite eq_TypeName_symm. rewrite andb_diag...
       - simpl. rewrite andb_false_r...
      }
      unfold lhs1. clear lhs1. repeat rewrite <- filter_compose.
      unfold global_before_local_ctors in GL.
      match goal with [|- _ = _ _ (_ ?f' _)] => erewrite filter_ext with (f:=f') end;
        [rewrite <- (GL (fst (fst x0)))|].
      2:{ intros. destruct a... }
      clear GL. rewrite map_app.
      f_equal.
      -- unfold gfunsigs_filterfun_g.
         match goal with [|- _ = ?l''] => remember l'' as l' end.
         assert (Aux: Forall (fun x => is_global x) l').
         { rewrite Forall_forall. intros. subst l'.
           rewrite in_map_iff in H. do 2 destruct H. rewrite filter_In in H0. destruct H0.
           destruct x1. destruct s; try discriminate. cbn in H. subst. constructor.
         }
         rewrite <- map_map. rewrite <- map_map with (g:=unscope).
         assert (Aux': l' = map global (map unscope l')).
         { clear - Aux. induction l'... cbn. inversion Aux; subst. rewrite <- IHl'... f_equal.
           inversion H1; subst...
         }
         rewrite Aux'. f_equal. f_equal. subst. clear. f_equal. rewrite filter_compose. apply filter_ext.
         intros. destruct a. cbn. destruct s.
         ++ rewrite andb_false_r...
         ++ cbn. rewrite andb_true_r. apply eq_TypeName_symm.
      -- unfold cfunsigs_filterfun_l.
         match goal with [|- _ = ?l''] => remember l'' as l' end.
         assert (Aux: Forall (fun x => is_local x) l').
         { rewrite Forall_forall. intros. subst l'.
           rewrite in_map_iff in H. do 2 destruct H. rewrite filter_In in H0. destruct H0.
           destruct x1. destruct s; try discriminate. cbn in H. subst. constructor.
         }
         rewrite <- map_map. rewrite <- map_map with (g:=unscope).
         assert (Aux': l' = map local (map unscope l')).
         { clear - Aux. induction l'... cbn. inversion Aux; subst. rewrite <- IHl'... f_equal.
           inversion H1; subst...
         }
         rewrite Aux'. f_equal. f_equal. subst. clear. f_equal. rewrite filter_compose. apply filter_ext.
         intros. destruct a. cbn. destruct s.
         ++ cbn. rewrite andb_true_r. apply eq_TypeName_symm.
         ++ rewrite andb_false_r...
    * clear TypG. unfold cfun_bods_l_typecheck in TypL.
      rewrite filter_In in H. destruct H. rewrite in_map_iff in H. do 2 destruct H.
      rewrite Forall_forall in TypL. apply TypL in H1. clear TypL. destruct H1 as [qn [args [t [Lookup Typ]]]].
      rename H0 into TypName. inversion Typ; subst. simpl in *.
      (**)
      clear H9. rename H13 into H9. clear H8. rename H12 into H8.
      (**)
      match goal with [|- _ = ?rhs] => replace rhs with (map fst ctorlist) end.
      2: { generalize H8. generalize H9. generalize ctorlist. generalize (snd x0). clear. induction l; intros.
        - destruct ctorlist... apply listTypeDeriv'_lemma_ctx in H9. rewrite Nat.eqb_eq in H9. discriminate.
        - destruct ctorlist.
          + apply listTypeDeriv'_lemma_ctx in H9. rewrite Nat.eqb_eq in H9. discriminate.
          + simpl. f_equal.
            * simpl in H8. inversion H8. destruct a. destruct p0...
            * inversion H9. inversion H8. rewrite IHl with (ctorlist:=ctorlist)...
      }
      rewrite eq_TypeName_eq in TypName. subst tn.
      (**)
      rename H11 into H7.
      (**)
      clear - H7 GL. unfold lookup_ctors in H7.
      destruct (filter (eq_TypeName (fst (fst x0))) (skeleton_dts (program_skeleton p)));
        try discriminate.
      inversion H7; subst. clear H7.
      repeat rewrite filter_compose. unfold gfunsigs_filterfun_g. unfold gfunsigs_filterfun_l.
      rewrite filter_ext with (g:=(fun x : ScopedName * list TypeName =>
        eq_TypeName (fst (unscope (fst x))) (fst (fst x0)) &&
        match fst x with local _ => false | global _ => true end)).
      2:{ intros. destruct a. destruct s.
       - simpl. rewrite andb_false_r...
       - simpl. rewrite andb_true_r. rewrite eq_TypeName_symm. rewrite andb_diag...
      }
      match goal with [|- ?lhs1' ++ _ = _] => set (lhs1:=lhs1') end.
      rewrite filter_ext with (g:=(fun x : ScopedName * list TypeName =>
        eq_TypeName (fst (unscope (fst x))) (fst (fst x0)) &&
        match fst x with local _ => true | global _ => false end)).
      2:{ intros. destruct a. destruct s.
       - simpl. rewrite andb_true_r. rewrite eq_TypeName_symm. rewrite andb_diag...
       - simpl. rewrite andb_false_r...
      }
      unfold lhs1. clear lhs1. repeat rewrite <- filter_compose.
      unfold global_before_local_ctors in GL.
      match goal with [|- _ = _ _ (_ ?f' _)] => erewrite filter_ext with (f:=f') end;
        [rewrite <- (GL (fst (fst x0)))|].
      2:{ intros. destruct a... }
      clear GL. rewrite map_app.
      f_equal.
      -- unfold gfunsigs_filterfun_g.
         match goal with [|- _ = ?l''] => remember l'' as l' end.
         assert (Aux: Forall (fun x => is_global x) l').
         { rewrite Forall_forall. intros. subst l'.
           rewrite in_map_iff in H. do 2 destruct H. rewrite filter_In in H0. destruct H0.
           destruct x1. destruct s; try discriminate. cbn in H. subst. constructor.
         }
         rewrite <- map_map. rewrite <- map_map with (g:=unscope).
         assert (Aux': l' = map global (map unscope l')).
         { clear - Aux. induction l'... cbn. inversion Aux; subst. rewrite <- IHl'... f_equal.
           inversion H1; subst...
         }
         rewrite Aux'. f_equal. f_equal. subst. clear. f_equal. rewrite filter_compose. apply filter_ext.
         intros. destruct a. cbn. destruct s.
         ++ rewrite andb_false_r...
         ++ cbn. rewrite andb_true_r. apply eq_TypeName_symm.
      -- unfold cfunsigs_filterfun_l.
         match goal with [|- _ = ?l''] => remember l'' as l' end.
         assert (Aux: Forall (fun x => is_local x) l').
         { rewrite Forall_forall. intros. subst l'.
           rewrite in_map_iff in H. do 2 destruct H. rewrite filter_In in H0. destruct H0.
           destruct x1. destruct s; try discriminate. cbn in H. subst. constructor.
         }
         rewrite <- map_map. rewrite <- map_map with (g:=unscope).
         assert (Aux': l' = map local (map unscope l')).
         { clear - Aux. induction l'... cbn. inversion Aux; subst. rewrite <- IHl'... f_equal.
           inversion H1; subst...
         }
         rewrite Aux'. f_equal. f_equal. subst. clear. f_equal. rewrite filter_compose. apply filter_ext.
         intros. destruct a. cbn. destruct s.
         ++ cbn. rewrite andb_true_r. apply eq_TypeName_symm.
         ++ rewrite andb_false_r...
  + unfold lhs. clear lhs. rewrite <- filter_app.
    match goal with [|- map _ (filter ?f' ?lhs1') = _] =>
      set (lhs1:=lhs1'); set (f:=f')
    end.
    assert (Flt: filter f lhs1 = lhs1).
    { clear. assert (H: exists l, l ++ lhs1 = lhs1). { exists []... }
      generalize H. generalize lhs1 at - 2. clear H. induction lhs0; intros...
      simpl. rewrite IHlhs0. 2:{ destruct H. exists (x++[a]). rewrite <- app_assoc... }
      assert (H0: f a = true); try rewrite H0...
      assert (In a lhs1).
      - destruct H. rewrite <- H. apply in_or_app. right. apply in_eq.
      - clear - H0. unfold lhs1 in H0. clear lhs1. apply in_app_or in H0. destruct H0.
        + rewrite map_map in H. rewrite in_map_iff in H. do 2 destruct H. simpl in H.
          unfold f. subst a. simpl. rewrite filter_In in H0. destruct H0 as [_ H0].
          unfold cfunsigs_filterfun_g in H0. destruct x. destruct s; try discriminate.
          rewrite eq_TypeName_symm...
        + rewrite map_map in H. rewrite in_map_iff in H. do 2 destruct H. simpl in H.
          unfold f. subst a. simpl. rewrite filter_In in H0. destruct H0 as [_ H0].
          unfold cfunsigs_filterfun_g in H0. destruct x. destruct s; try discriminate.
          rewrite eq_TypeName_symm...
    }
    rewrite Flt. unfold lhs1. clear Flt f lhs1.
    rewrite map_app. repeat rewrite map_map. simpl.

    remember rhs3 as rhs3InEq. unfold rhs3 in *.
    repeat rewrite map_map in Heqrhs3InEq. simpl in Heqrhs3InEq.
    erewrite map_ext in Heqrhs3InEq.
    2:{ intros. rewrite map_map. simpl. reflexivity. }

    remember rhs2 as rhs2InEq. unfold rhs2 in *.
    repeat rewrite map_map in Heqrhs2InEq. simpl in Heqrhs2InEq.
    rewrite map_ext with (g:=fst) in Heqrhs2InEq...

    erewrite map_ext.
    2:{ intros. rewrite <- map_app. reflexivity. }
    match goal with [|- _ ++ map ?f' _ = _] => erewrite map_ext with (f:=f') end.
    2:{ intros. rewrite <- map_app. reflexivity. }

    subst rhs3InEq. subst rhs2InEq. evar (sn : ScopedName). erewrite transpose_cfbods with (c:=(sn,E_FunCall (snd (unscope sn)) []))...
    2:{ clear - H GL. pose proof (in_eq p0 l). rewrite <- H in H0. clear H. rewrite filter_app in H0.
      rewrite in_map_iff in H0. destruct H0. destruct H. apply in_app_or in H0. destruct H0.
      - pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
        rewrite Forall_forall in TypG. rewrite filter_In in H0. destruct H0. rewrite in_map_iff in H0.
        do 2 destruct H0. apply TypG in H2. destruct H2 as [qn [args [t [LookupSig Typ]]]].
        inversion Typ; subst. cbn. rewrite map_map. rewrite map_length.
        (**)
        clear H11. rename H15 into H11. rename H13 into H9.
        (**)
        apply listTypeDeriv'_lemma_ctx in H11. rewrite Nat.eqb_eq in H11.
        repeat rewrite map_length in H11. unfold QName in *. unfold cfun_bod in *. rewrite <- H11.
        unfold lookup_ctors in H9.
        case_eq (filter (eq_TypeName (fst (fst x0))) (skeleton_dts (program_skeleton p))); intros;
          rewrite H in H9; try discriminate.
        inversion H9; subst.
        evar (g1 : (ScopedName * list TypeName) -> bool).
        rewrite filter_ext with (f:=gfunsigs_filterfun_g tn)(g:=g1).
        { evar (g2 : (ScopedName * list TypeName) -> bool).
          rewrite filter_ext with (f:=gfunsigs_filterfun_l tn)(g:=g2).
          - unfold g1. evar (g1_1 : (ScopedName * list TypeName) -> bool).
            evar (g1_2 : (ScopedName * list TypeName) -> bool).
            rewrite <- filter_compose with (f:=g1_1)(g:=g1_2).
            unfold g2. evar (g2_1 : (ScopedName * list TypeName) -> bool).
            evar (g2_2 : (ScopedName * list TypeName) -> bool).
            rewrite <- filter_compose with (f:=g2_1)(g:=g2_2).
            unfold g1_1. unfold g2_1. rewrite <- filter_app.
            unfold g1_2.
            instantiate (1:=fun x => match fst x with global _ => true | _ => false end).
            unfold g2_2.
            instantiate (1:=fun x => match fst x with local _ => true | _ => false end).
            match goal with [|- _ (_ ?f _) = _] => instantiate (1:=f) end.
            unfold global_before_local_ctors in GL. f_equal. rewrite filter_app.
            do 2 rewrite filter_compose. erewrite filter_ext; [ rewrite <- (GL (fst (fst x0))) |].
            { f_equal; erewrite filter_ext; [reflexivity| | reflexivity |].
              { intros. unfold cfunsigs_filterfun_g. destruct a. destruct s; cbn.
                - rewrite andb_false_r...
                - rewrite andb_true_r. rewrite eq_TypeName_symm...
              }
              { intros. unfold cfunsigs_filterfun_g. destruct a. destruct s; cbn.
                - rewrite andb_true_r. rewrite eq_TypeName_symm...
                - rewrite andb_false_r...
              }
            }
            intros. destruct a...
          - unfold g2. intros. unfold gfunsigs_filterfun_l. destruct a.
            rewrite eq_TypeName_eq in H1. subst tn. destruct s.
            + cbn. rewrite andb_true_r. apply eq_TypeName_symm.
            + cbn. rewrite andb_false_r...
        }
        intros. unfold g1. unfold gfunsigs_filterfun_g. destruct a.
        rewrite eq_TypeName_eq in H1. subst tn. destruct s.
        + cbn. rewrite andb_false_r...
        + cbn. rewrite andb_true_r. apply eq_TypeName_symm.
      - pose proof (program_cfun_bods_typecheck_l p) as TypL. unfold cfun_bods_l_typecheck in TypL.
        rewrite Forall_forall in TypL. rewrite filter_In in H0. destruct H0. rewrite in_map_iff in H0.
        do 2 destruct H0. apply TypL in H2. destruct H2 as [qn [args [t [LookupSig Typ]]]].
        inversion Typ; subst. cbn. rewrite map_map. rewrite map_length.
        (**)
        clear H11. rename H15 into H11. rename H13 into H9.
        (**)
        apply listTypeDeriv'_lemma_ctx in H11. rewrite Nat.eqb_eq in H11.
        repeat rewrite map_length in H11. unfold QName in *. unfold cfun_bod in *. rewrite <- H11.
        unfold lookup_ctors in H9.
        case_eq (filter (eq_TypeName (fst (fst x0))) (skeleton_dts (program_skeleton p))); intros;
          rewrite H in H9; try discriminate.
        inversion H9; subst.
        evar (g1 : (ScopedName * list TypeName) -> bool).
        rewrite filter_ext with (f:=gfunsigs_filterfun_g tn)(g:=g1).
        { evar (g2 : (ScopedName * list TypeName) -> bool).
          rewrite filter_ext with (f:=gfunsigs_filterfun_l tn)(g:=g2).
          - unfold g1. evar (g1_1 : (ScopedName * list TypeName) -> bool).
            evar (g1_2 : (ScopedName * list TypeName) -> bool).
            rewrite <- filter_compose with (f:=g1_1)(g:=g1_2).
            unfold g2. evar (g2_1 : (ScopedName * list TypeName) -> bool).
            evar (g2_2 : (ScopedName * list TypeName) -> bool).
            rewrite <- filter_compose with (f:=g2_1)(g:=g2_2).
            unfold g1_1. unfold g2_1. rewrite <- filter_app.
            unfold g1_2.
            instantiate (1:=fun x => match fst x with global _ => true | _ => false end).
            unfold g2_2.
            instantiate (1:=fun x => match fst x with local _ => true | _ => false end).
            match goal with [|- _ (_ ?f _) = _] => instantiate (1:=f) end.
            unfold global_before_local_ctors in GL. f_equal. rewrite filter_app.
            do 2 rewrite filter_compose. erewrite filter_ext; [ rewrite <- (GL (fst (fst x0))) |].
            { f_equal; erewrite filter_ext; [reflexivity| | reflexivity |].
              { intros. unfold cfunsigs_filterfun_g. destruct a. destruct s; cbn.
                - rewrite andb_false_r...
                - rewrite andb_true_r. rewrite eq_TypeName_symm...
              }
              { intros. unfold cfunsigs_filterfun_g. destruct a. destruct s; cbn.
                - rewrite andb_true_r. rewrite eq_TypeName_symm...
                - rewrite andb_false_r...
              }
            }
            intros. destruct a...
          - unfold g2. intros. unfold gfunsigs_filterfun_l. destruct a.
            rewrite eq_TypeName_eq in H1. subst tn. destruct s.
            + cbn. rewrite andb_true_r. apply eq_TypeName_symm.
            + cbn. rewrite andb_false_r...
        }
        intros. unfold g1. unfold gfunsigs_filterfun_g. destruct a.
        rewrite eq_TypeName_eq in H1. subst tn. destruct s.
        + cbn. rewrite andb_false_r...
        + cbn. rewrite andb_true_r. apply eq_TypeName_symm.
    }
    rewrite map_app. f_equal.
    * repeat rewrite map_map. apply map_ext_in. intros.
      unfold RefuncIII.globalize_aux. unfold RefuncIII.localize_aux.
      match goal with [|- ?lhs' = _] => set (lhs:=lhs') end.
      rewrite combine_fst_snd with (ps:=lhs).
      clear p0 l H. rename H0 into H.
      f_equal.
      -- unfold lhs. rewrite map_map. simpl. rewrite map_app. repeat rewrite map_map. simpl.
         erewrite filter_ext with (f:=fun x => eq_TypeName (fst (unscope (fst x))) tn).
         ++ rewrite filter_map. rewrite map_app. repeat rewrite map_map. simpl.
            rewrite filter_app.

            erewrite cfun_bods_g_map_filter.
            2:{ rewrite filter_In in H. destruct H... }
            2:{ rewrite filter_In in H. destruct H as [_ H]. unfold cfunsigs_filterfun_g in H.
                destruct a. destruct s; try discriminate. apply Is_global_global.
            }
            erewrite cfun_bods_l_map_filter.
            2:{ rewrite filter_In in H. destruct H... }
            2:{ rewrite filter_In in H. destruct H as [_ H]. unfold cfunsigs_filterfun_g in H.
                destruct a. destruct s; try discriminate. apply Is_global_global.
            }
            repeat rewrite map_map. simpl. f_equal.
            ** generalize (program_cfun_bods_g p). induction c...
               simpl. case_eq (eq_TypeName (fst (unscope (fst a))) (fst (fst a0))); intros.
               --- unfold QName in *. rewrite H0. simpl.
                   instantiate (1:=fun x => eq_TypeName (fst (unscope (fst a))) (fst (unscope x))).
                   simpl. rewrite H0. f_equal...
               --- simpl. unfold QName in *. rewrite H0...
            ** generalize (program_cfun_bods_l p). induction c...
               simpl. case_eq (eq_TypeName (fst (unscope (fst a))) (fst (fst a0))); intros.
               --- unfold QName in *. rewrite H0. simpl. f_equal...
               --- simpl. unfold QName in *. rewrite H0...
         ++ intros. simpl. rewrite eq_TypeName_symm.
            clear - H. rewrite filter_In in H. destruct H as [_ H].
            unfold gfunsigs_filterfun_g in H. destruct a. destruct s; try discriminate. simpl.
            rewrite eq_TypeName_eq in H. subst tn...
      -- unfold lhs. erewrite cfun_bods_g_map_filter with (d:=(sn,E_FunCall (snd (unscope sn)) []))...
         2:{ apply filter_In in H. destruct H... }
         2:{ apply filter_In in H. destruct H. unfold gfunsigs_filterfun_g in H0. destruct a.
             destruct s; try discriminate. constructor.
         }
         rewrite map_map. simpl. repeat rewrite map_map. simpl.
         erewrite cfun_bods_l_map_filter with (d:=(sn,E_FunCall (snd (unscope sn)) []))...
         2:{ apply filter_In in H. destruct H... }
         2:{ apply filter_In in H. destruct H. unfold gfunsigs_filterfun_g in H0. destruct a.
             destruct s; try discriminate. constructor.
         }
         rewrite map_map. simpl. rewrite filter_app. repeat rewrite map_app. f_equal.
         ++ rewrite map_map. simpl.

            apply filter_In in H. destruct H. unfold gfunsigs_filterfun_g in H0. destruct a.
            destruct s; try discriminate. rewrite eq_TypeName_eq in H0. simpl. subst tn.

            erewrite filter_ext.
            2:{ intros. rewrite eq_TypeName_symm. reflexivity. }

            rewrite <- filter_map. simpl. rewrite map_map. simpl.
            apply map_ext. intros. generalize (snd a). induction c.
            ** simpl. unfold RefuncIII.switch_indices_aux. unfold switch_indices_cfun.
               destruct (lookup_cfun_sig_scoped (program_skeleton p) (global (fst a)))...
            ** simpl. unfold refunc_term_helper. destruct a0. simpl. destruct s.
               --- rewrite IHc...
               --- case_eq (eq_QName q q0); intros...
                   simpl. rewrite eq_QName_eq in H0. subst.
                   change (global q0) with (fst (global q0, l)).
                   rewrite in_ctors_lookup_ctor_sig...
         ++ rewrite map_map. simpl.

            apply filter_In in H. destruct H. unfold gfunsigs_filterfun_g in H0. destruct a.
            destruct s; try discriminate. rewrite eq_TypeName_eq in H0. simpl. subst tn.

            erewrite filter_ext.
            2:{ intros. rewrite eq_TypeName_symm. reflexivity. }

            rewrite <- filter_map. simpl. rewrite map_map. simpl.
            apply map_ext. intros. generalize (snd a). induction c.
            ** simpl. unfold RefuncIII.switch_indices_aux. unfold switch_indices_cfun.
               destruct (lookup_cfun_sig_scoped (program_skeleton p) (local (fst a)))...
            ** simpl. unfold refunc_term_helper. destruct a0. simpl. destruct s.
               --- rewrite IHc...
               --- case_eq (eq_QName q q0); intros...
                   simpl. rewrite eq_QName_eq in H0. subst.
                   change (global q0) with (fst (global q0, l)).
                   rewrite in_ctors_lookup_ctor_sig...
    * repeat rewrite map_map. apply map_ext_in. intros.
      unfold RefuncIII.globalize_aux. unfold RefuncIII.localize_aux.
      match goal with [|- ?lhs' = _] => set (lhs:=lhs') end.
      rewrite combine_fst_snd with (ps:=lhs).
      clear p0 l H. rename H0 into H.
      f_equal.
      -- unfold lhs. rewrite map_map. simpl. rewrite map_app. repeat rewrite map_map. simpl.
         erewrite filter_ext with (f:=fun x => eq_TypeName (fst (unscope (fst x))) tn).
         ++ rewrite filter_map. rewrite map_app. repeat rewrite map_map. simpl.
            rewrite filter_app.

            erewrite cfun_bods_g_map_filter_l.
            2:{ rewrite filter_In in H. destruct H... }
            2:{ rewrite filter_In in H. destruct H as [_ H]. unfold gfunsigs_filterfun_l in H.
                destruct a. destruct s; try discriminate. apply Is_local_local.
            }
            erewrite cfun_bods_l_map_filter_l.
            2:{ rewrite filter_In in H. destruct H... }
            2:{ rewrite filter_In in H. destruct H as [_ H]. unfold gfunsigs_filterfun_l in H.
                destruct a. destruct s; try discriminate. apply Is_local_local.
            }
            repeat rewrite map_map. simpl. f_equal.
            ** generalize (program_cfun_bods_g p). induction c...
               simpl. case_eq (eq_TypeName (fst (unscope (fst a))) (fst (fst a0))); intros.
               --- unfold QName in *. rewrite H0. simpl.
                   instantiate (1:=fun x => eq_TypeName (fst (unscope (fst a))) (fst (unscope x))).
                   simpl. rewrite H0. f_equal...
               --- simpl. unfold QName in *. rewrite H0...
            ** generalize (program_cfun_bods_l p). induction c...
               simpl. case_eq (eq_TypeName (fst (unscope (fst a))) (fst (fst a0))); intros.
               --- unfold QName in *. rewrite H0. simpl. f_equal...
               --- simpl. unfold QName in *. rewrite H0...
         ++ intros. simpl. rewrite eq_TypeName_symm.
            clear - H. rewrite filter_In in H. destruct H as [_ H].
            unfold gfunsigs_filterfun_l in H. destruct a. destruct s; try discriminate. simpl.
            rewrite eq_TypeName_eq in H. subst tn...
      -- unfold lhs. erewrite cfun_bods_g_map_filter_l with (d:=(sn,E_FunCall (snd (unscope sn)) []))...
         2:{ apply filter_In in H. destruct H... }
         2:{ apply filter_In in H. destruct H. unfold gfunsigs_filterfun_l in H0. destruct a.
             destruct s; try discriminate. constructor.
         }
         rewrite map_map. simpl. repeat rewrite map_map. simpl.
         erewrite cfun_bods_l_map_filter_l with (d:=(sn,E_FunCall (snd (unscope sn)) []))...
         2:{ apply filter_In in H. destruct H... }
         2:{ apply filter_In in H. destruct H. unfold gfunsigs_filterfun_l in H0. destruct a.
             destruct s; try discriminate. constructor.
         }
         rewrite map_map. simpl. rewrite filter_app. repeat rewrite map_app. f_equal.
         ++ rewrite map_map. simpl.

            apply filter_In in H. destruct H. unfold gfunsigs_filterfun_l in H0. destruct a.
            destruct s; try discriminate. rewrite eq_TypeName_eq in H0. simpl. subst tn.

            erewrite filter_ext.
            2:{ intros. rewrite eq_TypeName_symm. reflexivity. }

            rewrite <- filter_map. simpl. rewrite map_map. simpl.
            apply map_ext. intros. generalize (snd a). induction c.
            ** simpl. unfold RefuncIII.switch_indices_aux. unfold switch_indices_cfun.
               destruct (lookup_cfun_sig_scoped (program_skeleton p) (global (fst a)))...
            ** simpl. unfold refunc_term_helper. destruct a0. simpl. destruct s.
               --- case_eq (eq_QName q q0); intros...
                   simpl. rewrite eq_QName_eq in H0. subst.
                   change (local q0) with (fst (local q0, l)).
                   rewrite in_ctors_lookup_ctor_sig...
               --- rewrite IHc...

         ++ rewrite map_map. simpl.

            apply filter_In in H. destruct H. unfold gfunsigs_filterfun_l in H0. destruct a.
            destruct s; try discriminate. rewrite eq_TypeName_eq in H0. simpl. subst tn.

            erewrite filter_ext.
            2:{ intros. rewrite eq_TypeName_symm. reflexivity. }

            rewrite <- filter_map. simpl. rewrite map_map. simpl.
            apply map_ext. intros. generalize (snd a). induction c.
            ** simpl. unfold RefuncIII.switch_indices_aux. unfold switch_indices_cfun.
               destruct (lookup_cfun_sig_scoped (program_skeleton p) (local (fst a)))...
            ** simpl. unfold refunc_term_helper. destruct a0. simpl. destruct s.
               --- case_eq (eq_QName q q0); intros...
                   simpl. rewrite eq_QName_eq in H0. subst.
                   change (local q0) with (fst (local q0, l)).
                   rewrite in_ctors_lookup_ctor_sig...
               --- rewrite IHc...
Unshelve. all:repeat constructor.
Qed.

Lemma same_ctors : forall (p : program) (tn : TypeName) (cfd1 cfd2 : list ScopedName),
  In cfd1 (map (map fst) (map snd (program_cfun_bods_for_type tn p))) ->
  In cfd2 (map (map fst) (map snd (program_cfun_bods_for_type tn p))) ->
  cfd1 = cfd2.
Proof.
intros. rewrite in_map_iff in *. do 2 destruct H. do 2 destruct H0. subst.
rewrite in_map_iff in *. destruct H1. destruct H. destruct H2. destruct H1. subst.
unfold program_cfun_bods_for_type in *. rewrite filter_In in *.
destruct H0. destruct H2. apply in_app_or in H. apply in_app_or in H1.
pose proof (program_cfun_bods_typecheck_g p) as TypG. unfold cfun_bods_g_typecheck in TypG.
rewrite Forall_forall in TypG.
pose proof (program_cfun_bods_typecheck_l p) as TypL. unfold cfun_bods_l_typecheck in TypL.
rewrite Forall_forall in TypL;
destruct H; destruct H1;
  rewrite in_map_iff in *; do 2 destruct H; do 2 destruct H1; destruct x1; destruct x2;
  inversion H; subst; inversion H1; subst; cbn in *;
  try apply TypG in H3; try apply TypG in H4; try apply TypL in H3; try apply TypL in H4;
  rename H0 into tnEq1; rename H2 into tnEq2;
  clear - H3 H4 tnEq1 tnEq2;
  destruct H3 as [qn1 [args1 [t1 [_ Typ1]]]]; destruct H4 as [qn2 [args2 [t2 [_ Typ2]]]];
  inversion Typ1; subst; inversion Typ2; subst; rewrite eq_TypeName_eq in *;
  unfold cfun_bod in *; rewrite tnEq1 in H10; rewrite tnEq2 in H17;
  rewrite H17 in H10; inversion H10; subst;
  pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H12) as Len1;
  pose proof (listTypeDeriv'_lemma_ctx _ _ _ _ H19) as Len2;
  clear - H11 H18 Len1 Len2; rewrite Nat.eqb_eq in *; repeat rewrite map_length in *;
  generalize dependent ctorlist; generalize dependent (snd x); generalize dependent (snd x0);
  clear; induction l; intros;
    try solve [ rewrite Len1 in Len2; destruct l; eauto; discriminate ];
    try solve [
      rewrite Len1 in Len2; destruct l0; try discriminate; cbn;
      destruct ctorlist; try discriminate; cbn in *;
      inversion H11; subst; inversion H18; subst; destruct p; destruct a; destruct p0;
      subst; f_equal; eapply IHl; eauto; omega
    ].
Qed.

Lemma refunc_is_matrix_transpose : forall p tn P1 P2 P3 P4 P5 pr
  (GL : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (Nonempty : program_cfun_bods_for_type tn p <> []),
  pr = refunctionalize_program p tn P1 P2 P3 P4 P5 ->
  program_gfun_bods_for_type tn pr =
    map (fun x => (fst x, map (fun y => (fst y, refunc_term_helper (program_skeleton p) tn (fst y) (fst x) (snd y))) (snd x)))
      (read_gfuns_from_matrix (transpose_matrix (read_cfuns_into_matrix (program_cfun_bods_for_type tn p)))).
Proof with eauto.
intros. erewrite refunc_is_matrix_transpose'... clear.
remember (program_cfun_bods_for_type tn p) as l. intros. cbn.
rewrite map_map. cbn. destruct l...
repeat rewrite map_map. cbn [snd]. cbn [map]. cbn [snd].
rewrite map_map. cbn [fst]. rewrite map_map. cbn [snd].
change (fun x : ScopedName * list (ScopedName * expr) => fst x) with (@fst ScopedName (list (ScopedName * expr))).
erewrite map_ext with (f:=fun x => map snd _).
2:{ intros. rewrite map_map. cbn. reflexivity. }
change (fun x : ScopedName * expr => fst x) with (@fst ScopedName expr).
rewrite <- map_map with (f:=snd). unfold cfun_bod in *.
replace (map snd (snd p0) :: map (map snd) (map snd l)) with
  (map (map snd) (snd p0 :: map snd l))...
replace (snd p0 :: map snd l) with (map snd (p0::l))...
generalize (length (map fst (snd p0))). intros.
replace (fst p0 :: map fst l) with (map fst (p0::l))...
remember (map fst (snd p0)) as l0.
match goal with [|- _ (_ _ (_ ((map ?f' (snd p0)) :: map ?f ?l) _)) = _] =>
  replace (map f' (snd p0) :: map f l) with (map f (p0::l)) end...
remember (p0::l) as l1.
assert (exists l', l'++l1 = p0::l /\ l'++l1 = program_cfun_bods_for_type tn p).
{ exists []... }
clear Heql1 Heql. rename H into Heql1.
clear - Heql0 Heql1.
generalize (refunc_term_helper (program_skeleton p) tn) as f. intros.
pose proof (eq_refl (length l1)). generalize dependent H. generalize dependent Heql1.
generalize (length l1) at 2. intros. generalize dependent l1.
induction n0; intros...
- destruct l1; try discriminate. cbn. clear.
  generalize dependent n. induction l0... destruct n... cbn. f_equal...
- destruct l1; try discriminate. cbn [map]. cbn [transpose].
  case_eq (snd p1); intros.
  + cbn. destruct l0...
  + cbn [map]. repeat rewrite map_with_index_map. repeat rewrite with_index_map_map.
    cbn [combine].
    match goal with [|- _ _ (_ (fun n1 x => ?lhs :: (?rhs x)) _) = _] =>
      change (fun n1 x => lhs :: (rhs x)) with (fun n x => (fun n1 y1 => lhs :: y1) n ((fun (_:nat) y2 => rhs y2) n x))
    end.
    rewrite <- with_index_map_map. repeat rewrite <- map_with_index_map.
    rewrite <- map_with_index_snd_f_combine. rewrite IHn0...
    2:{ destruct Heql1. exists (x++[p1]). rewrite <- app_assoc... }
    rewrite map_map.
    match goal with [|- _ _ (_ _ (_ _ (_ _ ?t))) = _] => generalize t end.
    clear - H0 Heql0 Heql1 H. rename H into Len. intros.
    repeat rewrite map_with_index_map. rewrite with_index_map_map. cbn - [nth].
    match goal with [|- _ = _ _ (_ _ (_ ?f' _))] =>
      rewrite <- map_with_index_snd_f_combine with (f0:=f')
    end.
    rewrite <- map_with_index_snd_f_combine. repeat rewrite with_index_map_map.
    apply map_with_index_ext_in. intros. cbn - [nth]. f_equal. f_equal. f_equal.
    repeat rewrite <- map_with_index_map.
    destruct p2. cbn - [nth].
    match goal with [|- _ _ (f (fst p1) s e :: (map ?f' l2)) _ = _] =>
      replace (f (fst p1) s e :: map f' l2) with (map f' ((s,e)::l2)) end...
    set (f':=fun x => f (fst p1) (fst x) (snd x)).
    replace (f (fst p1) s e) with (f' (s,e))...
    replace (f (fst p1) (fst a) (nth n (e :: map snd l2) e)) with
      (f' (fst a, nth n (e :: map snd l2) e))...
    replace e with (snd (s,e)) at 3 4...
    replace (snd (s, e) :: map snd l2) with (map snd ((s,e)::l2))...
    rewrite map_nth. rewrite map_nth.
    assert (fst a = fst (nth n ((s, e) :: l2) (s, e))).
    { assert (fst a = nth n l0 s).
      { symmetry in H1. pose proof H1 as H1'.
        apply nth_error_nth with (d:=(s,[e])) in H1. subst.
        assert (n < length (combine (map fst (snd p0)) l3)).
        { apply nth_error_Some. unfold not. intros. rewrite H1 in H1'. discriminate. }
        rewrite <- firstn_skipn with (l:=combine (map fst (snd p0)) l3)
         (n:=Nat.min (length (snd p0)) (length l3)).
        rewrite <- map_nth with (f:=fst). rewrite combine_length in H1.
        rewrite map_length in H1. rewrite map_app. rewrite app_nth1...
        2:{ rewrite map_length. rewrite firstn_length. rewrite combine_length.
          rewrite map_length. rewrite Nat.min_id... }
        rewrite firstn_combine. rewrite map_fst_combine.
        2:{ repeat rewrite firstn_length. rewrite Nat.min_comm. rewrite Nat.min_assoc.
          rewrite map_length. rewrite Nat.min_id. rewrite <- Nat.min_assoc.
          rewrite Nat.min_id... }
        rewrite <- firstn_skipn with (l:=map fst (snd p0))
          (n:=Nat.min (length (snd p0)) (length l3)) at 2.
        rewrite app_nth1... rewrite firstn_length.
        rewrite Nat.min_comm. rewrite Nat.min_assoc.
        rewrite map_length. rewrite Nat.min_id...
      }
      rewrite H2. rewrite <- H0. subst l0. replace s with (fst (s,e))...
      rewrite map_nth... cbn. rewrite <- map_nth.
      rewrite <- map_nth with (f:=fst). f_equal.
      destruct Heql1. destruct H3. pose proof (in_eq p0 l).
      rewrite <- H3 in H5. rewrite H4 in H5.
      assert (In p1 (program_cfun_bods_for_type tn p)).
      { rewrite <- H4. apply in_or_app. right. left... }
      clear - H5 H6. apply (in_map snd) in H5. apply (in_map snd) in H6.
      apply (in_map (map fst)) in H5. apply (in_map (map fst)) in H6.
      eapply same_ctors...
    }
    rewrite H2. rewrite <- surjective_pairing...
Qed.



Lemma in_map_with_index_if : forall {A B} (l : list A) (f : nat -> A -> B) y,
  In y (map_with_index f l) ->
  exists x n, f n x = y /\ In x l.
Proof with eauto.
intros. unfold map_with_index in H. generalize dependent 0.
induction l; intros.
- cbn in H. exfalso...
- cbn in *. destruct H... apply IHl in H. do 3 destruct H. subst.
  exists x. exists x0. split...
Qed.

Corollary derefunc_preserves_gfuns_nonempty :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton (defunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (Nonempty : program_gfun_bods_for_type tn p <> [])
  (NonemptyCfuns : program_cfun_bods_for_type tn (defunctionalize_program p tn P1 P2 P3 P4 P5) <> [])
  (NonemptyDtors : forall x, In x (map snd (program_gfun_bods_for_type tn p)) -> x <> [])
  (DefuncCdt : forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn)
  (DefuncCdt2 : In tn (skeleton_cdts (program_skeleton p))),
  pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5   ->
  pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_gfun_bods_for_type tn p = program_gfun_bods_for_type tn pr2.
Proof with eauto.
intros. subst. symmetry. erewrite refunc_is_matrix_transpose... erewrite defunc_is_matrix_transpose...
match goal with [|- map _ (_ (_ (_ (_ ?l)))) = _] => case_eq (snd l); intros end.
{ case_eq (program_gfun_bods_for_type tn p); intros...
  rewrite H0 in H.
  match goal with [_ : ?l' = [] |- _] => assert (l' <> []) end.
  { generalize dependent (p0::l). clear - Nonempty NonemptyDtors.
    intros. rewrite H0 in *. clear H H0.
    assert (exists l' x, l = l'++[x]).
    { clear - Nonempty. induction l.
      - exfalso. apply Nonempty...
      - destruct l.
        + exists []. exists a...
        + assert (p::l <> []). { unfold not. intros. discriminate. }
          pose proof (IHl H). do 2 destruct H0. exists (a::x). exists x0.
          rewrite H0...
    }
    do 2 destruct H. subst l. clear Nonempty. rename x into l. cbn.
    match goal with [|- _ _ ?len <> _] => assert (exists len', len = S len') end.
    { destruct l.
      - cbn in NonemptyDtors. specialize NonemptyDtors with (x:=snd x0).
        pose proof (NonemptyDtors (or_introl eq_refl)). destruct x0. destruct g.
        + exfalso. apply H...
        + cbn. eexists...
      - cbn in *. specialize NonemptyDtors with (x:=snd p0).
        pose proof (NonemptyDtors (or_introl eq_refl)). destruct p0. destruct g.
        + exfalso. apply H...
        + cbn. eexists...
    }
    destruct H. rewrite H. generalize x. clear H.
    induction l; intros.
    - cbn. destruct x0. cbn. destruct g.
      + cbn in *. exfalso. specialize NonemptyDtors with (x:=[]).
        cut ((@nil (ScopedName * expr)) <> []).
        * intros. apply H...
        * apply NonemptyDtors. left...
      + cbn. unfold not. intros. discriminate.
    - cbn. destruct a. cbn. destruct g.
      + cbn. exfalso. specialize NonemptyDtors with (x:=[]).
        cut ((@nil (ScopedName * expr)) <> []).
        * intros. apply H...
        * apply NonemptyDtors. left...
      + cbn in *. unfold not. intros.
        match goal with [_ : _ _ ?l' = [] |- _] => case_eq l'; intros end.
        2:{ rewrite H0 in H. cbn in H. discriminate. }
        unfold not in IHl. eapply IHl...
        intros. clear IHl H. subst.
        pose proof (NonemptyDtors [] (or_intror H1)). apply H...
  }
  rewrite H in H1. exfalso. apply H1...
}
rewrite read_cfuns_from_into_matrix.
2:{ rewrite H. unfold not. intros. discriminate. }
2:{ remember (program_gfun_bods_for_type tn p) as l1. clear - Heql1 NonemptyDtors. cbn.
  match goal with [|- _ (match ?m' with | [] => _ | _ => _ end) = _] => remember m' as m end.
  assert (forall x : gfun_bod, In x (map snd m) -> x <> []).
  { intros. subst m. rewrite map_map in H. cbn in H.
    rewrite in_map_iff in H. do 2 destruct H. subst x. apply (in_map snd) in H0.
    apply NonemptyDtors in H0. unfold not. intros. apply H0. destruct (snd x0)...
    cbn in H. discriminate.
  }
  assert (forall x1 x2, In x1 (map snd m) -> In x2 (map snd m) -> map fst x1 = map fst x2).
  { subst m. repeat rewrite map_map. cbn. intros.
    rewrite in_map_iff in *. destruct H0 as [H0_x [H0_eq H0]]. destruct H1 as [H1_x [H1_eq H1]].
    apply (f_equal (map fst)) in H0_eq. apply (f_equal (map fst)) in H1_eq.
    rewrite map_map in *. cbn in *. rewrite <- H0_eq. rewrite <- H1_eq. subst l1. clear - H0 H1.
    apply (in_map snd) in H0. apply (in_map snd) in H1.
    apply (in_map (map fst)) in H0. apply (in_map (map fst)) in H1.
    eapply same_dtors...
  }
  clear Heqm NonemptyDtors Heql1 l1.
  match goal with [|- ?n' = _] => remember n' as n end.
  generalize dependent n.
  induction m; intros; cbn; try rewrite repeat_length...
  case_eq (map snd (snd a)); intros.
  - unfold gfun_bod. rewrite H1.
    rewrite map_length in Heqn. subst. apply (f_equal (@length _)) in H1. rewrite map_length in H1...
  - unfold gfun_bod. rewrite H1. unfold map_with_index. rewrite map_with_index'_length.
    destruct m.
    + cbn. rewrite repeat_length...
    + apply IHm.
      * intros. apply H. cbn. right...
      * intros. eapply H0; cbn; right...
      * subst n. clear - H H0. cbn [map] in H0. pose proof (in_eq (snd a) (map snd m)).
        assert (In (snd p0) (snd a :: map snd (p0 :: m))). { right. left... }
        f_equal. apply H0... left...
}
2:{ intros. cbn. rewrite map_map. rewrite map_length. cbn in H0.
  repeat rewrite map_map in H0. cbn in H0. erewrite map_ext in H0.
  2:{ intros. rewrite map_map. cbn. reflexivity. }
  clear - H0.
  match goal with [_ : In _ (_ _ ?len) |- _] => generalize dependent len end.
  generalize dependent (program_gfun_bods_for_type tn p).
  generalize dependent l'. intros l' l. generalize l'. clear l'.
  induction l; intros.
  - cbn in H0. apply repeat_spec in H0. subst...
  - cbn in H0. case_eq (snd a); intros.
    + unfold gfun_bod in *. rewrite H in H0. cbn in H0. exfalso...
    + unfold gfun_bod in *. rewrite H in H0. cbn in H0.
      apply in_map_with_index_if in H0.
      destruct H0 as [H0_x [H0_n [H0_eq H0]]].
      destruct l'; try discriminate.
      cbn. f_equal. eapply IHl. inversion H0_eq; subst. apply H0.
}
clear H.
rewrite transpose_transpose.
2:{ simpl. repeat rewrite map_map. repeat rewrite map_length... }
2:{ rewrite Forall_forall. intros. clear - H. simpl in *.
  case_eq (program_gfun_bods_for_type tn p); intros.
  - rewrite H0 in H. simpl in H. exfalso...
  - simpl. repeat rewrite map_map in H. simpl in H. erewrite map_ext in H.
    2:{ intros. rewrite map_map. simpl. reflexivity. }
    rewrite map_map. simpl. rewrite in_map_iff in H. do 2 destruct H. subst.
    repeat rewrite map_length. pose proof (in_eq p0 l). rewrite <- H0 in H.
    apply (in_map snd) in H. apply (in_map snd) in H1.
    apply (in_map (map fst)) in H. apply (in_map (map fst)) in H1.
    repeat rewrite <- map_length with (f:=fst).
    erewrite same_dtors with (gfd1:=map fst (snd x0))...
}
rewrite read_gfuns_into_from_matrix.
- rewrite map_map. simpl. rewrite combine_fst_snd at 1. rewrite map_map. simpl.
  rewrite combine_fst_snd. f_equal...
  rewrite map_map. simpl. erewrite map_ext_in.
  2:{ intros. rewrite map_map. simpl. erewrite map_ext_in.
    2:{ intros. rewrite surjective_pairing with (p:=a0) in H0. rewrite surjective_pairing with (p:=a) in H.
      erewrite derefunc_helper_inverse... rewrite <- surjective_pairing. instantiate (1:=id). unfold id... }
    reflexivity.
  }
  apply map_ext. intros. rewrite map_id...
- intros. apply same_dtors with (p:=p) (tn:=tn).
  + rewrite in_map_iff in H. do 2 destruct H. destruct gfb1. inversion H; subst. simpl.
    rewrite map_map. simpl. apply in_map. apply in_map...
  + rewrite in_map_iff in H0. do 2 destruct H0. destruct gfb2. inversion H0; subst. simpl.
    rewrite map_map. simpl. apply in_map. apply in_map...
Qed.

Lemma derefunc_preserves_gfuns_empty_dtors :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (DefuncCdt : forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn)
  (DefuncCdt2 : In tn (skeleton_cdts (program_skeleton p)))
  (H : pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5 )
  (H0 : pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5')
  (p0 : ScopedName * gfun_bod)
  (l : list (ScopedName * gfun_bod))
  (H1 : program_gfun_bods_for_type tn p = p0 :: l)
  (H2 : snd p0 = []),
  p0 :: l = program_gfun_bods_for_type tn pr2.
Proof with eauto.
intros.
assert (Forall (fun x => snd x = []) l).
{ clear - H1 H2. rewrite Forall_forall. intros.
  assert (In x (p0::l)). { right... }
  apply (in_map snd) in H0.
  case_eq (snd x)... intros. rewrite H3 in H0.
  pose proof (in_eq p0 l). rewrite <- H1 in H4. rewrite <- H1 in H0.
  apply (in_map snd) in H4. apply (in_map (map fst)) in H4.
  apply (in_map (map fst)) in H0.
  pose proof (same_dtors _ _ _ _ H4 H0). rewrite H2 in H5. discriminate.
}

assert (Forall (fun x => snd x = []) (p0::l)). { constructor... }
clear H3 H2. rewrite <- H1 in *. clear H1. subst.
clear - H4 DefuncCdt DefuncCdt2.
unfold program_gfun_bods_for_type in H4. rewrite filter_app in H4.
rewrite <- Forall_app_iff in H4. destruct H4.

cbn. rewrite filter_app. unfold program_gfun_bods_for_type. rewrite filter_app.
f_equal.
- rewrite map_app. rewrite filter_app.
  unfold computeNewDatatype. unfold DefuncIII.new_gfun_bods_g.
  match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * gfun_bod)) end.
  2:{ rewrite map_map. cbn. match goal with [|- _ = _ _ (_ ?f (_ _ ?l))] =>
    generalize l end. clear. induction l; intros...
    cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    cbn. rewrite eq_TypeName_symm. rewrite H...
  }
  rewrite app_nil_r.
  rewrite filter_app. unfold Constructor.
  replace (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p)))
    with (@nil (ScopedName * list TypeName)).
  2:{ match goal with [|- _ = ?l] => case_eq l; intros end...
    clear - DefuncCdt H1. exfalso. pose proof (in_eq p0 l).
    rewrite <- H1 in H. clear H1. rewrite filter_In in H.
    destruct H. unfold not in DefuncCdt. eapply DefuncCdt... clear - H0.
    unfold gfunsigs_filterfun_g in H0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0; subst...
  }
  rewrite app_nil_r. rewrite filter_app. rewrite map_map. cbn.
  match goal with [|- _ = _ _ (_ _ (_ ++ ?l))] => replace l with (@nil (ScopedName * list TypeName)) end.
  2:{ clear. match goal with [|- _ = _ _ (_ _ ?l)] => generalize l end. induction l... }
  rewrite app_nil_r.
  match goal with [|- ?m = _] => rewrite combine_fst_snd with (ps:=m) end.
  change (fun x : ScopedName * gfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
    with (fun x : ScopedName * gfun_bod => (fun y => eq_TypeName (fst (unscope y)) tn) (fst x)).
  rewrite filter_map. rewrite map_map. cbn.
  match goal with [|- _ = ?m] => rewrite combine_fst_snd with (ps:=m) end.
  change (fun x : ScopedName * gfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
    with (fun x : ScopedName * gfun_bod => (fun y => eq_TypeName (fst (unscope y)) tn) (fst x)).
  rewrite filter_map. rewrite map_map. cbn.
  f_equal.
  + rewrite <- map_map with (g:=global). rewrite <- (program_has_all_gfun_bods_g p).
    unfold gfunsigs_filterfun_g. repeat rewrite <- filter_map.
    repeat rewrite map_map. cbn. f_equal. repeat rewrite filter_compose.
    apply filter_ext. intros. rewrite eq_TypeName_symm with (tn1:=tn).
    repeat rewrite andb_diag...
  + clear - H H0 DefuncCdt2. unfold DefuncIII.new_cfun_bods_g. unfold DefuncIII.new_cfun_bods_l.
    erewrite map_ext_in with (l:=filter (gfunsigs_filterfun_g tn) _).
    2:{ intros. erewrite map_ext_in with (l:=filter (cfunsigs_filterfun_g tn) _).
      2:{ intros.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H H2. generalize dependent (program_gfun_bods_g p). induction g...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H.
          replace ((global (fst a), snd a)::map (fun x => (global (fst x), snd x)) g)
            with ([(global (fst a), snd a)]++map (fun x => (global (fst x), snd x)) g) in H...
          rewrite filter_app in H. rewrite <- Forall_app_iff in H. destruct H.
          rewrite <- IHg...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct g...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction g...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold cfunsigs_filterfun_g in H1.
            destruct a0. destruct p0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H0 H2. generalize dependent (program_gfun_bods_l p). induction g...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H0.
          replace ((local (fst a), snd a)::map (fun x => (local (fst x), snd x)) g)
            with ([(local (fst a), snd a)]++map (fun x => (local (fst x), snd x)) g) in H0...
          rewrite filter_app in H0. rewrite <- Forall_app_iff in H0. destruct H0.
          rewrite <- IHg...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct g...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction g...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold cfunsigs_filterfun_g in H1.
            destruct a0. destruct p0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn. reflexivity.
      }
      erewrite map_ext_in with (l:=filter (cfunsigs_filterfun_l tn) _).
      2:{ intros.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H H2. generalize dependent (program_gfun_bods_g p). induction g...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H.
          replace ((global (fst a), snd a)::map (fun x => (global (fst x), snd x)) g)
            with ([(global (fst a), snd a)]++map (fun x => (global (fst x), snd x)) g) in H...
          rewrite filter_app in H. rewrite <- Forall_app_iff in H. destruct H.
          rewrite <- IHg...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct g...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction g...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold cfunsigs_filterfun_l in H1.
            destruct a0. destruct p0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H0 H2. generalize dependent (program_gfun_bods_l p). induction g...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H0.
          replace ((local (fst a), snd a)::map (fun x => (local (fst x), snd x)) g)
            with ([(local (fst a), snd a)]++map (fun x => (local (fst x), snd x)) g) in H0...
          rewrite filter_app in H0. rewrite <- Forall_app_iff in H0. destruct H0.
          rewrite <- IHg...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct g...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction g...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold cfunsigs_filterfun_l in H1.
            destruct a0. destruct p0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn. reflexivity.
      }
      repeat rewrite flat_map_app.
      match goal with [|- (_, _ _ (_ (_ (?l ++ _))) ++ _) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{ clear. generalize (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p))).
        intros. induction l...
      }
      cbn.
      match goal with [|- (_, _ ++ _ _ (_ (_ (?l ++ _)))) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{ clear. generalize (filter (cfunsigs_filterfun_l tn) (skeleton_dtors (program_skeleton p))).
        intros. induction l...
      }
      cbn.
      match goal with [|- (_, _ _ (_ ?l) ++ _) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{
        intros. clear - DefuncCdt2 H1. remember (program_cfun_bods_g p) as c.
        assert (Forall (fun x => In x (program_cfun_bods_g p)) c).
        { subst. rewrite Forall_forall... }
        clear - H DefuncCdt2 H1. induction c...
        inversion H; subst. cbn. rewrite filter_app. rewrite <- IHc...
        rewrite app_nil_r. clear - H3 H1 DefuncCdt2. destruct a0. cbn.
        assert (exists l, In (q, l++c) (program_cfun_bods_g p)). { exists []... }
        clear H3.
        induction c... cbn. destruct q. rewrite <- IHc.
        2:{ destruct H. exists (x++[a0]). rewrite <- app_assoc... }
        destruct a0. destruct s... cbn.
        case_eq (eq_TypeName t (fst (unscope (fst a)))); intros...
        exfalso. clear IHc. destruct H.
        apply (in_map fst) in H. cbn in H. rewrite <- (program_has_all_cfun_bods_g p) in H.
        rewrite eq_TypeName_eq in H0. subst.
        pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)).
        unfold cfun_sigs_in_dts in H0. rewrite Forall_forall in H0.
        rewrite in_map_iff in H. do 2 destruct H. apply H0 in H2.
        unfold QName in *. rewrite H in H2. cbn in H2. clear - H H1 H2 DefuncCdt2.
        rewrite filter_In in H1. destruct H1. unfold gfunsigs_filterfun_g in H1.
        destruct a. destruct s; try discriminate. rewrite eq_TypeName_eq in H1. subst.
        cbn in H2. clear - H2 DefuncCdt2.
        pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
        unfold dts_cdts_disjoint in H. unfold not in H. eapply H...
      }
      cbn.
      match goal with [|- (_, _ _ (_ ?l)) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{
        intros. clear - DefuncCdt2 H1. remember (program_cfun_bods_l p) as c.
        assert (Forall (fun x => In x (program_cfun_bods_l p)) c).
        { subst. rewrite Forall_forall... }
        clear - H DefuncCdt2 H1. induction c...
        inversion H; subst. cbn. rewrite filter_app. rewrite <- IHc...
        rewrite app_nil_r. clear - H3 H1 DefuncCdt2. destruct a0. cbn.
        assert (exists l, In (q, l++c) (program_cfun_bods_l p)). { exists []... }
        clear H3.
        induction c... cbn. destruct q. rewrite <- IHc.
        2:{ destruct H. exists (x++[a0]). rewrite <- app_assoc... }
        destruct a0. destruct s... cbn.
        case_eq (eq_TypeName t (fst (unscope (fst a)))); intros...
        exfalso. clear IHc. destruct H.
        apply (in_map fst) in H. cbn in H. rewrite <- (program_has_all_cfun_bods_l p) in H.
        rewrite eq_TypeName_eq in H0. subst.
        pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)).
        unfold cfun_sigs_in_dts in H0. rewrite Forall_forall in H0.
        rewrite in_map_iff in H. do 2 destruct H. apply H0 in H2.
        unfold QName in *. rewrite H in H2. cbn in H2. clear - H H1 H2 DefuncCdt2.
        rewrite filter_In in H1. destruct H1. unfold gfunsigs_filterfun_g in H1.
        destruct a. destruct s; try discriminate. rewrite eq_TypeName_eq in H1. subst.
        cbn in H2. clear - H2 DefuncCdt2.
        pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
        unfold dts_cdts_disjoint in H. unfold not in H. eapply H...
      }
      cbn. reflexivity.
    }
    match goal with [|- _ = _ _ (filter ?f ?l)] => replace (filter f l) with l end.
    2:{ clear. match goal with [|- _ _ (_ _ ?l) = _] => generalize l end. intros.
      induction l... cbn.
      case_eq (gfunsigs_filterfun_g tn a); intros...
      cbn. case_eq (eq_TypeName (fst (unscope (fst a))) tn); intros; try f_equal...
      exfalso. clear - H H0. unfold gfunsigs_filterfun_g in H.
      destruct a. destruct s; try discriminate.
      cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
    }
    rewrite map_map. cbn.
    match goal with [|- _ = _ _ (filter ?f ?l)] => replace (filter f l) with l end.
    2:{ clear. generalize (skeleton_gfun_sigs_g (program_skeleton p)). induction g...
      cbn. case_eq (eq_TypeName (fst (fst a)) tn); intros; unfold QName in *; rewrite H...
      cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
    }
    rewrite map_map. cbn. remember (program_gfun_bods_g p) as g.
    remember (skeleton_gfun_sigs_g (program_skeleton p)) as gs.
    assert (map fst gs = map fst g). { subst. apply program_has_all_gfun_bods_g. }
    clear - H H1. generalize dependent gs.
    induction g; intros; [ destruct gs; try discriminate; eauto | ].
    destruct gs; try discriminate. cbn in H1. inversion H1. cbn.
    unfold QName in *. rewrite H2. case_eq (eq_TypeName (fst (fst a)) tn); intros.
    * unfold QName in *. rewrite H0. cbn in *. rewrite H0 in H. inversion H; subst.
      cbn in *. f_equal...
    * unfold QName in *. rewrite H0. cbn in H. rewrite H0 in H...
- rewrite map_app. rewrite filter_app.
  unfold computeNewDatatype. unfold DefuncIII.new_gfun_bods_l.
  match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * gfun_bod)) end.
  2:{ rewrite map_map. cbn. match goal with [|- _ = _ _ (_ ?f (_ _ ?l))] =>
    generalize l end. clear. induction l; intros...
    cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    cbn. rewrite eq_TypeName_symm. rewrite H...
  }
  rewrite app_nil_r.
  rewrite filter_app. unfold Constructor.
  replace (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p)))
    with (@nil (ScopedName * list TypeName)).
  2:{ match goal with [|- _ = ?l] => case_eq l; intros end...
    clear - DefuncCdt H1. exfalso. pose proof (in_eq p0 l).
    rewrite <- H1 in H. clear H1. rewrite filter_In in H.
    destruct H. unfold not in DefuncCdt. eapply DefuncCdt... clear - H0.
    unfold gfunsigs_filterfun_l in H0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0; subst...
  }
  rewrite app_nil_r. rewrite filter_app. rewrite map_map. cbn.
  match goal with [|- _ = _ _ (_ _ (?l ++ _))] => replace l with (@nil (ScopedName * list TypeName)) end.
  2:{ clear. match goal with [|- _ = _ _ (_ _ ?l)] => generalize l end. induction l... }
  rewrite app_nil_l.
  match goal with [|- ?m = _] => rewrite combine_fst_snd with (ps:=m) end.
  change (fun x : ScopedName * gfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
    with (fun x : ScopedName * gfun_bod => (fun y => eq_TypeName (fst (unscope y)) tn) (fst x)).
  rewrite filter_map. rewrite map_map. cbn.
  match goal with [|- _ = ?m] => rewrite combine_fst_snd with (ps:=m) end.
  change (fun x : ScopedName * gfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
    with (fun x : ScopedName * gfun_bod => (fun y => eq_TypeName (fst (unscope y)) tn) (fst x)).
  rewrite filter_map. rewrite map_map. cbn.
  f_equal.
  + rewrite <- map_map with (g:=local). rewrite <- (program_has_all_gfun_bods_l p).
    unfold gfunsigs_filterfun_g. repeat rewrite <- filter_map.
    repeat rewrite map_map. cbn. f_equal. repeat rewrite filter_compose.
    apply filter_ext. intros. rewrite eq_TypeName_symm with (tn1:=tn).
    repeat rewrite andb_diag...
  + clear - H H0 DefuncCdt2. unfold DefuncIII.new_cfun_bods_g. unfold DefuncIII.new_cfun_bods_l.
    erewrite map_ext_in with (l:=filter (gfunsigs_filterfun_l tn) _).
    2:{ intros. erewrite map_ext_in with (l:=filter (cfunsigs_filterfun_g tn) _).
      2:{ intros.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H H2. generalize dependent (program_gfun_bods_g p). induction g...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H.
          replace ((global (fst a), snd a)::map (fun x => (global (fst x), snd x)) g)
            with ([(global (fst a), snd a)]++map (fun x => (global (fst x), snd x)) g) in H...
          rewrite filter_app in H. rewrite <- Forall_app_iff in H. destruct H.
          rewrite <- IHg...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct g...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction g...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold cfunsigs_filterfun_g in H1.
            destruct a0. destruct p0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H0 H2. generalize dependent (program_gfun_bods_l p). induction g...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H0.
          replace ((local (fst a), snd a)::map (fun x => (local (fst x), snd x)) g)
            with ([(local (fst a), snd a)]++map (fun x => (local (fst x), snd x)) g) in H0...
          rewrite filter_app in H0. rewrite <- Forall_app_iff in H0. destruct H0.
          rewrite <- IHg...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct g...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction g...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold cfunsigs_filterfun_g in H1.
            destruct a0. destruct p0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn. reflexivity.
      }
      erewrite map_ext_in with (l:=filter (cfunsigs_filterfun_l tn) _).
      2:{ intros.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H H2. generalize dependent (program_gfun_bods_g p). induction g...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H.
          replace ((global (fst a), snd a)::map (fun x => (global (fst x), snd x)) g)
            with ([(global (fst a), snd a)]++map (fun x => (global (fst x), snd x)) g) in H...
          rewrite filter_app in H. rewrite <- Forall_app_iff in H. destruct H.
          rewrite <- IHg...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct g...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction g...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold cfunsigs_filterfun_l in H1.
            destruct a0. destruct p0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H0 H2. generalize dependent (program_gfun_bods_l p). induction g...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H0.
          replace ((local (fst a), snd a)::map (fun x => (local (fst x), snd x)) g)
            with ([(local (fst a), snd a)]++map (fun x => (local (fst x), snd x)) g) in H0...
          rewrite filter_app in H0. rewrite <- Forall_app_iff in H0. destruct H0.
          rewrite <- IHg...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct g...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction g...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold cfunsigs_filterfun_l in H1.
            destruct a0. destruct p0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn. reflexivity.
      }
      repeat rewrite flat_map_app.
      match goal with [|- (_, _ _ (_ (_ (?l ++ _))) ++ _) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{ clear. generalize (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p))).
        intros. induction l...
      }
      cbn.
      match goal with [|- (_, _ ++ _ _ (_ (_ (?l ++ _)))) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{ clear. generalize (filter (cfunsigs_filterfun_l tn) (skeleton_dtors (program_skeleton p))).
        intros. induction l...
      }
      cbn.
      match goal with [|- (_, _ _ (_ ?l) ++ _) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{
        intros. clear - DefuncCdt2 H1. remember (program_cfun_bods_g p) as c.
        assert (Forall (fun x => In x (program_cfun_bods_g p)) c).
        { subst. rewrite Forall_forall... }
        clear - H DefuncCdt2 H1. induction c...
        inversion H; subst. cbn. rewrite filter_app. rewrite <- IHc...
        rewrite app_nil_r. clear - H3 H1 DefuncCdt2. destruct a0. cbn.
        assert (exists l, In (q, l++c) (program_cfun_bods_g p)). { exists []... }
        clear H3.
        induction c... cbn. destruct q. rewrite <- IHc.
        2:{ destruct H. exists (x++[a0]). rewrite <- app_assoc... }
        destruct a0. destruct s... cbn.
        case_eq (eq_TypeName t (fst (unscope (fst a)))); intros...
        exfalso. clear IHc. destruct H.
        apply (in_map fst) in H. cbn in H. rewrite <- (program_has_all_cfun_bods_g p) in H.
        rewrite eq_TypeName_eq in H0. subst.
        pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)).
        unfold cfun_sigs_in_dts in H0. rewrite Forall_forall in H0.
        rewrite in_map_iff in H. do 2 destruct H. apply H0 in H2.
        unfold QName in *. rewrite H in H2. cbn in H2. clear - H H1 H2 DefuncCdt2.
        rewrite filter_In in H1. destruct H1. unfold gfunsigs_filterfun_l in H1.
        destruct a. destruct s; try discriminate. rewrite eq_TypeName_eq in H1. subst.
        cbn in H2. clear - H2 DefuncCdt2.
        pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
        unfold dts_cdts_disjoint in H. unfold not in H. eapply H...
      }
      cbn.
      match goal with [|- (_, _ _ (_ ?l)) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{
        intros. clear - DefuncCdt2 H1. remember (program_cfun_bods_l p) as c.
        assert (Forall (fun x => In x (program_cfun_bods_l p)) c).
        { subst. rewrite Forall_forall... }
        clear - H DefuncCdt2 H1. induction c...
        inversion H; subst. cbn. rewrite filter_app. rewrite <- IHc...
        rewrite app_nil_r. clear - H3 H1 DefuncCdt2. destruct a0. cbn.
        assert (exists l, In (q, l++c) (program_cfun_bods_l p)). { exists []... }
        clear H3.
        induction c... cbn. destruct q. rewrite <- IHc.
        2:{ destruct H. exists (x++[a0]). rewrite <- app_assoc... }
        destruct a0. destruct s... cbn.
        case_eq (eq_TypeName t (fst (unscope (fst a)))); intros...
        exfalso. clear IHc. destruct H.
        apply (in_map fst) in H. cbn in H. rewrite <- (program_has_all_cfun_bods_l p) in H.
        rewrite eq_TypeName_eq in H0. subst.
        pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)).
        unfold cfun_sigs_in_dts in H0. rewrite Forall_forall in H0.
        rewrite in_map_iff in H. do 2 destruct H. apply H0 in H2.
        unfold QName in *. rewrite H in H2. cbn in H2. clear - H H1 H2 DefuncCdt2.
        rewrite filter_In in H1. destruct H1. unfold gfunsigs_filterfun_l in H1.
        destruct a. destruct s; try discriminate. rewrite eq_TypeName_eq in H1. subst.
        cbn in H2. clear - H2 DefuncCdt2.
        pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
        unfold dts_cdts_disjoint in H. unfold not in H. eapply H...
      }
      cbn. reflexivity.
    }
    match goal with [|- _ = _ _ (filter ?f ?l)] => replace (filter f l) with l end.
    2:{ clear. match goal with [|- _ _ (_ _ ?l) = _] => generalize l end. intros.
      induction l... cbn.
      case_eq (gfunsigs_filterfun_l tn a); intros...
      cbn. case_eq (eq_TypeName (fst (unscope (fst a))) tn); intros; try f_equal...
      exfalso. clear - H H0. unfold gfunsigs_filterfun_l in H.
      destruct a. destruct s; try discriminate.
      cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
    }
    rewrite map_map. cbn.
    match goal with [|- _ = _ _ (filter ?f ?l)] => replace (filter f l) with l end.
    2:{ clear. generalize (skeleton_gfun_sigs_l (program_skeleton p)). induction g...
      cbn. case_eq (eq_TypeName (fst (fst a)) tn); intros; unfold QName in *; rewrite H...
      cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
    }
    rewrite map_map. cbn. remember (program_gfun_bods_l p) as g.
    remember (skeleton_gfun_sigs_l (program_skeleton p)) as gs.
    assert (map fst gs = map fst g). { subst. apply program_has_all_gfun_bods_l. }
    clear - H0 H1. generalize dependent gs.
    induction g; intros; [ destruct gs; try discriminate; eauto | ].
    destruct gs; try discriminate. cbn in H1. inversion H1. cbn.
    unfold QName in *. rewrite H2. case_eq (eq_TypeName (fst (fst a)) tn); intros.
    * unfold QName in *. rewrite H. cbn in *. rewrite H in H0. inversion H0; subst.
      cbn in *. f_equal...
    * unfold QName in *. rewrite H. cbn in H0. rewrite H in H0...
Qed.

Corollary derefunc_preserves_gfuns_aux :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton (defunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (* Necessary in case of empty codatatype to make sure no datatypes are defunc.ed. *)
  (DefuncCdt : forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn)
  (DefuncCdt2 : In tn (skeleton_cdts (program_skeleton p))),
  pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_gfun_bods_for_type tn p = program_gfun_bods_for_type tn pr2.
Proof with eauto.
intros.
case_eq (program_gfun_bods_for_type tn p); intros.
- unfold program_gfun_bods_for_type in *. subst. cbn.
  rewrite <- app_nil_r with (l:=[]). rewrite filter_app. f_equal.
  + rewrite <- app_nil_r with (l:=[]). rewrite map_app. rewrite filter_app. f_equal.
    * rewrite filter_app. rewrite map_app. rewrite map_app. rewrite filter_app.
      match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * gfun_bod)) end.
      2:{ rewrite map_map. match goal with [|- _ = _ _ (_ _ ?l)] => replace l with (@nil (ScopedName * list TypeName)) end...
        clear - DefuncCdt. generalize dependent (skeleton_ctors (program_skeleton p)). induction c; intros...
        cbn. unfold gfunsigs_filterfun_g in *. destruct a. destruct s.
        - apply IHc. intros. apply DefuncCdt. right...
        - case_eq (eq_TypeName tn (fst q)); intros.
          + exfalso. unfold not in DefuncCdt. apply DefuncCdt with (c0:=(global q, l)); [left|]... cbn.
            rewrite eq_TypeName_eq in H...
          + apply IHc. intros. apply DefuncCdt. right...
      }
      rewrite app_nil_r.
      match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => replace l with (@nil (ScopedName * list TypeName)) end...
      clear - H1. unfold computeNewDatatype. rewrite filter_app.
      unfold gfunsigs_filterfun_g.
      match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * list TypeName)) end.
      2:{ clear. match goal with [|- _ = _ (_ _ ?l)] => generalize l end. intros. induction l... }
      rewrite app_nil_r.
      match goal with [|- _ = filter ?f ?l] => replace (filter f l) with l end.
      2:{ generalize (skeleton_gfun_sigs_g (program_skeleton p)). induction g...
        cbn. case_eq (eq_TypeName (fst (fst a)) tn); intros; unfold QName in *; rewrite H...
        cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
      }
      rewrite filter_app in H1. apply app_eq_nil in H1. destruct H1 as [H1 _].
      assert (forall {A B} (l : list A) (f : A -> B), map f l = [] -> l = []).
      { induction l; intros... cbn in H. discriminate. }
      symmetry. apply H with (f:=fun x => unscope (fst x)). clear H. rewrite map_map. cbn.
      apply (f_equal (map (fun x => unscope (fst x)))) in H1. rewrite <- filter_map in H1.
      rewrite map_map in H1. cbn in H1.
      erewrite filter_ext.
      { rewrite filter_map. erewrite filter_ext in H1.
        { rewrite filter_map in H1. rewrite program_has_all_gfun_bods_g. apply H1. }
        intros. destruct a. cbn. destruct q. cbn. instantiate (1:=fun x => eq_TypeName (fst x) tn)...
      }
      intros...
    * rewrite map_map. cbn. clear. unfold DefuncIII.new_gfun_bods_g.
      match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end. induction l...
      cbn. destruct a. case_eq (negb (eq_TypeName tn (fst q))); intros...
      cbn. rewrite negb_true_iff in H. rewrite eq_TypeName_symm in H. rewrite H...
  + rewrite <- app_nil_r with (l:=[]). rewrite map_app. rewrite filter_app. f_equal.
    * rewrite filter_app. rewrite map_app. rewrite map_app. rewrite filter_app.
      match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * gfun_bod)) end.
      2:{ rewrite map_map. match goal with [|- _ = _ _ (_ _ ?l)] => replace l with (@nil (ScopedName * list TypeName)) end...
        clear - DefuncCdt. generalize dependent (skeleton_ctors (program_skeleton p)). induction c; intros...
        cbn. unfold gfunsigs_filterfun_l in *. destruct a. destruct s.
        - case_eq (eq_TypeName tn (fst q)); intros.
          + exfalso. unfold not in DefuncCdt. apply DefuncCdt with (c0:=(local q, l)); [left|]... cbn.
            rewrite eq_TypeName_eq in H...
          + apply IHc. intros. apply DefuncCdt. right...
        - apply IHc. intros. apply DefuncCdt. right...
      }
      rewrite app_nil_r.
      match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => replace l with (@nil (ScopedName * list TypeName)) end...
      clear - H1. unfold computeNewDatatype. rewrite filter_app.
      unfold gfunsigs_filterfun_l.
      match goal with [|- _ = ?l ++ _] => replace l with (@nil (ScopedName * list TypeName)) end.
      2:{ clear. match goal with [|- _ = _ (_ _ ?l)] => generalize l end. intros. induction l... }
      cbn.
      match goal with [|- _ = filter ?f ?l] => replace (filter f l) with l end.
      2:{ generalize (skeleton_gfun_sigs_l (program_skeleton p)). induction g...
        cbn. case_eq (eq_TypeName (fst (fst a)) tn); intros; unfold QName in *; rewrite H...
        cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
      }
      rewrite filter_app in H1. apply app_eq_nil in H1. destruct H1 as [_ H1].
      assert (forall {A B} (l : list A) (f : A -> B), map f l = [] -> l = []).
      { induction l; intros... cbn in H. discriminate. }
      symmetry. apply H with (f:=fun x => unscope (fst x)). clear H. rewrite map_map. cbn.
      apply (f_equal (map (fun x => unscope (fst x)))) in H1. rewrite <- filter_map in H1.
      rewrite map_map in H1. cbn in H1.
      erewrite filter_ext.
      { rewrite filter_map. erewrite filter_ext in H1.
        { rewrite filter_map in H1. rewrite program_has_all_gfun_bods_l. apply H1. }
        intros. destruct a. cbn. destruct q. cbn. instantiate (1:=fun x => eq_TypeName (fst x) tn)...
      }
      intros...
    * rewrite map_map. cbn. clear. unfold DefuncIII.new_gfun_bods_l.
      match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end. induction l...
      cbn. destruct a. case_eq (negb (eq_TypeName tn (fst q))); intros...
      cbn. rewrite negb_true_iff in H. rewrite eq_TypeName_symm in H. rewrite H...
- case_eq (snd p0); intros.
  { eapply derefunc_preserves_gfuns_empty_dtors... }

  assert (program_gfun_bods_for_type tn p <> []).
  { unfold not. intros. rewrite H3 in H1. discriminate. }
  rewrite <- H1.
  eapply derefunc_preserves_gfuns_nonempty...
  { clear - H1 H2. cbn. unfold program_gfun_bods_for_type in H1.
    rewrite filter_app in H1. pose proof (in_eq p0 l) as InAux.
    rewrite <- H1 in InAux. rename H2 into p0Eq. clear - p0Eq InAux.
    apply in_app_or in InAux.
    pose proof (program_gfun_bods_typecheck_g p) as TypG.
    pose proof (program_gfun_bods_typecheck_l p) as TypL.
    unfold gfun_bods_g_typecheck in TypG.
    unfold gfun_bods_l_typecheck in TypL. rewrite Forall_forall in *.
    destruct InAux; rewrite filter_In in H; destruct H as [H_1 H_2];
      rewrite in_map_iff in H_1; destruct H_1 as [H_1_1 [H_1_2 H_1_3]];
      [ apply TypG in H_1_3 | apply TypL in H_1_3 ];
      clear TypG; clear TypL; destruct H_1_3 as [qn [args [_ Typ]]];
      destruct H_1_1 as [qn' bod]; subst; cbn in *; subst;
      rewrite eq_TypeName_eq in H_2; subst; inversion Typ; subst;
      apply listTypeDeriv'_lemma in H8; rewrite Nat.eqb_eq in H8;
      clear - H6 H8; unfold lookup_dtors in H6;
      case_eq (filter (eq_TypeName (fst qn')) (skeleton_cdts (program_skeleton p)));
      intros; rewrite H in H6; try discriminate; inversion H6; subst;
      clear - H8; repeat rewrite map_length in H8;
      match goal with [_ : _ ?l = _ |- _] =>
        case_eq l; intros; rewrite H in H8; try discriminate end;
      clear - H; pose proof (in_eq p0 l); rewrite <- H in H0; clear H;
      do 2 destruct p0; destruct s;
      try solve [
      assert (In (local q, l0, t) (filter (cfunsigs_filterfun_l (fst qn'))
        (skeleton_dtors (program_skeleton p))));
      [ unfold cfunsigs_filterfun_l; rewrite filter_In in *;
        destruct H0; split; eauto; rewrite eq_TypeName_symm; eauto | ];
      apply in_split in H; do 2 destruct H; unfold DefuncIII.new_cfun_bods_l;
      rewrite H; apply not_eq_sym; repeat rewrite map_app; cbn;
      repeat rewrite filter_app; cbn;
      assert (eq_TypeName (fst q) (fst qn') = true);
      [ rewrite filter_In in H0; destruct H0; eauto | ];
      rewrite H1; rewrite app_assoc;
      match goal with [|- [] <> _ ++ ?l'] => case_eq l'; intros end;
        [| apply app_cons_not_nil ];
      rewrite app_nil_r; rewrite app_assoc; apply app_cons_not_nil
      ];
      try solve
      [
      assert (In (global q, l0, t) (filter (cfunsigs_filterfun_g (fst qn'))
        (skeleton_dtors (program_skeleton p))));
      [ unfold cfunsigs_filterfun_g; rewrite filter_In in *;
        destruct H0; split; eauto; rewrite eq_TypeName_symm; eauto | ];
      apply in_split in H; do 2 destruct H; unfold DefuncIII.new_cfun_bods_g;
      rewrite H; apply not_eq_sym; repeat rewrite map_app; cbn;
      repeat rewrite filter_app; cbn;
      repeat rewrite filter_app; cbn;
      assert (eq_TypeName (fst q) (fst qn') = true);
      [ rewrite filter_In in H0; destruct H0; eauto | ];
      rewrite H1;
      match goal with [|- [] <> _ ++ ?l'] => case_eq l'; intros end;
        [| apply app_cons_not_nil ]; rewrite app_nil_r;
      match goal with [|- [] <> _ ++ ?l'] => case_eq l'; intros end;
        [| apply app_cons_not_nil ]; rewrite app_nil_r;
      apply app_cons_not_nil
      ].
  }
  { clear - H1 H2. intros. unfold not. intros. subst.
    apply (in_map (map fst)) in H.
    pose proof (in_eq p0 l). rewrite <- H1 in H0.
    apply (in_map snd) in H0. apply (in_map (map fst)) in H0.
    rewrite H2 in H0.
    pose proof (same_dtors _ _ _ _ H H0). discriminate.
  }
Qed.

Lemma defunc_cdt_aux : forall p tn,
  In tn (skeleton_cdts (program_skeleton p)) ->
  (forall c, In c (skeleton_ctors (program_skeleton p)) -> fst (unscope (fst c)) <> tn).
Proof with eauto.
intros. pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)).
unfold dts_ctors_in_dts in H1. rewrite Forall_forall in H1.
apply H1 in H0. clear H1.
pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
unfold dts_cdts_disjoint in H1. unfold not in *. intros. subst.
eapply H1...
Qed.


Corollary redefunc_preserves_cfuns_nonempty :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton (refunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (Nonempty : program_cfun_bods_for_type tn p <> [])
  (NonemptyGfuns : program_gfun_bods_for_type tn (refunctionalize_program p tn P1 P2 P3 P4 P5) <> [])
  (NonemptyCtors : forall x, In x (map snd (program_cfun_bods_for_type tn p)) -> x <> [])
  (RefuncDt : forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn)
  (RefuncDt2 : In tn (skeleton_dts (program_skeleton p))),
  pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_cfun_bods_for_type tn p = program_cfun_bods_for_type tn pr2.
Proof with eauto.
intros. subst. symmetry. erewrite defunc_is_matrix_transpose'... erewrite refunc_is_matrix_transpose'...
match goal with [|- map _ (_ (_ (_ (_ ?l)))) = _] => case_eq (snd l); intros end.
{ case_eq (program_cfun_bods_for_type tn p); intros...
  rewrite H0 in H.
  match goal with [_ : ?l' = [] |- _] => assert (l' <> []) end.
  { generalize dependent (p0::l). clear - Nonempty NonemptyCtors.
    intros. rewrite H0 in *. clear H H0.
    assert (exists l' x, l = l'++[x]).
    { clear - Nonempty. induction l.
      - exfalso. apply Nonempty...
      - destruct l.
        + exists []. exists a...
        + assert (p::l <> []). { unfold not. intros. discriminate. }
          pose proof (IHl H). do 2 destruct H0. exists (a::x). exists x0.
          rewrite H0...
    }
    do 2 destruct H. subst l. clear Nonempty. rename x into l. cbn.
    match goal with [|- _ _ ?len <> _] => assert (exists len', len = S len') end.
    { destruct l.
      - cbn in NonemptyCtors. specialize NonemptyCtors with (x:=snd x0).
        pose proof (NonemptyCtors (or_introl eq_refl)). destruct x0. destruct c.
        + exfalso. apply H...
        + cbn. eexists...
      - cbn in *. specialize NonemptyCtors with (x:=snd p0).
        pose proof (NonemptyCtors (or_introl eq_refl)). destruct p0. destruct c.
        + exfalso. apply H...
        + cbn. eexists...
    }
    destruct H. rewrite H. generalize x. clear H.
    induction l; intros.
    - cbn. destruct x0. cbn. destruct c.
      + cbn in *. exfalso. specialize NonemptyCtors with (x:=[]).
        cut ((@nil (ScopedName * expr)) <> []).
        * intros. apply H...
        * apply NonemptyCtors. left...
      + cbn. unfold not. intros. discriminate.
    - cbn. destruct a. cbn. destruct c.
      + cbn. exfalso. specialize NonemptyCtors with (x:=[]).
        cut ((@nil (ScopedName * expr)) <> []).
        * intros. apply H...
        * apply NonemptyCtors. left...
      + cbn in *. unfold not. intros.
        match goal with [_ : _ _ ?l' = [] |- _] => case_eq l'; intros end.
        2:{ rewrite H0 in H. cbn in H. discriminate. }
        unfold not in IHl. eapply IHl...
        intros. clear IHl H. subst.
        pose proof (NonemptyCtors [] (or_intror H1)). apply H...
  }
  rewrite H in H1. exfalso. apply H1...
}
rewrite read_cfuns_from_into_matrix.
2:{ rewrite H. unfold not. intros. discriminate. }
2:{ remember (program_cfun_bods_for_type tn p) as l1. clear - Heql1 NonemptyCtors. cbn.
  match goal with [|- _ (match ?m' with | [] => _ | _ => _ end) = _] => remember m' as m end.
  assert (forall x : cfun_bod, In x (map snd m) -> x <> []).
  { intros. subst m. rewrite map_map in H. cbn in H.
    rewrite in_map_iff in H. do 2 destruct H. subst x. apply (in_map snd) in H0.
    apply NonemptyCtors in H0. unfold not. intros. apply H0. destruct (snd x0)...
    cbn in H. discriminate.
  }
  assert (forall x1 x2, In x1 (map snd m) -> In x2 (map snd m) -> map fst x1 = map fst x2).
  { subst m. repeat rewrite map_map. cbn. intros.
    rewrite in_map_iff in *. destruct H0 as [H0_x [H0_eq H0]]. destruct H1 as [H1_x [H1_eq H1]].
    apply (f_equal (map fst)) in H0_eq. apply (f_equal (map fst)) in H1_eq.
    rewrite map_map in *. cbn in *. rewrite <- H0_eq. rewrite <- H1_eq. subst l1. clear - H0 H1.
    apply (in_map snd) in H0. apply (in_map snd) in H1.
    apply (in_map (map fst)) in H0. apply (in_map (map fst)) in H1.
    eapply same_ctors...
  }
  clear Heqm NonemptyCtors Heql1 l1.
  match goal with [|- ?n' = _] => remember n' as n end.
  generalize dependent n.
  induction m; intros; cbn; try rewrite repeat_length...
  case_eq (map snd (snd a)); intros.
  - unfold cfun_bod. rewrite H1.
    rewrite map_length in Heqn. subst. apply (f_equal (@length _)) in H1. rewrite map_length in H1...
  - unfold cfun_bod. rewrite H1. unfold map_with_index. rewrite map_with_index'_length.
    destruct m.
    + cbn. rewrite repeat_length...
    + apply IHm.
      * intros. apply H. cbn. right...
      * intros. eapply H0; cbn; right...
      * subst n. clear - H H0. cbn [map] in H0. pose proof (in_eq (snd a) (map snd m)).
        assert (In (snd p0) (snd a :: map snd (p0 :: m))). { right. left... }
        f_equal. apply H0... left...
}
2:{ intros. cbn. rewrite map_map. rewrite map_length. cbn in H0.
  repeat rewrite map_map in H0. cbn in H0. erewrite map_ext in H0.
  2:{ intros. rewrite map_map. cbn. reflexivity. }
  clear - H0.
  match goal with [_ : In _ (_ _ ?len) |- _] => generalize dependent len end.
  generalize dependent (program_cfun_bods_for_type tn p).
  generalize dependent l'. intros l' l. generalize l'. clear l'.
  induction l; intros.
  - cbn in H0. apply repeat_spec in H0. subst...
  - cbn in H0. case_eq (snd a); intros.
    + unfold cfun_bod in *. rewrite H in H0. cbn in H0. exfalso...
    + unfold cfun_bod in *. rewrite H in H0. cbn in H0.
      apply in_map_with_index_if in H0.
      destruct H0 as [H0_x [H0_n [H0_eq H0]]].
      destruct l'; try discriminate.
      cbn. f_equal. eapply IHl. inversion H0_eq; subst. apply H0.
}
clear H.
rewrite transpose_transpose.
2:{ simpl. repeat rewrite map_map. repeat rewrite map_length... }
2:{ rewrite Forall_forall. intros. clear - H. simpl in *.
  case_eq (program_cfun_bods_for_type tn p); intros.
  - rewrite H0 in H. simpl in H. exfalso...
  - simpl. repeat rewrite map_map in H. simpl in H. erewrite map_ext in H.
    2:{ intros. rewrite map_map. simpl. reflexivity. }
    rewrite map_map. simpl. rewrite in_map_iff in H. do 2 destruct H. subst.
    repeat rewrite map_length. pose proof (in_eq p0 l). rewrite <- H0 in H.
    apply (in_map snd) in H. apply (in_map snd) in H1.
    apply (in_map (map fst)) in H. apply (in_map (map fst)) in H1.
    repeat rewrite <- map_length with (f:=fst).
    erewrite same_ctors with (cfd1:=map fst (snd x0))...
}
rewrite read_cfuns_into_from_matrix.
- rewrite map_map. simpl. rewrite combine_fst_snd at 1. rewrite map_map. simpl.
  rewrite combine_fst_snd. f_equal...
  rewrite map_map. simpl. erewrite map_ext_in.
  2:{ intros. rewrite map_map. simpl. erewrite map_ext_in.
    2:{ intros. rewrite surjective_pairing with (p:=a0) in H0. rewrite surjective_pairing with (p:=a) in H.
      erewrite redefunc_helper_inverse... rewrite <- surjective_pairing. instantiate (1:=id). unfold id... }
    reflexivity.
  }
  apply map_ext. intros. rewrite map_id...
- intros. apply same_ctors with (p:=p) (tn:=tn).
  + rewrite in_map_iff in H. do 2 destruct H. destruct cfb1. inversion H; subst. simpl.
    rewrite map_map. simpl. apply in_map. apply in_map...
  + rewrite in_map_iff in H0. do 2 destruct H0. destruct cfb2. inversion H0; subst. simpl.
    rewrite map_map. simpl. apply in_map. apply in_map...
Qed.

Lemma redefunc_preserves_cfuns_empty_ctors :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (RefuncDt : forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn)
  (RefuncDt2 : In tn (skeleton_dts (program_skeleton p)))
  (H : pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5)
  (H0 : pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5')
  (p0 : ScopedName * cfun_bod)
  (l : list (ScopedName * cfun_bod))
  (H1 : program_cfun_bods_for_type tn p = p0 :: l)
  (H2 : snd p0 = []),
  p0 :: l = program_cfun_bods_for_type tn pr2.
Proof with eauto.
intros.
assert (Forall (fun x => snd x = []) l).
{ clear - H1 H2. rewrite Forall_forall. intros.
  assert (In x (p0::l)). { right... }
  apply (in_map snd) in H0.
  case_eq (snd x)... intros. rewrite H3 in H0.
  pose proof (in_eq p0 l). rewrite <- H1 in H4. rewrite <- H1 in H0.
  apply (in_map snd) in H4. apply (in_map (map fst)) in H4.
  apply (in_map (map fst)) in H0.
  pose proof (same_ctors _ _ _ _ H4 H0). rewrite H2 in H5. discriminate.
}

assert (Forall (fun x => snd x = []) (p0::l)). { constructor... }
clear H3 H2. rewrite <- H1 in *. clear H1. subst.
clear - H4 RefuncDt RefuncDt2.
unfold program_cfun_bods_for_type in H4. rewrite filter_app in H4.
rewrite <- Forall_app_iff in H4. destruct H4.

cbn. rewrite filter_app. unfold program_cfun_bods_for_type. rewrite filter_app.
f_equal.
- rewrite map_app. rewrite filter_app.
  unfold computeNewCoDatatype. unfold RefuncIII.new_cfun_bods_g.
  match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * cfun_bod)) end.
  2:{ rewrite map_map. cbn. match goal with [|- _ = _ _ (_ ?f (_ _ ?l))] =>
    generalize l end. clear. induction l; intros...
    cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    cbn. rewrite eq_TypeName_symm. rewrite H...
  }
  rewrite app_nil_r.
  rewrite filter_app. unfold Destructor.
  replace (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p)))
    with (@nil (ScopedName * list TypeName * TypeName)).
  2:{ match goal with [|- _ = ?l] => case_eq l; intros end...
    clear - RefuncDt H1. exfalso. pose proof (in_eq p0 l).
    rewrite <- H1 in H. clear H1. rewrite filter_In in H.
    destruct H. unfold not in RefuncDt. eapply RefuncDt... clear - H0.
    unfold cfunsigs_filterfun_g in H0. destruct p0. destruct p. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0; subst...
  }
  rewrite app_nil_r. rewrite filter_app. rewrite map_map. cbn.
  match goal with [|- _ = _ _ (_ _ (_ ++ ?l))] => replace l with (@nil (ScopedName * list TypeName * TypeName)) end.
  2:{ clear. match goal with [|- _ = _ _ (_ _ ?l)] => generalize l end. induction l... }
  rewrite app_nil_r.
  match goal with [|- ?m = _] => rewrite combine_fst_snd with (ps:=m) end.
  change (fun x : ScopedName * cfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
    with (fun x : ScopedName * cfun_bod => (fun y => eq_TypeName (fst (unscope y)) tn) (fst x)).
  rewrite filter_map. rewrite map_map. cbn.
  match goal with [|- _ = ?m] => rewrite combine_fst_snd with (ps:=m) end.
  change (fun x : ScopedName * cfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
    with (fun x : ScopedName * cfun_bod => (fun y => eq_TypeName (fst (unscope y)) tn) (fst x)).
  rewrite filter_map. rewrite map_map. cbn.
  f_equal.
  + rewrite <- map_map with (g:=global). rewrite <- (program_has_all_cfun_bods_g p).
    unfold cfunsigs_filterfun_g. repeat rewrite <- filter_map.
    repeat rewrite map_map. cbn. f_equal. repeat rewrite filter_compose.
    apply filter_ext. intros. rewrite eq_TypeName_symm with (tn1:=tn).
    repeat rewrite andb_diag...
  + clear - H H0 RefuncDt2. unfold RefuncIII.new_gfun_bods_g. unfold RefuncIII.new_gfun_bods_l.
    erewrite map_ext_in with (l:=filter (cfunsigs_filterfun_g tn) _).
    2:{ intros. erewrite map_ext_in with (l:=filter (gfunsigs_filterfun_g tn) _).
      2:{ intros.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H H2. generalize dependent (program_cfun_bods_g p). induction c...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H.
          replace ((global (fst a), snd a)::map (fun x => (global (fst x), snd x)) c)
            with ([(global (fst a), snd a)]++map (fun x => (global (fst x), snd x)) c) in H...
          rewrite filter_app in H. rewrite <- Forall_app_iff in H. destruct H.
          rewrite <- IHc...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct c...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction c...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold gfunsigs_filterfun_g in H1.
            destruct a0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H0 H2. generalize dependent (program_cfun_bods_l p). induction c...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H0.
          replace ((local (fst a), snd a)::map (fun x => (local (fst x), snd x)) c)
            with ([(local (fst a), snd a)]++map (fun x => (local (fst x), snd x)) c) in H0...
          rewrite filter_app in H0. rewrite <- Forall_app_iff in H0. destruct H0.
          rewrite <- IHc...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct c...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction c...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold gfunsigs_filterfun_g in H1.
            destruct a0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn. reflexivity.
      }
      erewrite map_ext_in with (l:=filter (gfunsigs_filterfun_l tn) _).
      2:{ intros.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H H2. generalize dependent (program_cfun_bods_g p). induction c...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H.
          replace ((global (fst a), snd a)::map (fun x => (global (fst x), snd x)) c)
            with ([(global (fst a), snd a)]++map (fun x => (global (fst x), snd x)) c) in H...
          rewrite filter_app in H. rewrite <- Forall_app_iff in H. destruct H.
          rewrite <- IHc...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct c...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction c...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold gfunsigs_filterfun_l in H1.
            destruct a0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H0 H2. generalize dependent (program_cfun_bods_l p). induction c...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H0.
          replace ((local (fst a), snd a)::map (fun x => (local (fst x), snd x)) c)
            with ([(local (fst a), snd a)]++map (fun x => (local (fst x), snd x)) c) in H0...
          rewrite filter_app in H0. rewrite <- Forall_app_iff in H0. destruct H0.
          rewrite <- IHc...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct c...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction c...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold gfunsigs_filterfun_l in H1.
            destruct a0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn. reflexivity.
      }
      repeat rewrite flat_map_app.
      match goal with [|- (_, _ _ (_ (_ (?l ++ _))) ++ _) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{ clear. generalize (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))).
        intros. induction l...
      }
      cbn.
      match goal with [|- (_, _ ++ _ _ (_ (_ (?l ++ _)))) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{ clear. generalize (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))).
        intros. induction l...
      }
      cbn.
      match goal with [|- (_, _ _ (_ ?l) ++ _) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{
        intros. clear - RefuncDt2 H1. remember (program_gfun_bods_g p) as g.
        assert (Forall (fun x => In x (program_gfun_bods_g p)) g).
        { subst. rewrite Forall_forall... }
        clear - H RefuncDt2 H1. induction g...
        inversion H; subst. cbn. rewrite filter_app. rewrite <- IHg...
        rewrite app_nil_r. clear - H3 H1 RefuncDt2. destruct a0. cbn.
        assert (exists l, In (q, l++g) (program_gfun_bods_g p)). { exists []... }
        clear H3.
        induction g... cbn. destruct q. rewrite <- IHg.
        2:{ destruct H. exists (x++[a0]). rewrite <- app_assoc... }
        destruct a0. destruct s... cbn.
        case_eq (eq_TypeName t (fst (unscope (fst (fst a))))); intros...
        exfalso. clear IHg. destruct H.
        apply (in_map fst) in H. cbn in H. rewrite <- (program_has_all_gfun_bods_g p) in H.
        rewrite eq_TypeName_eq in H0. subst.
        pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)).
        unfold gfun_sigs_in_cdts in H0. rewrite Forall_forall in H0.
        rewrite in_map_iff in H. do 2 destruct H. apply H0 in H2.
        unfold QName in *. rewrite H in H2. cbn in H2. clear - H H1 H2 RefuncDt2.
        rewrite filter_In in H1. destruct H1. unfold cfunsigs_filterfun_g in H1.
        destruct a. destruct p0. destruct s; try discriminate. rewrite eq_TypeName_eq in H1. subst.
        cbn in H2. clear - H2 RefuncDt2.
        pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
        unfold dts_cdts_disjoint in H. unfold not in H. eapply H...
      }
      cbn.
      match goal with [|- (_, _ _ (_ ?l)) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{
        intros. clear - RefuncDt2 H1. remember (program_gfun_bods_l p) as g.
        assert (Forall (fun x => In x (program_gfun_bods_l p)) g).
        { subst. rewrite Forall_forall... }
        clear - H RefuncDt2 H1. induction g...
        inversion H; subst. cbn. rewrite filter_app. rewrite <- IHg...
        rewrite app_nil_r. clear - H3 H1 RefuncDt2. destruct a0. cbn.
        assert (exists l, In (q, l++g) (program_gfun_bods_l p)). { exists []... }
        clear H3.
        induction g... cbn. destruct q. rewrite <- IHg.
        2:{ destruct H. exists (x++[a0]). rewrite <- app_assoc... }
        destruct a0. destruct s... cbn.
        case_eq (eq_TypeName t (fst (unscope (fst (fst a))))); intros...
        exfalso. clear IHg. destruct H.
        apply (in_map fst) in H. cbn in H. rewrite <- (program_has_all_gfun_bods_l p) in H.
        rewrite eq_TypeName_eq in H0. subst.
        pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)).
        unfold gfun_sigs_in_cdts in H0. rewrite Forall_forall in H0.
        rewrite in_map_iff in H. do 2 destruct H. apply H0 in H2.
        unfold QName in *. rewrite H in H2. cbn in H2. clear - H H1 H2 RefuncDt2.
        rewrite filter_In in H1. destruct H1. unfold cfunsigs_filterfun_g in H1.
        destruct a. destruct p0. destruct s; try discriminate. rewrite eq_TypeName_eq in H1. subst.
        cbn in H2. clear - H2 RefuncDt2.
        pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
        unfold dts_cdts_disjoint in H. unfold not in H. eapply H...
      }
      cbn. reflexivity.
    }
    match goal with [|- _ = _ _ (filter ?f ?l)] => replace (filter f l) with l end.
    2:{ clear. match goal with [|- _ _ (_ _ ?l) = _] => generalize l end. intros.
      induction l... cbn.
      case_eq (cfunsigs_filterfun_g tn a); intros...
      cbn. case_eq (eq_TypeName (fst (unscope (fst (fst a)))) tn); intros; try f_equal...
      exfalso. clear - H H0. unfold cfunsigs_filterfun_g in H.
      destruct a. destruct p. destruct s; try discriminate.
      cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
    }
    rewrite map_map. cbn.
    match goal with [|- _ = _ _ (filter ?f ?l)] => replace (filter f l) with l end.
    2:{ clear. generalize (skeleton_cfun_sigs_g (program_skeleton p)). induction c...
      cbn. case_eq (eq_TypeName (fst (fst (fst a))) tn); intros; unfold QName in *; rewrite H...
      cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
    }
    rewrite map_map. cbn. remember (program_cfun_bods_g p) as c.
    remember (skeleton_cfun_sigs_g (program_skeleton p)) as cs.
    assert (map fst (map fst cs) = map fst c). { subst. rewrite map_map. apply program_has_all_cfun_bods_g. }
    clear - H H1. generalize dependent cs.
    induction c; intros; [ destruct cs; try discriminate; eauto | ].
    destruct cs; try discriminate. cbn in H1. inversion H1. cbn.
    unfold QName in *. rewrite H2. case_eq (eq_TypeName (fst (fst a)) tn); intros.
    * unfold QName in *. rewrite H0. cbn in *. rewrite H0 in H. inversion H; subst.
      cbn in *. f_equal...
    * unfold QName in *. rewrite H0. cbn in H. rewrite H0 in H...
- rewrite map_app. rewrite filter_app.
  unfold computeNewCoDatatype. unfold RefuncIII.new_cfun_bods_l.
  match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * cfun_bod)) end.
  2:{ rewrite map_map. cbn. match goal with [|- _ = _ _ (_ ?f (_ _ ?l))] =>
    generalize l end. clear. induction l; intros...
    cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    cbn. rewrite eq_TypeName_symm. rewrite H...
  }
  rewrite app_nil_r.
  rewrite filter_app. unfold Destructor.
  replace (filter (cfunsigs_filterfun_l tn) (skeleton_dtors (program_skeleton p)))
    with (@nil (ScopedName * list TypeName * TypeName)).
  2:{ match goal with [|- _ = ?l] => case_eq l; intros end...
    clear - RefuncDt H1. exfalso. pose proof (in_eq p0 l).
    rewrite <- H1 in H. clear H1. rewrite filter_In in H.
    destruct H. unfold not in RefuncDt. eapply RefuncDt... clear - H0.
    unfold cfunsigs_filterfun_l in H0. destruct p0. destruct p. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0; subst...
  }
  rewrite app_nil_r. rewrite filter_app. rewrite map_map. cbn.
  match goal with [|- _ = _ _ (_ _ (?l ++ _))] => replace l with (@nil (ScopedName * list TypeName * TypeName)) end.
  2:{ clear. match goal with [|- _ = _ _ (_ _ ?l)] => generalize l end. induction l... }
  rewrite app_nil_l.
  match goal with [|- ?m = _] => rewrite combine_fst_snd with (ps:=m) end.
  change (fun x : ScopedName * cfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
    with (fun x : ScopedName * cfun_bod => (fun y => eq_TypeName (fst (unscope y)) tn) (fst x)).
  rewrite filter_map. rewrite map_map. cbn.
  match goal with [|- _ = ?m] => rewrite combine_fst_snd with (ps:=m) end.
  change (fun x : ScopedName * cfun_bod => eq_TypeName (fst (unscope (fst x))) tn)
    with (fun x : ScopedName * cfun_bod => (fun y => eq_TypeName (fst (unscope y)) tn) (fst x)).
  rewrite filter_map. rewrite map_map. cbn.
  f_equal.
  + rewrite <- map_map with (g:=local). rewrite <- (program_has_all_cfun_bods_l p).
    unfold cfunsigs_filterfun_g. repeat rewrite <- filter_map.
    repeat rewrite map_map. cbn. f_equal. repeat rewrite filter_compose.
    apply filter_ext. intros. rewrite eq_TypeName_symm with (tn1:=tn).
    repeat rewrite andb_diag...
  + clear - H H0 RefuncDt2. unfold RefuncIII.new_gfun_bods_g. unfold RefuncIII.new_gfun_bods_l.
    erewrite map_ext_in with (l:=filter (cfunsigs_filterfun_l tn) _).
    2:{ intros. erewrite map_ext_in with (l:=filter (gfunsigs_filterfun_g tn) _).
      2:{ intros.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H H2. generalize dependent (program_cfun_bods_g p). induction c...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H.
          replace ((global (fst a), snd a)::map (fun x => (global (fst x), snd x)) c)
            with ([(global (fst a), snd a)]++map (fun x => (global (fst x), snd x)) c) in H...
          rewrite filter_app in H. rewrite <- Forall_app_iff in H. destruct H.
          rewrite <- IHc...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct c...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction c...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold gfunsigs_filterfun_g in H1.
            destruct a0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H0 H2. generalize dependent (program_cfun_bods_l p). induction c...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H0.
          replace ((local (fst a), snd a)::map (fun x => (local (fst x), snd x)) c)
            with ([(local (fst a), snd a)]++map (fun x => (local (fst x), snd x)) c) in H0...
          rewrite filter_app in H0. rewrite <- Forall_app_iff in H0. destruct H0.
          rewrite <- IHc...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct c...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction c...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold gfunsigs_filterfun_g in H1.
            destruct a0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn. reflexivity.
      }
      erewrite map_ext_in with (l:=filter (gfunsigs_filterfun_l tn) _).
      2:{ intros.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H H2. generalize dependent (program_cfun_bods_g p). induction c...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H.
          replace ((global (fst a), snd a)::map (fun x => (global (fst x), snd x)) c)
            with ([(global (fst a), snd a)]++map (fun x => (global (fst x), snd x)) c) in H...
          rewrite filter_app in H. rewrite <- Forall_app_iff in H. destruct H.
          rewrite <- IHc...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct c...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction c...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold gfunsigs_filterfun_l in H1.
            destruct a0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn.
        replace (filter _ (flat_map _ _)) with (@nil (QName * (ScopedName * expr))).
        2:{ clear - H0 H2. generalize dependent (program_cfun_bods_l p). induction c...
          intros. cbn. rewrite filter_app.
          cbn - [filter] in H0.
          replace ((local (fst a), snd a)::map (fun x => (local (fst x), snd x)) c)
            with ([(local (fst a), snd a)]++map (fun x => (local (fst x), snd x)) c) in H0...
          rewrite filter_app in H0. rewrite <- Forall_app_iff in H0. destruct H0.
          rewrite <- IHc...
          clear - H H2. cbn in H. case_eq (eq_TypeName (fst (fst a)) tn); intros.
          - replace (filter _ _) with (@nil (QName * (ScopedName * expr)))...
            destruct a. cbn in *. rewrite H0 in H. clear H0. destruct c...
            inversion H. discriminate.
          - clear - H0 H2. destruct a. cbn. induction c...
            cbn. destruct q. destruct a. destruct s...
            cbn in *. rewrite filter_In in H2. destruct H2. unfold gfunsigs_filterfun_l in H1.
            destruct a0. destruct s; try discriminate.
            rewrite eq_TypeName_eq in *. subst. cbn. rewrite H0. cbn.
            rewrite app_nil_r in *...
        }
        cbn. reflexivity.
      }
      repeat rewrite flat_map_app.
      match goal with [|- (_, _ _ (_ (_ (?l ++ _))) ++ _) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{ clear. generalize (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))).
        intros. induction l...
      }
      cbn.
      match goal with [|- (_, _ ++ _ _ (_ (_ (?l ++ _)))) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{ clear. generalize (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))).
        intros. induction l...
      }
      cbn.
      match goal with [|- (_, _ _ (_ ?l) ++ _) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{
        intros. clear - RefuncDt2 H1. remember (program_gfun_bods_g p) as g.
        assert (Forall (fun x => In x (program_gfun_bods_g p)) g).
        { subst. rewrite Forall_forall... }
        clear - H RefuncDt2 H1. induction g...
        inversion H; subst. cbn. rewrite filter_app. rewrite <- IHg...
        rewrite app_nil_r. clear - H3 H1 RefuncDt2. destruct a0. cbn.
        assert (exists l, In (q, l++g) (program_gfun_bods_g p)). { exists []... }
        clear H3.
        induction g... cbn. destruct q. rewrite <- IHg.
        2:{ destruct H. exists (x++[a0]). rewrite <- app_assoc... }
        destruct a0. destruct s... cbn.
        case_eq (eq_TypeName t (fst (unscope (fst (fst a))))); intros...
        exfalso. clear IHg. destruct H.
        apply (in_map fst) in H. cbn in H. rewrite <- (program_has_all_gfun_bods_g p) in H.
        rewrite eq_TypeName_eq in H0. subst.
        pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)).
        unfold gfun_sigs_in_cdts in H0. rewrite Forall_forall in H0.
        rewrite in_map_iff in H. do 2 destruct H. apply H0 in H2.
        unfold QName in *. rewrite H in H2. cbn in H2. clear - H H1 H2 RefuncDt2.
        rewrite filter_In in H1. destruct H1. unfold cfunsigs_filterfun_l in H1.
        destruct a. destruct p0. destruct s; try discriminate. rewrite eq_TypeName_eq in H1. subst.
        cbn in H2. clear - H2 RefuncDt2.
        pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
        unfold dts_cdts_disjoint in H. unfold not in H. eapply H...
      }
      cbn.
      match goal with [|- (_, _ _ (_ ?l)) = _] =>
        replace l with (@nil (QName * (ScopedName * expr))) end.
      2:{
        intros. clear - RefuncDt2 H1. remember (program_gfun_bods_l p) as g.
        assert (Forall (fun x => In x (program_gfun_bods_l p)) g).
        { subst. rewrite Forall_forall... }
        clear - H RefuncDt2 H1. induction g...
        inversion H; subst. cbn. rewrite filter_app. rewrite <- IHg...
        rewrite app_nil_r. clear - H3 H1 RefuncDt2. destruct a0. cbn.
        assert (exists l, In (q, l++g) (program_gfun_bods_l p)). { exists []... }
        clear H3.
        induction g... cbn. destruct q. rewrite <- IHg.
        2:{ destruct H. exists (x++[a0]). rewrite <- app_assoc... }
        destruct a0. destruct s... cbn.
        case_eq (eq_TypeName t (fst (unscope (fst (fst a))))); intros...
        exfalso. clear IHg. destruct H.
        apply (in_map fst) in H. cbn in H. rewrite <- (program_has_all_gfun_bods_l p) in H.
        rewrite eq_TypeName_eq in H0. subst.
        pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)).
        unfold gfun_sigs_in_cdts in H0. rewrite Forall_forall in H0.
        rewrite in_map_iff in H. do 2 destruct H. apply H0 in H2.
        unfold QName in *. rewrite H in H2. cbn in H2. clear - H H1 H2 RefuncDt2.
        rewrite filter_In in H1. destruct H1. unfold cfunsigs_filterfun_l in H1.
        destruct a. destruct p0. destruct s; try discriminate. rewrite eq_TypeName_eq in H1. subst.
        cbn in H2. clear - H2 RefuncDt2.
        pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
        unfold dts_cdts_disjoint in H. unfold not in H. eapply H...
      }
      cbn. reflexivity.
    }
    match goal with [|- _ = _ _ (filter ?f ?l)] => replace (filter f l) with l end.
    2:{ clear. match goal with [|- _ _ (_ _ ?l) = _] => generalize l end. intros.
      induction l... cbn.
      case_eq (cfunsigs_filterfun_l tn a); intros...
      cbn. case_eq (eq_TypeName (fst (unscope (fst (fst a)))) tn); intros; try f_equal...
      exfalso. clear - H H0. unfold cfunsigs_filterfun_l in H.
      destruct a. destruct p. destruct s; try discriminate.
      cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
    }
    rewrite map_map. cbn.
    match goal with [|- _ = _ _ (filter ?f ?l)] => replace (filter f l) with l end.
    2:{ clear. generalize (skeleton_cfun_sigs_l (program_skeleton p)). induction c...
      cbn. case_eq (eq_TypeName (fst (fst (fst a))) tn); intros; unfold QName in *; rewrite H...
      cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
    }
    rewrite map_map. cbn. remember (program_cfun_bods_l p) as c.
    remember (skeleton_cfun_sigs_l (program_skeleton p)) as cs.
    assert (map fst (map fst cs) = map fst c). { subst. rewrite map_map. apply program_has_all_cfun_bods_l. }
    clear - H0 H1. generalize dependent cs.
    induction c; intros; [ destruct cs; try discriminate; eauto | ].
    destruct cs; try discriminate. cbn in H1. inversion H1. cbn.
    unfold QName in *. rewrite H2. case_eq (eq_TypeName (fst (fst a)) tn); intros.
    * unfold QName in *. rewrite H. cbn in *. rewrite H in H0. inversion H0; subst.
      cbn in *. f_equal...
    * unfold QName in *. rewrite H. cbn in H0. rewrite H in H0...
Qed.

Corollary redefunc_preserves_cfuns_aux :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton (refunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (RefuncDt : forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn)
  (RefuncDt2 : In tn (skeleton_dts (program_skeleton p))),
  pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_cfun_bods_for_type tn p = program_cfun_bods_for_type tn pr2.
Proof with eauto.
intros.
case_eq (program_cfun_bods_for_type tn p); intros.
- unfold program_cfun_bods_for_type in *. subst. cbn.
  rewrite <- app_nil_r with (l:=[]). rewrite filter_app. f_equal.
  + rewrite <- app_nil_r with (l:=[]). rewrite map_app. rewrite filter_app. f_equal.
    * rewrite filter_app. rewrite map_app. rewrite map_app. rewrite filter_app.
      match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * cfun_bod)) end.
      2:{ rewrite map_map. match goal with [|- _ = _ _ (_ _ ?l)] => replace l with (@nil (ScopedName * list TypeName * TypeName)) end...
        clear - RefuncDt. generalize dependent (skeleton_dtors (program_skeleton p)). induction d; intros...
        cbn. unfold cfunsigs_filterfun_g in *. destruct a. destruct p0. destruct s.
        - apply IHd. intros. apply RefuncDt. right...
        - case_eq (eq_TypeName tn (fst q)); intros.
          + exfalso. unfold not in RefuncDt. apply RefuncDt with (d0:=(global q, l, t)); [left|]... cbn.
            rewrite eq_TypeName_eq in H...
          + apply IHd. intros. apply RefuncDt. right...
      }
      rewrite app_nil_r.
      match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => replace l with (@nil (ScopedName * list TypeName * TypeName)) end...
      clear - H1. unfold computeNewCoDatatype. rewrite filter_app.
      unfold cfunsigs_filterfun_g.
      match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * list TypeName * TypeName)) end.
      2:{ clear. match goal with [|- _ = _ (_ _ ?l)] => generalize l end. intros. induction l... }
      rewrite app_nil_r.
      match goal with [|- _ = filter ?f ?l] => replace (filter f l) with l end.
      2:{ generalize (skeleton_cfun_sigs_g (program_skeleton p)). induction c...
        cbn. case_eq (eq_TypeName (fst (fst (fst a))) tn); intros; unfold QName in *; rewrite H...
        cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
      }
      rewrite filter_app in H1. apply app_eq_nil in H1. destruct H1 as [H1 _].
      assert (forall {A B} (l : list A) (f : A -> B), map f l = [] -> l = []).
      { induction l; intros... cbn in H. discriminate. }
      symmetry. apply H with (f:=fun x => unscope (fst (fst x))). clear H. rewrite map_map. cbn.
      apply (f_equal (map (fun x => unscope (fst x)))) in H1. rewrite <- filter_map in H1.
      rewrite map_map in H1. cbn in H1.
      erewrite filter_ext.
      { rewrite filter_map. erewrite filter_ext in H1.
        { rewrite filter_map in H1. rewrite program_has_all_cfun_bods_g. apply H1. }
        intros. destruct a. cbn. destruct q. cbn. instantiate (1:=fun x => eq_TypeName (fst x) tn)...
      }
      intros...
    * rewrite map_map. cbn. clear. unfold RefuncIII.new_cfun_bods_g.
      match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end. induction l...
      cbn. destruct a. case_eq (negb (eq_TypeName tn (fst q))); intros...
      cbn. rewrite negb_true_iff in H. rewrite eq_TypeName_symm in H. rewrite H...
  + rewrite <- app_nil_r with (l:=[]). rewrite map_app. rewrite filter_app. f_equal.
    * rewrite filter_app. rewrite map_app. rewrite map_app. rewrite filter_app.
      match goal with [|- _ = _ ++ ?l] => replace l with (@nil (ScopedName * cfun_bod)) end.
      2:{ rewrite map_map. match goal with [|- _ = _ _ (_ _ ?l)] => replace l with (@nil (ScopedName * list TypeName * TypeName)) end...
        clear - RefuncDt. generalize dependent (skeleton_dtors (program_skeleton p)). induction d; intros...
        cbn. unfold cfunsigs_filterfun_l in *. destruct a. destruct p0. destruct s.
        - case_eq (eq_TypeName tn (fst q)); intros.
          + exfalso. unfold not in RefuncDt. apply RefuncDt with (d0:=(local q, l, t)); [left|]... cbn.
            rewrite eq_TypeName_eq in H...
          + apply IHd. intros. apply RefuncDt. right...
        - apply IHd. intros. apply RefuncDt. right...
      }
      rewrite app_nil_r.
      match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => replace l with (@nil (ScopedName * list TypeName * TypeName)) end...
      clear - H1. unfold computeNewCoDatatype. rewrite filter_app.
      unfold cfunsigs_filterfun_l.
      match goal with [|- _ = ?l ++ _] => replace l with (@nil (ScopedName * list TypeName * TypeName)) end.
      2:{ clear. match goal with [|- _ = _ (_ _ ?l)] => generalize l end. intros. induction l... }
      cbn.
      match goal with [|- _ = filter ?f ?l] => replace (filter f l) with l end.
      2:{ generalize (skeleton_cfun_sigs_l (program_skeleton p)). induction c...
        cbn. case_eq (eq_TypeName (fst (fst (fst a))) tn); intros; unfold QName in *; rewrite H...
        cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
      }
      rewrite filter_app in H1. apply app_eq_nil in H1. destruct H1 as [_ H1].
      assert (forall {A B} (l : list A) (f : A -> B), map f l = [] -> l = []).
      { induction l; intros... cbn in H. discriminate. }
      symmetry. apply H with (f:=fun x => unscope (fst (fst x))). clear H. rewrite map_map. cbn.
      apply (f_equal (map (fun x => unscope (fst x)))) in H1. rewrite <- filter_map in H1.
      rewrite map_map in H1. cbn in H1.
      erewrite filter_ext.
      { rewrite filter_map. erewrite filter_ext in H1.
        { rewrite filter_map in H1. rewrite program_has_all_cfun_bods_l. apply H1. }
        intros. destruct a. cbn. destruct q. cbn. instantiate (1:=fun x => eq_TypeName (fst x) tn)...
      }
      intros...
    * rewrite map_map. cbn. clear. unfold RefuncIII.new_cfun_bods_l.
      match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end. induction l...
      cbn. destruct a. case_eq (negb (eq_TypeName tn (fst q))); intros...
      cbn. rewrite negb_true_iff in H. rewrite eq_TypeName_symm in H. rewrite H...
- case_eq (snd p0); intros.
  { eapply redefunc_preserves_cfuns_empty_ctors... }

  assert (program_cfun_bods_for_type tn p <> []).
  { unfold not. intros. rewrite H3 in H1. discriminate. }
  rewrite <- H1.
  eapply redefunc_preserves_cfuns_nonempty...
  { clear - H1 H2. cbn. unfold program_cfun_bods_for_type in H1.
    rewrite filter_app in H1. pose proof (in_eq p0 l) as InAux.
    rewrite <- H1 in InAux. rename H2 into p0Eq. clear - p0Eq InAux.
    apply in_app_or in InAux.
    pose proof (program_cfun_bods_typecheck_g p) as TypG.
    pose proof (program_cfun_bods_typecheck_l p) as TypL.
    unfold cfun_bods_g_typecheck in TypG.
    unfold cfun_bods_l_typecheck in TypL. rewrite Forall_forall in *.
    destruct InAux; rewrite filter_In in H; destruct H as [H_1 H_2];
      rewrite in_map_iff in H_1; destruct H_1 as [H_1_1 [H_1_2 H_1_3]];
      [ apply TypG in H_1_3 | apply TypL in H_1_3 ];
      clear TypG; clear TypL; destruct H_1_3 as [qn [args [t [_ Typ]]]];
      destruct H_1_1 as [qn' bod]; subst; cbn in *; subst;
      rewrite eq_TypeName_eq in H_2; subst; inversion Typ; subst;
      apply listTypeDeriv'_lemma_ctx in H12; rewrite Nat.eqb_eq in H12;
      clear - H10 H12; unfold lookup_ctors in H10;
      case_eq (filter (eq_TypeName (fst qn')) (skeleton_dts (program_skeleton p)));
      intros; rewrite H in H10; try discriminate; inversion H10; subst;
      clear - H12; repeat rewrite map_length in H12;
      match goal with [_ : _ ?l = _ |- _] =>
        case_eq l; intros; rewrite H in H12; try discriminate end;
      clear - H; pose proof (in_eq p0 l); rewrite <- H in H0; clear H;
      destruct p0; destruct s;
      try solve [
      assert (In (local q, l0) (filter (gfunsigs_filterfun_l (fst qn'))
        (skeleton_ctors (program_skeleton p))));
      [ unfold gfunsigs_filterfun_l; rewrite filter_In in *;
        destruct H0; split; eauto; rewrite eq_TypeName_symm; eauto | ];
      apply in_split in H; do 2 destruct H; unfold RefuncIII.new_gfun_bods_l;
      rewrite H; apply not_eq_sym; repeat rewrite map_app; cbn;
      repeat rewrite filter_app; cbn;
      assert (eq_TypeName (fst q) (fst qn') = true);
      [ rewrite filter_In in H0; destruct H0; eauto | ];
      rewrite H1; rewrite app_assoc;
      match goal with [|- [] <> _ ++ ?l'] => case_eq l'; intros end;
        [| apply app_cons_not_nil ];
      rewrite app_nil_r; rewrite app_assoc; apply app_cons_not_nil
      ];
      try solve
      [
      assert (In (global q, l0) (filter (gfunsigs_filterfun_g (fst qn'))
        (skeleton_ctors (program_skeleton p))));
      [ unfold gfunsigs_filterfun_g; rewrite filter_In in *;
        destruct H0; split; eauto; rewrite eq_TypeName_symm; eauto | ];
      apply in_split in H; do 2 destruct H; unfold RefuncIII.new_gfun_bods_g;
      rewrite H; apply not_eq_sym; repeat rewrite map_app; cbn;
      repeat rewrite filter_app; cbn;
      repeat rewrite filter_app; cbn;
      assert (eq_TypeName (fst q) (fst qn') = true);
      [ rewrite filter_In in H0; destruct H0; eauto | ];
      rewrite H1;
      match goal with [|- [] <> _ ++ ?l'] => case_eq l'; intros end;
        [| apply app_cons_not_nil ]; rewrite app_nil_r;
      match goal with [|- [] <> _ ++ ?l'] => case_eq l'; intros end;
        [| apply app_cons_not_nil ]; rewrite app_nil_r;
      apply app_cons_not_nil
      ].
  }
  { clear - H1 H2. intros. unfold not. intros. subst.
    apply (in_map (map fst)) in H.
    pose proof (in_eq p0 l). rewrite <- H1 in H0.
    apply (in_map snd) in H0. apply (in_map (map fst)) in H0.
    rewrite H2 in H0.
    pose proof (same_ctors _ _ _ _ H H0). discriminate.
  }
Qed.

Lemma refunc_dt_aux : forall p tn,
  In tn (skeleton_dts (program_skeleton p)) ->
  (forall d, In d (skeleton_dtors (program_skeleton p)) -> fst (unscope (fst (fst d))) <> tn).
Proof with eauto.
intros. pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)).
unfold cdts_dtors_in_cdts in H1. rewrite Forall_forall in H1.
apply H1 in H0. clear H1.
pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
unfold dts_cdts_disjoint in H1. unfold not in *. intros. subst.
eapply H1...
Qed.


Lemma derefunc_preserves_cfuns_aux :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton (defunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (* Necessary in case of empty codatatype to make sure no datatypes are defunc.ed. *)
  (DefuncCdt : In tn (skeleton_cdts (program_skeleton p))),
  pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_cfun_bods_for_type tn p = program_cfun_bods_for_type tn pr2.
Proof with eauto.
intros. subst. cbn.
unfold DefuncIII.new_cfun_bods_g. unfold DefuncIII.new_cfun_bods_l.
repeat rewrite filter_app.
repeat rewrite map_app. repeat rewrite filter_app. rewrite map_app.
match goal with [|- ?l' = _] => replace l' with (@nil (ScopedName * cfun_bod)) end.
2:{ clear - DefuncCdt.
  match goal with [|- _ = ?l] => case_eq l; intros end... exfalso.
  pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)).
  pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)).
  pose proof (in_eq p0 l). rewrite <- H in H2. clear H.
  unfold program_cfun_bods_for_type in H2. rewrite filter_In in H2.
  destruct H2. rename H2 into tnEq. rewrite eq_TypeName_eq in tnEq. subst.
  apply (in_map fst) in H. rewrite map_app in H.
  repeat rewrite map_map in H. cbn in H.
  do 2 rewrite <- map_map with (f:=fst) in H.
  rewrite <- program_has_all_cfun_bods_g in H.
  rewrite <- program_has_all_cfun_bods_l in H.
  unfold cfun_sigs_in_dts in H0. rewrite Forall_forall in H0.
  unfold cfun_sigs_in_dts in H1. rewrite Forall_forall in H1.
  apply in_app_or in H.
  pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
  unfold dts_cdts_disjoint in Disj. unfold not in Disj.
  destruct H; rewrite map_map in H; rewrite in_map_iff in H; do 2 destruct H;
    try apply H0 in H2; try apply H1 in H2; rewrite <- H in DefuncCdt...
}
rewrite <- app_nil_r at 1. f_equal.
- rewrite filter_app.
  match goal with [|- _ = _ _ (_ _ (_ _ ?l)) ++ _] => generalize l end. intros.
  match goal with [|- _ = _ ++ _ _ (_ _ (_ _ ?l))] => generalize l end. intros.
  clear. generalize dependent l0. induction l; intros; induction l0...
  + cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    cbn. rewrite eq_TypeName_symm. rewrite H...
  + cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    * cbn. specialize IHl with (l0:=[]). rewrite app_nil_r in *...
    * cbn. rewrite eq_TypeName_symm. rewrite H.
      specialize IHl with (l0:=[]). rewrite app_nil_r in *...
  + cbn. destruct a. destruct a0. case_eq (eq_TypeName tn (fst q)); intros; cbn.
    * case_eq (eq_TypeName tn (fst q0)); intros; cbn...
      rewrite eq_TypeName_symm. rewrite H0...
    * rewrite eq_TypeName_symm. rewrite H.
      case_eq (eq_TypeName tn (fst q0)); intros; cbn...
      rewrite eq_TypeName_symm. rewrite H0...
- repeat rewrite map_app. rewrite filter_app.
  match goal with [|- _ = _ _ (_ _ (_ _ ?l)) ++ _] => generalize l end. intros.
  match goal with [|- _ = _ ++ _ _ (_ _ (_ _ ?l))] => generalize l end. intros.
  clear. generalize dependent l0. induction l; intros; induction l0...
  + cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    cbn. rewrite eq_TypeName_symm. rewrite H...
  + cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    * cbn. specialize IHl with (l0:=[]). rewrite app_nil_r in *...
    * cbn. rewrite eq_TypeName_symm. rewrite H.
      specialize IHl with (l0:=[]). rewrite app_nil_r in *...
  + cbn. destruct a. destruct a0. case_eq (eq_TypeName tn (fst q)); intros; cbn.
    * case_eq (eq_TypeName tn (fst q0)); intros; cbn...
      rewrite eq_TypeName_symm. rewrite H0...
    * rewrite eq_TypeName_symm. rewrite H.
      case_eq (eq_TypeName tn (fst q0)); intros; cbn...
      rewrite eq_TypeName_symm. rewrite H0...
Qed.

Lemma redefunc_preserves_gfuns_aux :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton (refunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (* Necessary in case of empty datatype to make sure no codatatypes are defunc.ed. *)
  (RefuncDt : In tn (skeleton_dts (program_skeleton p))),
  pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_gfun_bods_for_type tn p = program_gfun_bods_for_type tn pr2.
Proof with eauto.
intros. subst. cbn.
unfold RefuncIII.new_gfun_bods_g. unfold RefuncIII.new_gfun_bods_l.
repeat rewrite filter_app.
repeat rewrite map_app. repeat rewrite filter_app. rewrite map_app.
match goal with [|- ?l' = _] => replace l' with (@nil (ScopedName * gfun_bod)) end.
2:{ clear - RefuncDt.
  match goal with [|- _ = ?l] => case_eq l; intros end... exfalso.
  pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)).
  pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)).
  pose proof (in_eq p0 l). rewrite <- H in H2. clear H.
  unfold program_gfun_bods_for_type in H2. rewrite filter_In in H2.
  destruct H2. rename H2 into tnEq. rewrite eq_TypeName_eq in tnEq. subst.
  apply (in_map fst) in H. rewrite map_app in H.
  repeat rewrite map_map in H. cbn in H.
  do 2 rewrite <- map_map with (f:=fst) in H.
  rewrite <- program_has_all_gfun_bods_g in H.
  rewrite <- program_has_all_gfun_bods_l in H.
  unfold gfun_sigs_in_cdts in H0. rewrite Forall_forall in H0.
  unfold gfun_sigs_in_cdts in H1. rewrite Forall_forall in H1.
  apply in_app_or in H.
  pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)) as Disj.
  unfold dts_cdts_disjoint in Disj. unfold not in Disj.
  destruct H; rewrite map_map in H; rewrite in_map_iff in H; do 2 destruct H;
    try apply H0 in H2; try apply H1 in H2; rewrite <- H in RefuncDt...
}
rewrite <- app_nil_r at 1. f_equal.
- rewrite filter_app.
  match goal with [|- _ = _ _ (_ _ (_ _ ?l)) ++ _] => generalize l end. intros.
  match goal with [|- _ = _ ++ _ _ (_ _ (_ _ ?l))] => generalize l end. intros.
  clear. generalize dependent l0. induction l; intros; induction l0...
  + cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    cbn. rewrite eq_TypeName_symm. rewrite H...
  + cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    * cbn. specialize IHl with (l0:=[]). rewrite app_nil_r in *...
    * cbn. rewrite eq_TypeName_symm. rewrite H.
      specialize IHl with (l0:=[]). rewrite app_nil_r in *...
  + cbn. destruct a. destruct a0. case_eq (eq_TypeName tn (fst q)); intros; cbn.
    * case_eq (eq_TypeName tn (fst q0)); intros; cbn...
      rewrite eq_TypeName_symm. rewrite H0...
    * rewrite eq_TypeName_symm. rewrite H.
      case_eq (eq_TypeName tn (fst q0)); intros; cbn...
      rewrite eq_TypeName_symm. rewrite H0...
- repeat rewrite map_app. rewrite filter_app.
  match goal with [|- _ = _ _ (_ _ (_ _ ?l)) ++ _] => generalize l end. intros.
  match goal with [|- _ = _ ++ _ _ (_ _ (_ _ ?l))] => generalize l end. intros.
  clear. generalize dependent l0. induction l; intros; induction l0...
  + cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    cbn. rewrite eq_TypeName_symm. rewrite H...
  + cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros...
    * cbn. specialize IHl with (l0:=[]). rewrite app_nil_r in *...
    * cbn. rewrite eq_TypeName_symm. rewrite H.
      specialize IHl with (l0:=[]). rewrite app_nil_r in *...
  + cbn. destruct a. destruct a0. case_eq (eq_TypeName tn (fst q)); intros; cbn.
    * case_eq (eq_TypeName tn (fst q0)); intros; cbn...
      rewrite eq_TypeName_symm. rewrite H0...
    * rewrite eq_TypeName_symm. rewrite H.
      case_eq (eq_TypeName tn (fst q0)); intros; cbn...
      rewrite eq_TypeName_symm. rewrite H0...
Qed.



(* Results for function bodies *)

Theorem derefunc_preserves_gfuns :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton (defunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (* Necessary in case of empty codatatype to make sure no datatypes are defunc.ed. *)
  (DefuncCdt : In tn (skeleton_cdts (program_skeleton p))),
  pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_gfun_bods_for_type tn p = program_gfun_bods_for_type tn pr2.
Proof with eauto.
intros. eapply derefunc_preserves_gfuns_aux... apply defunc_cdt_aux...
Qed.

Theorem redefunc_preserves_cfuns :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton (refunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (* Necessary in case of empty datatype to make sure no codatatypes are refunc.ed. *)
  (RefuncDt : In tn (skeleton_dts (program_skeleton p))),
  pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_cfun_bods_for_type tn p = program_cfun_bods_for_type tn pr2.
Proof with eauto.
intros. eapply redefunc_preserves_cfuns_aux... apply refunc_dt_aux...
Qed.

Theorem derefunc_preserves_cfuns :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton (defunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (* Necessary in case of empty codatatype to make sure no datatypes are defunc.ed. *)
  (DefuncCdt : In tn (skeleton_cdts (program_skeleton p))),
  pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_cfun_bods_for_type tn p = program_cfun_bods_for_type tn pr2.
Proof with eauto.
intros. eapply derefunc_preserves_cfuns_aux...
Qed.

Theorem redefunc_preserves_gfuns :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton (refunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (* Necessary in case of empty datatype to make sure no codatatypes are refunc.ed. *)
  (RefuncDt : In tn (skeleton_dts (program_skeleton p))),
  pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_gfun_bods_for_type tn p = program_gfun_bods_for_type tn pr2.
Proof with eauto.
intros. eapply redefunc_preserves_gfuns_aux...
Qed.




Require Import Coq.Logic.ProofIrrelevance.

Lemma skeleton_split :
forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23
  P1' P2' P3' P4' P5' P6' P7' P8' P9' P10' P11' P12' P13' P14' P15' P16' P17' P18' P19' P20' P21' P22' P23',
  P1 = P1' -> P2 = P2' -> P5 = P5' -> P6 = P6' -> P10 = P10' -> P12 = P12' -> P15 = P15' ->
  P18 = P18' -> P21 = P21' ->
  mkSkeleton P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 =
    mkSkeleton P1' P2' P3' P4' P5' P6' P7' P8' P9' P10' P11' P12' P13' P14' P15' P16' P17' P18' P19' P20' P21' P22' P23'.
Proof.
intros. subst.
rewrite proof_irrelevance with (p1:=P3)(p2:=P3').
rewrite proof_irrelevance with (p1:=P4)(p2:=P4').
rewrite proof_irrelevance with (p1:=P7)(p2:=P7').
rewrite proof_irrelevance with (p1:=P8)(p2:=P8').
rewrite proof_irrelevance with (p1:=P9)(p2:=P9').
rewrite proof_irrelevance with (p1:=P11)(p2:=P11').
rewrite proof_irrelevance with (p1:=P13)(p2:=P13').
rewrite proof_irrelevance with (p1:=P14)(p2:=P14').
rewrite proof_irrelevance with (p1:=P16)(p2:=P16').
rewrite proof_irrelevance with (p1:=P17)(p2:=P17').
rewrite proof_irrelevance with (p1:=P19)(p2:=P19').
rewrite proof_irrelevance with (p1:=P20)(p2:=P20').
rewrite proof_irrelevance with (p1:=P22)(p2:=P22').
rewrite proof_irrelevance with (p1:=P23)(p2:=P23').
reflexivity.
Qed.

Definition gfun_sigs_g_for_type_in_front p tn : Prop :=
  skeleton_gfun_sigs_g p =
    filter (fun x => eq_TypeName (fst (fst x)) tn) (skeleton_gfun_sigs_g p) ++
    filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) (skeleton_gfun_sigs_g p).

Definition gfun_sigs_l_for_type_in_front p tn : Prop :=
  skeleton_gfun_sigs_l p =
    filter (fun x => eq_TypeName (fst (fst x)) tn) (skeleton_gfun_sigs_l p) ++
    filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) (skeleton_gfun_sigs_l p).

Definition cdt_for_type_in_front p tn : Prop :=
  skeleton_cdts p =
  tn :: filter (fun n' : TypeName => negb (eq_TypeName tn n')) (skeleton_cdts p).

Definition dtors_for_type_in_front p tn : Prop :=
  skeleton_dtors p =
  filter
    (fun x : ScopedName * list TypeName * TypeName =>
     let (y, _) := x in let (n', _) := y in eq_TypeName tn (fst (unscope n')))
    (skeleton_dtors p) ++
  filter
    (fun x : ScopedName * list TypeName * TypeName =>
     let (y, _) := x in let (n', _) := y in negb (eq_TypeName tn (fst (unscope n'))))
    (skeleton_dtors p).

Theorem derefunc_preserves_skeleton :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton (defunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (* Necessary in case of empty codatatype to make sure no datatypes are defunc.ed. *)
  (DefuncCdt : In tn (skeleton_cdts (program_skeleton p)))
  (* In other words, the equality of skeletons only holds up to permutation of sigs *)
  (InFront : gfun_sigs_g_for_type_in_front (program_skeleton p) tn
    /\ gfun_sigs_l_for_type_in_front (program_skeleton p) tn
    /\ cdt_for_type_in_front (program_skeleton p) tn
    /\ dtors_for_type_in_front (program_skeleton p) tn),
  pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_skeleton p = program_skeleton pr2.
Proof with eauto.
intros.
assert (skeleton_dts (program_skeleton p) = skeleton_dts (program_skeleton pr2)).
{ subst. cbn. rewrite eq_TypeName_refl. cbn. clear - DefuncCdt.
  assert (forall x, In x (skeleton_dts (program_skeleton p)) -> In x (skeleton_dts (program_skeleton p))).
  { intros... }
  generalize dependent H. generalize (skeleton_dts (program_skeleton p)) at - 2.
  induction d... intros. cbn. pose proof (H a (in_eq a d)).
  case_eq (eq_TypeName tn a); intros.
  - exfalso. pose proof skeleton_dts_cdts_disjoint. unfold dts_cdts_disjoint in H2.
    unfold not in H2. rewrite eq_TypeName_eq in H1. subst. eapply H2...
  - cbn. f_equal. apply IHd. intros. apply H. right...
}
assert (skeleton_ctors (program_skeleton p) = skeleton_ctors (program_skeleton pr2)).
{ subst. cbn. rewrite filter_app. rewrite <- app_nil_l at 1. f_equal.
  - unfold computeNewDatatype. clear. generalize (skeleton_gfun_sigs_g (program_skeleton p)).
    generalize (skeleton_gfun_sigs_l (program_skeleton p)).
    induction g; intros.
    + cbn. rewrite app_nil_r. induction g; intros...
      cbn. case_eq (eq_TypeName (fst (fst a)) tn); intros; unfold QName in *; rewrite H...
      cbn. rewrite eq_TypeName_symm. rewrite H...
    + cbn. case_eq (eq_TypeName (fst (fst a)) tn); intros; unfold QName in *; rewrite H...
      cbn. rewrite filter_app. cbn. rewrite eq_TypeName_symm. rewrite H. cbn.
      rewrite <- filter_app...
  - clear - DefuncCdt.
    assert (forall x, In x (skeleton_ctors (program_skeleton p)) -> In x (skeleton_ctors (program_skeleton p))).
    { intros... }
    generalize dependent H. generalize (skeleton_ctors (program_skeleton p)) at - 2.
    induction c... cbn. destruct a. case_eq (eq_TypeName tn (fst (unscope s))); intros.
    + exfalso. rewrite eq_TypeName_eq in H. subst. pose proof (H0 (s,l) (in_eq (s,l) c)).
      pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)). unfold dts_ctors_in_dts in H1.
      rewrite Forall_forall in H1. apply H1 in H.
      pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
      unfold dts_cdts_disjoint in H2. unfold not in H2. eapply H2...
    + cbn. f_equal...
}
assert (skeleton_cdts (program_skeleton p) = skeleton_cdts (program_skeleton pr2)).
{ subst. cbn. unfold new_cdts. destruct InFront as [_ [_ [Done _]]]... }
assert (skeleton_dtors (program_skeleton p) = skeleton_dtors (program_skeleton pr2)).
{ subst. cbn. unfold new_dtors. rewrite (proj2 (proj2 (proj2 InFront))) at 1. f_equal.
  unfold DefuncI.new_cfunsigs_g. unfold DefuncI.new_cfunsigs_l.
  do 2 rewrite filter_app.
  assert (filter
     (fun x : TypeName * Name * list TypeName * TypeName =>
      eq_TypeName (fst (fst (fst x))) tn)
     (skeleton_cfun_sigs_g (program_skeleton p)) = []).
  { clear - DefuncCdt. match goal with [|- ?l = _] => case_eq l; intros end...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear H.
    rewrite filter_In in H0. destruct H0. rewrite eq_TypeName_eq in H0. subst.
    pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)).
    unfold cfun_sigs_in_dts in H0. rewrite Forall_forall in H0. apply H0 in H.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H1. unfold not in H1...
  }
  assert (filter
     (fun x : TypeName * Name * list TypeName * TypeName =>
      eq_TypeName (fst (fst (fst x))) tn)
     (skeleton_cfun_sigs_l (program_skeleton p)) = []).
  { clear - DefuncCdt. match goal with [|- ?l = _] => case_eq l; intros end...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear H.
    rewrite filter_In in H0. destruct H0. rewrite eq_TypeName_eq in H0. subst.
    pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)).
    unfold cfun_sigs_in_dts in H0. rewrite Forall_forall in H0. apply H0 in H.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H1. unfold not in H1...
  }
  unfold QName in *. rewrite H. rewrite H0. do 2 rewrite app_nil_r.
  clear - GLd. unfold global_before_local_dtors in GLd.
  erewrite filter_ext.
  - rewrite <- GLd with (tn:=tn). clear. f_equal.
    + generalize (skeleton_dtors (program_skeleton p)).
      induction d... cbn. case_eq (cfunsigs_filterfun_g tn a); intros...
      cbn. case_eq (eq_TypeName (fst (fst (fst (cfunsigs_mapfun a)))) tn); intros;
        unfold QName in *; rewrite H0.
      * cbn. f_equal... unfold cfunsigs_mapfun. destruct a. destruct p0. cbn.
        unfold cfunsigs_filterfun_g in H. destruct s; try discriminate...
      * exfalso. unfold cfunsigs_filterfun_g in H. destruct a. destruct p0.
        destruct s; try discriminate. cbn in H0. rewrite eq_TypeName_symm in H.
        rewrite H in H0. discriminate.
    + generalize (skeleton_dtors (program_skeleton p)).
      induction d... cbn. case_eq (cfunsigs_filterfun_l tn a); intros...
      cbn. case_eq (eq_TypeName (fst (fst (fst (cfunsigs_mapfun a)))) tn); intros;
        unfold QName in *; rewrite H0.
      * cbn. f_equal... unfold cfunsigs_mapfun. destruct a. destruct p0. cbn.
        unfold cfunsigs_filterfun_g in H. destruct s; try discriminate...
      * exfalso. unfold cfunsigs_filterfun_l in H. destruct a. destruct p0.
        destruct s; try discriminate. cbn in H0. rewrite eq_TypeName_symm in H.
        rewrite H in H0. discriminate.
  - intros. destruct a. destruct p0. cbn. apply eq_TypeName_symm.
}
assert (skeleton_fun_sigs (program_skeleton p) = skeleton_fun_sigs (program_skeleton pr2)).
{ subst... }
assert (skeleton_cfun_sigs_g (program_skeleton p) = skeleton_cfun_sigs_g (program_skeleton pr2)).
{ subst. cbn. unfold DefuncI.new_cfunsigs_g. rewrite <- app_nil_l at 1. rewrite filter_app. f_equal.
  - match goal with [|- _ = ?l] => case_eq l; intros end...
    exfalso. clear - H. pose proof (in_eq p0 l). rewrite <- H in H0.
    rewrite filter_In in H0. rewrite in_map_iff in H0. do 3 destruct H0.
    rewrite filter_In in H2. destruct H2. pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)).
    unfold cdts_dtors_in_cdts in H4. rewrite Forall_forall in H4. apply H4 in H2.
    unfold cfunsigs_filterfun_g in H3. destruct p0. destruct p0. destruct x. destruct p0.
    destruct s; try discriminate. rewrite eq_TypeName_eq in H3. subst. cbn in H2.
    unfold cfunsigs_mapfun in H0. cbn in H0. inversion H0; subst. rewrite eq_TypeName_refl in H1.
    discriminate.
  - assert (forall x, In x (skeleton_cfun_sigs_g (program_skeleton p)) ->
      In x (skeleton_cfun_sigs_g (program_skeleton p))).
    { intros... }
    generalize dependent H. generalize (skeleton_cfun_sigs_g (program_skeleton p)) at - 2.
    induction c... intros. cbn. pose proof (H a (in_eq a c)). destruct a. destruct p0.
    case_eq (eq_TypeName tn (fst q)); intros.
    + exfalso. pose proof skeleton_dts_cdts_disjoint. unfold dts_cdts_disjoint in H7.
      unfold not in H7. rewrite eq_TypeName_eq in H6. subst. eapply H7. split...
      pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)). unfold cfun_sigs_in_dts in H6.
      rewrite Forall_forall in H6. apply H6 in H0...
    + cbn. f_equal. apply IHc. intros. apply H. right...
}
assert (skeleton_cfun_sigs_l (program_skeleton p) = skeleton_cfun_sigs_l (program_skeleton pr2)).
{ subst. cbn. unfold DefuncI.new_cfunsigs_l. rewrite <- app_nil_l at 1. rewrite filter_app. f_equal.
  - match goal with [|- _ = ?l] => case_eq l; intros end...
    exfalso. clear - H. pose proof (in_eq p0 l). rewrite <- H in H0.
    rewrite filter_In in H0. rewrite in_map_iff in H0. do 3 destruct H0.
    rewrite filter_In in H2. destruct H2. pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)).
    unfold cdts_dtors_in_cdts in H4. rewrite Forall_forall in H4. apply H4 in H2.
    unfold cfunsigs_filterfun_l in H3. destruct p0. destruct p0. destruct x. destruct p0.
    destruct s; try discriminate. rewrite eq_TypeName_eq in H3. subst. cbn in H2.
    unfold cfunsigs_mapfun in H0. cbn in H0. inversion H0; subst. rewrite eq_TypeName_refl in H1.
    discriminate.
  - assert (forall x, In x (skeleton_cfun_sigs_l (program_skeleton p)) ->
      In x (skeleton_cfun_sigs_l (program_skeleton p))).
    { intros... }
    generalize dependent H. generalize (skeleton_cfun_sigs_l (program_skeleton p)) at - 2.
    induction c... intros. cbn. pose proof (H a (in_eq a c)). destruct a. destruct p0.
    case_eq (eq_TypeName tn (fst q)); intros.
    + exfalso. pose proof skeleton_dts_cdts_disjoint. unfold dts_cdts_disjoint in H8.
      unfold not in H8. rewrite eq_TypeName_eq in H7. subst. eapply H8. split...
      pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)). unfold cfun_sigs_in_dts in H7.
      rewrite Forall_forall in H7. apply H7 in H0...
    + cbn. f_equal. apply IHc. intros. apply H. right...
}
assert (skeleton_gfun_sigs_g (program_skeleton p) = skeleton_gfun_sigs_g (program_skeleton pr2)).
{ subst. cbn. unfold DefuncI.new_gfunsigs_g. unfold computeNewDatatype. unfold gfunsigs_mapfun.
  rewrite (proj1 InFront) at 1. rewrite filter_ext with (f:=(fun x : TypeName * Name * list TypeName =>
    let (n', _) := x in negb (eq_TypeName tn (fst n'))))
    (g:=fun x : TypeName * Name * list TypeName => negb (eq_TypeName (fst (fst x)) tn)).
  2:{ intros. destruct a. rewrite eq_TypeName_symm... }
  unfold QName. f_equal. rewrite filter_app. unfold Constructor.
  replace (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))) with (@nil (ScopedName * list TypeName)).
  2:{ case_eq (filter (gfunsigs_filterfun_g tn) (skeleton_ctors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - DefuncCdt H0.
    rewrite filter_In in H0. destruct H0.
    pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)).
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_ctors_in_dts in H1. unfold dts_cdts_disjoint in H2.
    unfold not in H2. rewrite Forall_forall in H1. apply H1 in H.
    unfold gfunsigs_filterfun_g in H0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0. subst. cbn in H. eapply H2... }
  rewrite app_nil_r. rewrite filter_app. rewrite map_app. rewrite <- app_nil_r at 1. f_equal.
  2:{ match goal with [|- _ = ?l] => case_eq l; intros end... clear - H.
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear H.
    rewrite in_map_iff in H0. destruct H0. destruct H. rewrite filter_In in H0.
    destruct H0. rewrite in_map_iff in H0. do 2 destruct H0. subst.
    rewrite filter_In in H2. destruct H2. rewrite eq_TypeName_eq in H0.
    subst. discriminate.
  }
  match goal with [|- _ _ ?lhs = _] => generalize lhs end. clear. induction g...
  cbn. case_eq (eq_TypeName tn (fst (fst a))); intros.
  - rewrite eq_TypeName_symm. unfold QName in *. rewrite H. cbn. rewrite H.
    cbn. rewrite <- surjective_pairing. f_equal...
  - rewrite eq_TypeName_symm. unfold QName in *. rewrite H...
}
assert (skeleton_gfun_sigs_l (program_skeleton p) = skeleton_gfun_sigs_l (program_skeleton pr2)).
{ subst. cbn. unfold DefuncI.new_gfunsigs_l. unfold computeNewDatatype. unfold gfunsigs_mapfun.
  rewrite (proj1 (proj2 InFront)) at 1. rewrite filter_ext with (f:=(fun x : TypeName * Name * list TypeName =>
    let (n', _) := x in negb (eq_TypeName tn (fst n'))))
    (g:=fun x : TypeName * Name * list TypeName => negb (eq_TypeName (fst (fst x)) tn)).
  2:{ intros. destruct a. rewrite eq_TypeName_symm... }
  unfold QName. f_equal. rewrite filter_app. unfold Constructor.
  replace (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))) with (@nil (ScopedName * list TypeName)).
  2:{ case_eq (filter (gfunsigs_filterfun_l tn) (skeleton_ctors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - DefuncCdt H0.
    rewrite filter_In in H0. destruct H0.
    pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)).
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_ctors_in_dts in H1. unfold dts_cdts_disjoint in H2.
    unfold not in H2. rewrite Forall_forall in H1. apply H1 in H.
    unfold gfunsigs_filterfun_l in H0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0. subst. cbn in H. eapply H2... }
  rewrite app_nil_r. rewrite filter_app. rewrite map_app. rewrite <- app_nil_l at 1. f_equal.
  { match goal with [|- _ = ?l] => case_eq l; intros end... clear - H.
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear H.
    rewrite in_map_iff in H0. destruct H0. destruct H. rewrite filter_In in H0.
    destruct H0. rewrite in_map_iff in H0. do 2 destruct H0. subst.
    rewrite filter_In in H2. destruct H2. rewrite eq_TypeName_eq in H0.
    subst. discriminate.
  }
  match goal with [|- _ _ ?lhs = _] => generalize lhs end. clear. induction g...
  cbn. case_eq (eq_TypeName tn (fst (fst a))); intros.
  - rewrite eq_TypeName_symm. unfold QName in *. rewrite H. cbn. rewrite H.
    cbn. rewrite <- surjective_pairing. f_equal...
  - rewrite eq_TypeName_symm. unfold QName in *. rewrite H...
}
clear - H1 H2 H3 H4 H5 H6 H7 H8 H9. generalize dependent (program_skeleton p).
generalize dependent (program_skeleton pr2). intros.
destruct s0. destruct s. cbn in *. apply skeleton_split...
Qed.


Lemma prog_split :
forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18
  P1' P2' P3' P4' P5' P6' P7' P8' P9' P10' P11' P12' P13' P14' P15' P16' P17' P18',
  P1 = P1' -> P2 = P2' -> P5 = P5' -> P8 = P8' -> P11 = P11' ->  P14 = P14' ->
  mkProgram P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 =
    mkProgram P1' P2' P3' P4' P5' P6' P7' P8' P9' P10' P11' P12' P13' P14' P15' P16' P17' P18'.
Proof.
intros. subst.
rewrite proof_irrelevance with (p1:=P3)(p2:=P3').
rewrite proof_irrelevance with (p1:=P4)(p2:=P4').
rewrite proof_irrelevance with (p1:=P6)(p2:=P6').
rewrite proof_irrelevance with (p1:=P7)(p2:=P7').
rewrite proof_irrelevance with (p1:=P9)(p2:=P9').
rewrite proof_irrelevance with (p1:=P10)(p2:=P10').
rewrite proof_irrelevance with (p1:=P12)(p2:=P12').
rewrite proof_irrelevance with (p1:=P13)(p2:=P13').
rewrite proof_irrelevance with (p1:=P15)(p2:=P15').
rewrite proof_irrelevance with (p1:=P16)(p2:=P16').
rewrite proof_irrelevance with (p1:=P17)(p2:=P17').
rewrite proof_irrelevance with (p1:=P18)(p2:=P18').
reflexivity.
Qed.


Definition gfun_bods_g_for_type_in_front p tn : Prop :=
  program_gfun_bods_g p =
    filter (fun x => eq_TypeName (fst (fst x)) tn) (program_gfun_bods_g p) ++
    filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) (program_gfun_bods_g p).

Definition gfun_bods_l_for_type_in_front p tn : Prop :=
  program_gfun_bods_l p =
    filter (fun x => eq_TypeName (fst (fst x)) tn) (program_gfun_bods_l p) ++
    filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) (program_gfun_bods_l p).

Theorem derefunc_preserves_prog_aux :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton (defunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (* Necessary in case of empty codatatype to make sure no datatypes are defunc.ed. *)
  (DefuncCdt : In tn (skeleton_cdts (program_skeleton p)))
  (* In other words, the equality of programs only holds up to permutation of fundefs *)
  (InFront : gfun_bods_g_for_type_in_front p tn /\ gfun_bods_l_for_type_in_front p tn)
  (InFrontSigs : gfun_sigs_g_for_type_in_front (program_skeleton p) tn
    /\ gfun_sigs_l_for_type_in_front (program_skeleton p) tn
    /\ cdt_for_type_in_front (program_skeleton p) tn
    /\ dtors_for_type_in_front (program_skeleton p) tn),
  pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  p = pr2.
Proof with eauto.
intros.
assert (program_skeleton p = program_skeleton pr2). { eapply derefunc_preserves_skeleton... }
assert (program_fun_bods p = program_fun_bods pr2).
{ subst. cbn. unfold DefuncIII.new_fun_bods. rewrite map_map.
  rewrite map_ext_in with (g:=id); try solve [rewrite map_id; eauto].
  intros. unfold id. cbn. rewrite surjective_pairing. f_equal.
  apply derefunc_exp_inverse with (p:=p); try solve [apply defunc_cdt_aux; eauto]...
  right. right. apply in_map...
}
assert (program_cfun_bods_g p = program_cfun_bods_g pr2).
{ subst. match goal with [|- _ = ?rhs] => remember rhs end.
  match goal with [_ : c = _ ?p'' |- _] => set (p':=p'') in * end.
  pose proof Heqc as Work.
  cbn in Work.
  unfold DefuncIII.new_cfun_bods_g in *.
  rewrite map_app in Work. rewrite map_map in Work. rewrite filter_app in Work.
  match goal with [_ : c = ?rhs1' ++ ?rhs2' |- _] =>
    set (rhs1:=rhs1') in Work; set (rhs2:=rhs2') in Work end.
  assert (rhs1 = []) as Work1.
  { unfold rhs1. clear. generalize (skeleton_dtors (program_skeleton p)).
    induction d... cbn. case_eq (cfunsigs_filterfun_g tn a); intros...
    cbn. case_eq (eq_TypeName tn (fst (unscope (fst (fst a))))); intros...
    exfalso. clear - H H0. unfold cfunsigs_filterfun_g in H. destruct a. destruct p.
    destruct s; try discriminate. cbn in H0. rewrite H in H0. discriminate.
  }
  assert (rhs2 = program_cfun_bods_g p) as Work2.
  { unfold rhs2. rewrite map_map. cbn. rewrite map_ext_in with (g:=id).
    2:{ intros. rewrite map_map. rewrite map_ext_in with (g:=id).
      2:{ intros. cbn. unfold id.
          rewrite derefunc_exp_inverse with (p:=p); try solve [apply defunc_cdt_aux; eauto]...
        - rewrite <- surjective_pairing...
        - clear - H H0. right. left. apply in_map. rewrite in_flat_map. unfold program_cfun_bods.
          destruct a. exists (global q,l). split...
          apply in_or_app. left. rewrite in_map_iff. exists (q,l). split...
      }
      unfold id. rewrite map_id. symmetry. apply surjective_pairing.
    }
    unfold id. rewrite map_id. clear - DefuncCdt.
    assert (forall x, In x (program_cfun_bods_g p) -> In x (program_cfun_bods_g p)).
    { intros... }
    generalize dependent H. generalize (program_cfun_bods_g p) at - 2. induction c; intros...
    cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros.
    - exfalso. pose proof (H (q,c0) (in_eq (q,c0) c)). apply (in_map fst) in H1.
      cbn in H1. rewrite <- program_has_all_cfun_bods_g in H1.
      rewrite in_map_iff in H1. do 2 destruct H1.
      pose proof (skeleton_cfun_sigs_in_dts_g (program_skeleton p)).
      unfold cfun_sigs_in_dts in H3. rewrite Forall_forall in H3.
      apply H3 in H2. subst. rewrite eq_TypeName_eq in H0. subst.
      pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
      unfold dts_cdts_disjoint in H0. unfold not in H0. eapply H0...
    - cbn. f_equal. apply IHc. intros. apply H. right...
  }
  rewrite Work. rewrite Work1. rewrite Work2...
}
assert (program_cfun_bods_l p = program_cfun_bods_l pr2).
{ subst. match goal with [|- _ = ?rhs] => remember rhs end.
  match goal with [_ : c = _ ?p'' |- _] => set (p':=p'') in * end.
  pose proof Heqc as Work.
  cbn in Work.
  unfold DefuncIII.new_cfun_bods_l in *.
  rewrite map_app in Work. rewrite map_map in Work. rewrite filter_app in Work.
  match goal with [_ : c = ?rhs1' ++ ?rhs2' |- _] =>
    set (rhs1:=rhs1') in Work; set (rhs2:=rhs2') in Work end.
  assert (rhs1 = []) as Work1.
  { unfold rhs1. clear. generalize (skeleton_dtors (program_skeleton p)).
    induction d... cbn. case_eq (cfunsigs_filterfun_l tn a); intros...
    cbn. case_eq (eq_TypeName tn (fst (unscope (fst (fst a))))); intros...
    exfalso. clear - H H0. unfold cfunsigs_filterfun_l in H. destruct a. destruct p.
    destruct s; try discriminate. cbn in H0. rewrite H in H0. discriminate.
  }
  assert (rhs2 = program_cfun_bods_l p) as Work2.
  { unfold rhs2. rewrite map_map. cbn. rewrite map_ext_in with (g:=id).
    2:{ intros. rewrite map_map. rewrite map_ext_in with (g:=id).
      2:{ intros. cbn. unfold id.
          rewrite derefunc_exp_inverse with (p:=p); try solve [apply defunc_cdt_aux; eauto]...
        - rewrite <- surjective_pairing...
        - clear - H H0. right. left. apply in_map. rewrite in_flat_map. unfold program_cfun_bods.
          destruct a. exists (local q,l). split...
          apply in_or_app. right. rewrite in_map_iff. exists (q,l). split...
      }
      unfold id. rewrite map_id. symmetry. apply surjective_pairing.
    }
    unfold id. rewrite map_id. clear - DefuncCdt.
    assert (forall x, In x (program_cfun_bods_l p) -> In x (program_cfun_bods_l p)).
    { intros... }
    generalize dependent H. generalize (program_cfun_bods_l p) at - 2. induction c; intros...
    cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros.
    - exfalso. pose proof (H (q,c0) (in_eq (q,c0) c)). apply (in_map fst) in H1.
      cbn in H1. rewrite <- program_has_all_cfun_bods_l in H1.
      rewrite in_map_iff in H1. do 2 destruct H1.
      pose proof (skeleton_cfun_sigs_in_dts_l (program_skeleton p)).
      unfold cfun_sigs_in_dts in H3. rewrite Forall_forall in H3.
      apply H3 in H2. subst. rewrite eq_TypeName_eq in H0. subst.
      pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
      unfold dts_cdts_disjoint in H0. unfold not in H0. eapply H0...
    - cbn. f_equal. apply IHc. intros. apply H. right...
  }
  rewrite Work. rewrite Work1. rewrite Work2...
}
assert (program_gfun_bods_g p = program_gfun_bods_g pr2).
{ subst. match goal with [|- _ = ?rhs] => remember rhs end.
  match goal with [_ : g = _ ?p'' |- _] => set (p':=p'') in * end.
  pose proof Heqg as Work.
  cbn in Work. match goal with [_ : g = ?rhs1' ++ ?rhs2' |- _] =>
    set (rhs1:=rhs1') in Work; set (rhs2:=rhs2') in Work end.
  unfold DefuncIII.new_gfun_bods_g in *.
  assert (rhs1 = filter (fun x => eq_TypeName (fst (fst x)) tn) g) as Work1.
  { rewrite Work. rewrite filter_app. replace (filter _ rhs2) with (@nil (QName * gfun_bod)).
    2:{ unfold rhs2. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
      induction l... cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros... cbn.
      rewrite eq_TypeName_symm. rewrite H...
    }
    rewrite app_nil_r. unfold rhs1. match goal with [|- _ _ (_ _ ?l) = _] => generalize l end.
    clear. induction l... cbn. case_eq (gfunsigs_filterfun_g tn a); intros... cbn.
    case_eq (eq_TypeName (fst (unscope (fst a))) tn); intros; f_equal...
    exfalso. clear - H H0. unfold gfunsigs_filterfun_g in H. destruct a. destruct s; try discriminate.
    cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
  }
  assert (rhs2 = filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) g) as Work2.
  { rewrite Work. rewrite filter_app. replace (filter _ rhs1) with (@nil (QName * gfun_bod)).
    2:{ unfold rhs1. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
      induction l... cbn. case_eq (gfunsigs_filterfun_g tn a); intros... cbn.
      case_eq (eq_TypeName (fst (unscope (fst a))) tn); intros; f_equal...
      exfalso. clear - H H0. unfold gfunsigs_filterfun_g in H. destruct a. destruct s; try discriminate.
      cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
    }
    cbn. unfold rhs2. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
    induction l... cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros... cbn.
    rewrite eq_TypeName_symm. rewrite H. cbn. f_equal...
  }
  assert (rhs1 = map (fun x => (unscope (fst x), snd x))
    (filter (fun x => match fst x with global _ => true | _ => false end)
      (program_gfun_bods_for_type tn p'))) as Work1'.
  { rewrite Work1. rewrite Heqg. unfold program_gfun_bods_for_type.
    rewrite filter_filter. rewrite filter_app. erewrite (@filter_ext (ScopedName * gfun_bod)).
    { rewrite filter_map. f_equal; try reflexivity.
      match goal with [|- _ = _ _ (_ ++ ?l)] => replace l with (@nil (ScopedName * gfun_bod)) end.
      2:{ generalize (program_gfun_bods_l p'). induction g0... }
      rewrite app_nil_r. generalize (program_gfun_bods_g p'). induction g0...
      cbn. rewrite <- surjective_pairing. f_equal...
    }
    intros...
  }
  erewrite <- derefunc_preserves_gfuns with (p:=p) in Work1'...
  2:{ unfold p'... }
  rewrite (proj1 InFront). rewrite Work. rewrite Work1'. unfold rhs2.
  unfold program_gfun_bods_for_type. do 2 rewrite filter_app. do 2 rewrite filter_compose.
  rewrite map_app.
  match goal with [|- _ = (_ ?m (_ ?f1 ?l1) ++ _ ?m (_ ?f2 ?l2)) ++ _] =>
    replace (map m (filter f1 l1)) with
      (filter (fun x : QName * gfun_bod => eq_TypeName (fst (fst x)) tn) (map m l1));
    [ replace (filter f2 l2) with (@nil (ScopedName * gfun_bod)) |] end.
  2:{ generalize (program_gfun_bods_l p). induction g0... }
  2:{ generalize (program_gfun_bods_g p). induction g0... cbn.
    case_eq (eq_TypeName (fst (fst a)) tn); intros... cbn. f_equal...
  }
  cbn. rewrite app_nil_r. rewrite map_map. cbn. erewrite map_ext.
  2:{ intros. rewrite <- surjective_pairing. reflexivity. }
  rewrite map_id. f_equal.
  rewrite <- filter_map. rewrite map_map. cbn. rewrite map_ext_in with (g:=id).
  2:{ intros. destruct a. cbn. unfold id. f_equal. rewrite map_map. cbn.
    rewrite map_ext_in with (g:=id); [ rewrite map_id | ]...
    intros. rewrite derefunc_exp_inverse with (p:=p); try solve [apply defunc_cdt_aux; eauto]...
    - unfold id. rewrite <- surjective_pairing...
    - clear - H H0. left. apply in_map. rewrite in_flat_map. unfold program_gfun_bods.
      rewrite filter_In in H. destruct H. exists (global q,l). split...
      apply in_or_app. left. rewrite in_map_iff. exists (q,l). split...
   }
   rewrite map_id. apply filter_ext. intros. f_equal. apply eq_TypeName_symm.
}
assert (program_gfun_bods_l p = program_gfun_bods_l pr2).
{ subst. match goal with [|- _ = ?rhs] => remember rhs end.
  match goal with [_ : g = _ ?p'' |- _] => set (p':=p'') in * end.
  pose proof Heqg as Work.
  cbn in Work. match goal with [_ : g = ?rhs1' ++ ?rhs2' |- _] =>
    set (rhs1:=rhs1') in Work; set (rhs2:=rhs2') in Work end.
  unfold DefuncIII.new_gfun_bods_l in *.
  assert (rhs1 = filter (fun x => eq_TypeName (fst (fst x)) tn) g) as Work1.
  { rewrite Work. rewrite filter_app. replace (filter _ rhs2) with (@nil (QName * gfun_bod)).
    2:{ unfold rhs2. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
      induction l... cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros... cbn.
      rewrite eq_TypeName_symm. rewrite H...
    }
    rewrite app_nil_r. unfold rhs1. match goal with [|- _ _ (_ _ ?l) = _] => generalize l end.
    clear. induction l... cbn. case_eq (gfunsigs_filterfun_l tn a); intros... cbn.
    case_eq (eq_TypeName (fst (unscope (fst a))) tn); intros; f_equal...
    exfalso. clear - H H0. unfold gfunsigs_filterfun_l in H. destruct a. destruct s; try discriminate.
    cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
  }
  assert (rhs2 = filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) g) as Work2.
  { rewrite Work. rewrite filter_app. replace (filter _ rhs1) with (@nil (QName * gfun_bod)).
    2:{ unfold rhs1. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
      induction l... cbn. case_eq (gfunsigs_filterfun_l tn a); intros... cbn.
      case_eq (eq_TypeName (fst (unscope (fst a))) tn); intros; f_equal...
      exfalso. clear - H H0. unfold gfunsigs_filterfun_l in H. destruct a. destruct s; try discriminate.
      cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
    }
    cbn. unfold rhs2. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
    induction l... cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros... cbn.
    rewrite eq_TypeName_symm. rewrite H. cbn. f_equal...
  }
  assert (rhs1 = map (fun x => (unscope (fst x), snd x))
    (filter (fun x => match fst x with global _ => false | _ => true end)
      (program_gfun_bods_for_type tn p'))) as Work1'.
  { rewrite Work1. rewrite Heqg. unfold program_gfun_bods_for_type.
    rewrite filter_filter. rewrite filter_app. erewrite (@filter_ext (ScopedName * gfun_bod)).
    { rewrite filter_map. f_equal; try reflexivity.
      match goal with [|- _ = _ _ (?l ++ _)] => replace l with (@nil (ScopedName * gfun_bod)) end.
      2:{ generalize (program_gfun_bods_g p'). induction g0... }
      generalize (program_gfun_bods_l p'). induction g0...
      cbn. rewrite <- surjective_pairing. f_equal...
    }
    intros...
  }
  erewrite <- derefunc_preserves_gfuns with (p:=p) in Work1'...
  2:{ unfold p'... }
  rewrite (proj2 InFront). rewrite Work. rewrite Work1'. unfold rhs2.
  unfold program_gfun_bods_for_type. do 2 rewrite filter_app. do 2 rewrite filter_compose.
  rewrite map_app.
  match goal with [|- _ = (_ ?m (_ ?f1 ?l1) ++ _ ?m (_ ?f2 ?l2)) ++ _] =>
    replace (map m (filter f2 l2)) with
      (filter (fun x : QName * gfun_bod => eq_TypeName (fst (fst x)) tn) (map m l2));
    [ replace (filter f1 l1) with (@nil (ScopedName * gfun_bod)) |] end.
  2:{ generalize (program_gfun_bods_g p). induction g0... }
  2:{ generalize (program_gfun_bods_l p). induction g0... cbn.
    case_eq (eq_TypeName (fst (fst a)) tn); intros... cbn. f_equal...
  }
  cbn. rewrite map_map. cbn. erewrite map_ext.
  2:{ intros. rewrite <- surjective_pairing. reflexivity. }
  rewrite map_id. f_equal.
  rewrite <- filter_map. rewrite map_map. cbn. rewrite map_ext_in with (g:=id).
  2:{ intros. destruct a. cbn. unfold id. f_equal. rewrite map_map. cbn.
    rewrite map_ext_in with (g:=id); [ rewrite map_id | ]...
    intros. rewrite derefunc_exp_inverse with (p:=p); try solve [apply defunc_cdt_aux; eauto]...
    - unfold id. rewrite <- surjective_pairing...
    - clear - H H0. left. apply in_map. rewrite in_flat_map. unfold program_gfun_bods.
      rewrite filter_In in H. destruct H. exists (local q,l). split...
      apply in_or_app. right. rewrite in_map_iff. exists (q,l). split...
   }
   rewrite map_id. apply filter_ext. intros. f_equal. apply eq_TypeName_symm.
}
subst. unfold refunctionalize_program. destruct p. apply prog_split...
Qed.

Lemma global_before_local_ctors_defunc :
forall p tn P1 P2 P3 P4 P5 (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (DefuncCdt : In tn (skeleton_cdts (program_skeleton p))),
  global_before_local_ctors (skeleton_ctors (program_skeleton (defunctionalize_program p tn P1 P2 P3 P4 P5))).
Proof with eauto.
intros. unfold global_before_local_ctors in *. intros.
cbn. clear - GLc DefuncCdt. case_eq (eq_TypeName tn tn0); intros.
- rewrite eq_TypeName_eq in H. subst. repeat rewrite filter_app.
  match goal with [|- (_ ++ ?l1) ++ (_ ++ ?l2) = _ ++ ?l3] =>
    replace l1 with (@nil Constructor); [ replace l2 with (@nil Constructor) |];
    [ replace l3 with (@nil Constructor) | |]
  end.
  2:{ case_eq (filter (fun x : ScopedName * list TypeName => eq_TypeName (fst (unscope (fst x))) tn0)
        (skeleton_ctors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - H0 DefuncCdt.
    rewrite filter_In in H0. destruct H0. pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)).
    unfold dts_ctors_in_dts in H1. rewrite Forall_forall in H1. apply H1 in H.
    rewrite eq_TypeName_eq in H0. subst. pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H0. unfold not in H0...
  }
  2:{ case_eq (filter (gfunsigs_filterfun_l tn0) (skeleton_ctors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - H0 DefuncCdt.
    rewrite filter_In in H0. destruct H0. pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)).
    unfold dts_ctors_in_dts in H1. rewrite Forall_forall in H1. apply H1 in H.
    unfold gfunsigs_filterfun_l in H0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0. subst. pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H0. unfold not in H0...
  }
  2:{ case_eq (filter (gfunsigs_filterfun_g tn0) (skeleton_ctors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - H0 DefuncCdt.
    rewrite filter_In in H0. destruct H0. pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)).
    unfold dts_ctors_in_dts in H1. rewrite Forall_forall in H1. apply H1 in H.
    unfold gfunsigs_filterfun_g in H0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0. subst. pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H0. unfold not in H0...
  }
  repeat rewrite app_nil_r. unfold computeNewDatatype.
  generalize (skeleton_gfun_sigs_g (program_skeleton p)).
  generalize (skeleton_gfun_sigs_l (program_skeleton p)).
  clear. intros. repeat rewrite filter_app.
  match goal with [|- (_ ++ ?l1) ++ (?l2 ++ _) = _] =>
    replace l1 with (@nil Constructor); [ replace l2 with (@nil Constructor) |]
  end.
  2:{ induction g0... cbn.
    case_eq (eq_TypeName (fst (fst a)) tn0); intros; unfold QName in *; rewrite H...
  }
  2:{ induction g... cbn.
    case_eq (eq_TypeName (fst (fst a)) tn0); intros; unfold QName in *; rewrite H...
  }
  repeat rewrite app_nil_r. f_equal.
  + induction g0... cbn.
    case_eq (eq_TypeName (fst (fst a)) tn0); intros; unfold QName in *; rewrite H...
    cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
  + cbn. induction g... cbn.
    case_eq (eq_TypeName (fst (fst a)) tn0); intros; unfold QName in *; rewrite H...
    cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
- repeat rewrite filter_app.
  match goal with [|- (?l1 ++ _) ++ (?l2 ++ _) = ?l3 ++ _] =>
    replace l1 with (@nil Constructor); [ replace l2 with (@nil Constructor) |];
    [ replace l3 with (@nil Constructor) | |]
  end.
  2:{ case_eq (filter (fun x : ScopedName * list TypeName => eq_TypeName (fst (unscope (fst x))) tn0)
        (computeNewDatatype p tn)); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H0 in H1. clear - H H1.
    rewrite filter_In in H1. destruct H1. unfold computeNewDatatype in H0. apply in_app_or in H0.
    destruct H0; rewrite in_map_iff in H0; do 2 destruct H0; subst;
      rewrite filter_In in H2; destruct H2; cbn in H1; rewrite eq_TypeName_eq in *; subst;
      rewrite eq_TypeName_refl in H; discriminate.
  }
  2:{ case_eq (filter (gfunsigs_filterfun_l tn0) (computeNewDatatype p tn)); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H0 in H1. clear - H H1.
    rewrite filter_In in H1. destruct H1. unfold computeNewDatatype in H0. apply in_app_or in H0.
    destruct H0; rewrite in_map_iff in H0; do 2 destruct H0; subst;
      rewrite filter_In in H2; destruct H2; cbn in H1; rewrite eq_TypeName_eq in *; subst;
      try rewrite eq_TypeName_refl in H; discriminate.
  }
  2:{ case_eq (filter (gfunsigs_filterfun_g tn0) (computeNewDatatype p tn)); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H0 in H1. clear - H H1.
    rewrite filter_In in H1. destruct H1. unfold computeNewDatatype in H0. apply in_app_or in H0.
    destruct H0; rewrite in_map_iff in H0; do 2 destruct H0; subst;
      rewrite filter_In in H2; destruct H2; cbn in H1; rewrite eq_TypeName_eq in *; subst;
      try rewrite eq_TypeName_refl in H; discriminate.
  }
  eauto.
Qed.



Definition cfun_sigs_g_for_type_in_front p tn : Prop :=
  skeleton_cfun_sigs_g p =
    filter (fun x => eq_TypeName (fst (fst (fst x))) tn) (skeleton_cfun_sigs_g p) ++
    filter (fun x => negb (eq_TypeName (fst (fst (fst x))) tn)) (skeleton_cfun_sigs_g p).

Definition cfun_sigs_l_for_type_in_front p tn : Prop :=
  skeleton_cfun_sigs_l p =
    filter (fun x => eq_TypeName (fst (fst (fst x))) tn) (skeleton_cfun_sigs_l p) ++
    filter (fun x => negb (eq_TypeName (fst (fst (fst x))) tn)) (skeleton_cfun_sigs_l p).

Definition dt_for_type_in_front p tn : Prop :=
  skeleton_dts p =
  tn :: filter (fun n' : TypeName => negb (eq_TypeName tn n')) (skeleton_dts p).

Definition ctors_for_type_in_front p tn : Prop :=
  skeleton_ctors p =
  filter
    (fun x : ScopedName * list TypeName =>
     let (n', _) := x in eq_TypeName tn (fst (unscope n')))
    (skeleton_ctors p) ++
  filter
    (fun x : ScopedName * list TypeName =>
     let (n', _) := x in negb (eq_TypeName tn (fst (unscope n'))))
    (skeleton_ctors p).

Theorem redefunc_preserves_skeleton :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton (refunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (* Necessary in case of empty datatype to make sure no codatatypes are defunc.ed. *)
  (RefuncDt : In tn (skeleton_dts (program_skeleton p)))
  (* In other words, the equality of skeletons only holds up to permutation of sigs *)
  (InFront : cfun_sigs_g_for_type_in_front (program_skeleton p) tn
    /\ cfun_sigs_l_for_type_in_front (program_skeleton p) tn
    /\ dt_for_type_in_front (program_skeleton p) tn
    /\ ctors_for_type_in_front (program_skeleton p) tn),
  pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  program_skeleton p = program_skeleton pr2.
Proof with eauto.
intros.
assert (skeleton_dts (program_skeleton p) = skeleton_dts (program_skeleton pr2)).
{ subst. cbn. unfold new_dts. destruct InFront as [_ [_ [Done _]]]... }
assert (skeleton_ctors (program_skeleton p) = skeleton_ctors (program_skeleton pr2)).
{ subst. cbn. unfold new_ctors. rewrite (proj2 (proj2 (proj2 InFront))) at 1. f_equal.
  unfold new_gfunsigs_g. unfold new_gfunsigs_l.
  do 2 rewrite filter_app.
  assert (filter
     (fun x : TypeName * Name * list TypeName =>
      eq_TypeName (fst (fst x)) tn)
     (skeleton_gfun_sigs_g (program_skeleton p)) = []).
  { clear - RefuncDt. match goal with [|- ?l = _] => case_eq l; intros end...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear H.
    rewrite filter_In in H0. destruct H0. rewrite eq_TypeName_eq in H0. subst.
    pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)).
    unfold gfun_sigs_in_cdts in H0. rewrite Forall_forall in H0. apply H0 in H.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H1. unfold not in H1...
  }
  assert (filter
     (fun x : TypeName * Name * list TypeName =>
      eq_TypeName (fst (fst x)) tn)
     (skeleton_gfun_sigs_l (program_skeleton p)) = []).
  { clear - RefuncDt. match goal with [|- ?l = _] => case_eq l; intros end...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear H.
    rewrite filter_In in H0. destruct H0. rewrite eq_TypeName_eq in H0. subst.
    pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)).
    unfold gfun_sigs_in_cdts in H0. rewrite Forall_forall in H0. apply H0 in H.
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H1. unfold not in H1...
  }
  unfold QName in *. rewrite H. rewrite H0. do 2 rewrite app_nil_r.
  clear - GLc. unfold global_before_local_ctors in GLc.
  erewrite filter_ext.
  - rewrite <- GLc with (tn:=tn). clear. f_equal.
    + generalize (skeleton_ctors (program_skeleton p)).
      induction c... cbn. case_eq (gfunsigs_filterfun_g tn a); intros...
      cbn. case_eq (eq_TypeName (fst (fst (gfunsigs_mapfun a))) tn); intros;
        unfold QName in *; rewrite H0.
      * cbn. f_equal... unfold gfunsigs_mapfun. destruct a. cbn.
        unfold gfunsigs_filterfun_g in H. destruct s; try discriminate...
      * exfalso. unfold gfunsigs_filterfun_g in H. destruct a.
        destruct s; try discriminate. cbn in H0. rewrite eq_TypeName_symm in H.
        rewrite H in H0. discriminate.
    + generalize (skeleton_ctors (program_skeleton p)).
      induction c... cbn. case_eq (gfunsigs_filterfun_l tn a); intros...
      cbn. case_eq (eq_TypeName (fst (fst (gfunsigs_mapfun a))) tn); intros;
        unfold QName in *; rewrite H0.
      * cbn. f_equal... unfold gfunsigs_mapfun. destruct a. cbn.
        unfold gfunsigs_filterfun_g in H. destruct s; try discriminate...
      * exfalso. unfold gfunsigs_filterfun_l in H. destruct a.
        destruct s; try discriminate. cbn in H0. rewrite eq_TypeName_symm in H.
        rewrite H in H0. discriminate.
  - intros. destruct a. cbn. apply eq_TypeName_symm.
}
assert (skeleton_cdts (program_skeleton p) = skeleton_cdts (program_skeleton pr2)).
{ subst. cbn. rewrite eq_TypeName_refl. cbn. clear - RefuncDt.
  assert (forall x, In x (skeleton_cdts (program_skeleton p)) -> In x (skeleton_cdts (program_skeleton p))).
  { intros... }
  generalize dependent H. generalize (skeleton_cdts (program_skeleton p)) at - 2.
  induction c... intros. cbn. pose proof (H a (in_eq a c)).
  case_eq (eq_TypeName tn a); intros.
  - exfalso. pose proof skeleton_dts_cdts_disjoint. unfold dts_cdts_disjoint in H2.
    unfold not in H2. rewrite eq_TypeName_eq in H1. subst. eapply H2...
  - cbn. f_equal. apply IHc. intros. apply H. right...
}
assert (skeleton_dtors (program_skeleton p) = skeleton_dtors (program_skeleton pr2)).
{ subst. cbn. rewrite filter_app. rewrite <- app_nil_l at 1. f_equal.
  - unfold computeNewCoDatatype. clear. generalize (skeleton_cfun_sigs_g (program_skeleton p)).
    generalize (skeleton_cfun_sigs_l (program_skeleton p)).
    induction c; intros.
    + cbn. rewrite app_nil_r. induction c; intros...
      cbn. case_eq (eq_TypeName (fst (fst (fst a))) tn); intros; unfold QName in *; rewrite H...
      cbn. rewrite eq_TypeName_symm. rewrite H...
    + cbn. case_eq (eq_TypeName (fst (fst (fst a))) tn); intros; unfold QName in *; rewrite H...
      cbn. rewrite filter_app. cbn. rewrite eq_TypeName_symm. rewrite H. cbn.
      rewrite <- filter_app...
  - clear - RefuncDt.
    assert (forall x, In x (skeleton_dtors (program_skeleton p)) -> In x (skeleton_dtors (program_skeleton p))).
    { intros... }
    generalize dependent H. generalize (skeleton_dtors (program_skeleton p)) at - 2.
    induction d... cbn. destruct a. destruct p0. case_eq (eq_TypeName tn (fst (unscope s))); intros.
    + exfalso. rewrite eq_TypeName_eq in H. subst. pose proof (H0 (s,l,t) (in_eq (s,l,t) d)).
      pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)). unfold cdts_dtors_in_cdts in H1.
      rewrite Forall_forall in H1. apply H1 in H.
      pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
      unfold dts_cdts_disjoint in H2. unfold not in H2. eapply H2...
    + cbn. f_equal...
}
assert (skeleton_fun_sigs (program_skeleton p) = skeleton_fun_sigs (program_skeleton pr2)).
{ subst... }
assert (skeleton_cfun_sigs_g (program_skeleton p) = skeleton_cfun_sigs_g (program_skeleton pr2)).
{ subst. cbn. unfold new_cfunsigs_g. unfold computeNewCoDatatype. unfold cfunsigs_mapfun.
  rewrite (proj1 InFront) at 1. rewrite filter_ext with (f:=(fun x : TypeName * Name * list TypeName * TypeName =>
    let (y, _) := x in let (n', _) := y in negb (eq_TypeName tn (fst n'))))
    (g:=fun x : TypeName * Name * list TypeName * TypeName => negb (eq_TypeName (fst (fst (fst x))) tn)).
  2:{ intros. destruct a. destruct p0. rewrite eq_TypeName_symm... }
  unfold QName. f_equal. rewrite filter_app. unfold Destructor.
  replace (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p))) with (@nil (ScopedName * list TypeName * TypeName)).
  2:{ case_eq (filter (cfunsigs_filterfun_g tn) (skeleton_dtors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - RefuncDt H0.
    rewrite filter_In in H0. destruct H0.
    pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)).
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold cdts_dtors_in_cdts in H1. unfold dts_cdts_disjoint in H2.
    unfold not in H2. rewrite Forall_forall in H1. apply H1 in H.
    unfold cfunsigs_filterfun_g in H0. destruct p0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0. subst. cbn in H. eapply H2... }
  rewrite app_nil_r. rewrite filter_app. rewrite map_app. rewrite <- app_nil_r at 1. f_equal.
  2:{ match goal with [|- _ = ?l] => case_eq l; intros end... clear - H.
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear H.
    rewrite in_map_iff in H0. destruct H0. destruct H. rewrite filter_In in H0.
    destruct H0. rewrite in_map_iff in H0. do 2 destruct H0. subst.
    rewrite filter_In in H2. destruct H2. rewrite eq_TypeName_eq in H0.
    subst. discriminate.
  }
  match goal with [|- _ _ ?lhs = _] => generalize lhs end. clear. induction c...
  cbn. case_eq (eq_TypeName tn (fst (fst (fst a)))); intros.
  - rewrite eq_TypeName_symm. unfold QName in *. rewrite H. cbn. rewrite H.
    cbn. rewrite <- surjective_pairing. f_equal... apply surjective_pairing.
  - rewrite eq_TypeName_symm. unfold QName in *. rewrite H...
}
assert (skeleton_cfun_sigs_l (program_skeleton p) = skeleton_cfun_sigs_l (program_skeleton pr2)).
{ subst. cbn. unfold new_cfunsigs_l. unfold computeNewCoDatatype. unfold cfunsigs_mapfun.
  rewrite (proj1 (proj2 InFront)) at 1. rewrite filter_ext with (f:=(fun x : TypeName * Name * list TypeName * TypeName =>
    let (y, _) := x in let (n', _) := y in negb (eq_TypeName tn (fst n'))))
    (g:=fun x : TypeName * Name * list TypeName * TypeName => negb (eq_TypeName (fst (fst (fst x))) tn)).
  2:{ intros. destruct a. destruct p0. rewrite eq_TypeName_symm... }
  unfold QName. f_equal. rewrite filter_app. unfold Destructor.
  replace (filter (cfunsigs_filterfun_l tn) (skeleton_dtors (program_skeleton p))) with (@nil (ScopedName * list TypeName * TypeName)).
  2:{ case_eq (filter (cfunsigs_filterfun_l tn) (skeleton_dtors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - RefuncDt H0.
    rewrite filter_In in H0. destruct H0.
    pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)).
    pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold cdts_dtors_in_cdts in H1. unfold dts_cdts_disjoint in H2.
    unfold not in H2. rewrite Forall_forall in H1. apply H1 in H.
    unfold cfunsigs_filterfun_l in H0. destruct p0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0. subst. cbn in H. eapply H2... }
  rewrite app_nil_r. rewrite filter_app. rewrite map_app. rewrite <- app_nil_l at 1. f_equal.
  { match goal with [|- _ = ?l] => case_eq l; intros end... clear - H.
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear H.
    rewrite in_map_iff in H0. destruct H0. destruct H. rewrite filter_In in H0.
    destruct H0. rewrite in_map_iff in H0. do 2 destruct H0. subst.
    rewrite filter_In in H2. destruct H2. rewrite eq_TypeName_eq in H0.
    subst. discriminate.
  }
  match goal with [|- _ _ ?lhs = _] => generalize lhs end. clear. induction c...
  cbn. case_eq (eq_TypeName tn (fst (fst (fst a)))); intros.
  - rewrite eq_TypeName_symm. unfold QName in *. rewrite H. cbn. rewrite H.
    cbn. rewrite <- surjective_pairing. f_equal... apply surjective_pairing.
  - rewrite eq_TypeName_symm. unfold QName in *. rewrite H...
}
assert (skeleton_gfun_sigs_g (program_skeleton p) = skeleton_gfun_sigs_g (program_skeleton pr2)).
{ subst. cbn. unfold new_gfunsigs_g. rewrite <- app_nil_l at 1. rewrite filter_app. f_equal.
  - match goal with [|- _ = ?l] => case_eq l; intros end...
    exfalso. clear - H. pose proof (in_eq p0 l). rewrite <- H in H0.
    rewrite filter_In in H0. rewrite in_map_iff in H0. do 3 destruct H0.
    rewrite filter_In in H2. destruct H2. pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)).
    unfold dts_ctors_in_dts in H4. rewrite Forall_forall in H4. apply H4 in H2.
    unfold gfunsigs_filterfun_g in H3. destruct p0. destruct x.
    destruct s; try discriminate. rewrite eq_TypeName_eq in H3. subst. cbn in H2.
    unfold gfunsigs_mapfun in H0. cbn in H0. inversion H0; subst. rewrite eq_TypeName_refl in H1.
    discriminate.
  - assert (forall x, In x (skeleton_gfun_sigs_g (program_skeleton p)) ->
      In x (skeleton_gfun_sigs_g (program_skeleton p))).
    { intros... }
    generalize dependent H. generalize (skeleton_gfun_sigs_g (program_skeleton p)) at - 2.
    induction g... intros. cbn. pose proof (H a (in_eq a g)). destruct a.
    case_eq (eq_TypeName tn (fst q)); intros.
    + exfalso. pose proof skeleton_dts_cdts_disjoint. unfold dts_cdts_disjoint in H9.
      unfold not in H9. rewrite eq_TypeName_eq in H8. subst. eapply H9. split...
      pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)). unfold gfun_sigs_in_cdts in H8.
      rewrite Forall_forall in H8. apply H8 in H0...
    + cbn. f_equal. apply IHg. intros. apply H. right...
}
assert (skeleton_gfun_sigs_l (program_skeleton p) = skeleton_gfun_sigs_l (program_skeleton pr2)).
{ subst. cbn. unfold new_gfunsigs_l. rewrite <- app_nil_l at 1. rewrite filter_app. f_equal.
  - match goal with [|- _ = ?l] => case_eq l; intros end...
    exfalso. clear - H. pose proof (in_eq p0 l). rewrite <- H in H0.
    rewrite filter_In in H0. rewrite in_map_iff in H0. do 3 destruct H0.
    rewrite filter_In in H2. destruct H2. pose proof (skeleton_dts_ctors_in_dts (program_skeleton p)).
    unfold dts_ctors_in_dts in H4. rewrite Forall_forall in H4. apply H4 in H2.
    unfold gfunsigs_filterfun_l in H3. destruct p0. destruct x.
    destruct s; try discriminate. rewrite eq_TypeName_eq in H3. subst. cbn in H2.
    unfold gfunsigs_mapfun in H0. cbn in H0. inversion H0; subst. rewrite eq_TypeName_refl in H1.
    discriminate.
  - assert (forall x, In x (skeleton_gfun_sigs_l (program_skeleton p)) ->
      In x (skeleton_gfun_sigs_l (program_skeleton p))).
    { intros... }
    generalize dependent H. generalize (skeleton_gfun_sigs_l (program_skeleton p)) at - 2.
    induction g... intros. cbn. pose proof (H a (in_eq a g)). destruct a.
    case_eq (eq_TypeName tn (fst q)); intros.
    + exfalso. pose proof skeleton_dts_cdts_disjoint. unfold dts_cdts_disjoint in H10.
      unfold not in H10. rewrite eq_TypeName_eq in H9. subst. eapply H10. split...
      pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)). unfold gfun_sigs_in_cdts in H9.
      rewrite Forall_forall in H9. apply H9 in H0...
    + cbn. f_equal. apply IHg. intros. apply H. right...
}
clear - H1 H2 H3 H4 H5 H6 H7 H8 H9. generalize dependent (program_skeleton p).
generalize dependent (program_skeleton pr2). intros.
destruct s0. destruct s. cbn in *. apply skeleton_split...
Qed.


Definition cfun_bods_g_for_type_in_front p tn : Prop :=
  program_cfun_bods_g p =
    filter (fun x => eq_TypeName (fst (fst x)) tn) (program_cfun_bods_g p) ++
    filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) (program_cfun_bods_g p).

Definition cfun_bods_l_for_type_in_front p tn : Prop :=
  program_cfun_bods_l p =
    filter (fun x => eq_TypeName (fst (fst x)) tn) (program_cfun_bods_l p) ++
    filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) (program_cfun_bods_l p).

Theorem redefunc_preserves_prog_aux :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton (refunctionalize_program p tn P1 P2 P3 P4 P5))))
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (* Necessary in case of empty datatype to make sure no codatatypes are defunc.ed. *)
  (RefuncDt : In tn (skeleton_dts (program_skeleton p)))
  (* In other words, the equality of programs only holds up to permutation of fundefs *)
  (InFront : cfun_bods_g_for_type_in_front p tn /\ cfun_bods_l_for_type_in_front p tn)
  (InFrontSigs : cfun_sigs_g_for_type_in_front (program_skeleton p) tn
    /\ cfun_sigs_l_for_type_in_front (program_skeleton p) tn
    /\ dt_for_type_in_front (program_skeleton p) tn
    /\ ctors_for_type_in_front (program_skeleton p) tn),
  pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  p = pr2.
Proof with eauto.
intros.
assert (program_skeleton p = program_skeleton pr2). { eapply redefunc_preserves_skeleton... }
assert (program_fun_bods p = program_fun_bods pr2).
{ subst. cbn. unfold RefuncIII.new_fun_bods. rewrite map_map.
  rewrite map_ext_in with (g:=id); try solve [rewrite map_id; eauto].
  intros. unfold id. cbn. rewrite surjective_pairing. f_equal.
  apply redefunc_exp_inverse with (p:=p); try solve [apply refunc_dt_aux; eauto]...
  right. right. apply in_map...
}
assert (program_cfun_bods_g p = program_cfun_bods_g pr2).
{ subst. match goal with [|- _ = ?rhs] => remember rhs end.
  match goal with [_ : c = _ ?p'' |- _] => set (p':=p'') in * end.
  pose proof Heqc as Work.
  cbn in Work. match goal with [_ : c = ?rhs1' ++ ?rhs2' |- _] =>
    set (rhs1:=rhs1') in Work; set (rhs2:=rhs2') in Work end.
  unfold RefuncIII.new_cfun_bods_g in *.
  assert (rhs1 = filter (fun x => eq_TypeName (fst (fst x)) tn) c) as Work1.
  { rewrite Work. rewrite filter_app. replace (filter _ rhs2) with (@nil (QName * cfun_bod)).
    2:{ unfold rhs2. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
      induction l... cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros... cbn.
      rewrite eq_TypeName_symm. rewrite H...
    }
    rewrite app_nil_r. unfold rhs1. match goal with [|- _ _ (_ _ ?l) = _] => generalize l end.
    clear. induction l... cbn. case_eq (cfunsigs_filterfun_g tn a); intros... cbn.
    case_eq (eq_TypeName (fst (unscope (fst (fst a)))) tn); intros; f_equal...
    exfalso. clear - H H0. unfold cfunsigs_filterfun_g in H. destruct a. destruct p. destruct s; try discriminate.
    cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
  }
  assert (rhs2 = filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) c) as Work2.
  { rewrite Work. rewrite filter_app. replace (filter _ rhs1) with (@nil (QName * cfun_bod)).
    2:{ unfold rhs1. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
      induction l... cbn. case_eq (cfunsigs_filterfun_g tn a); intros... cbn.
      case_eq (eq_TypeName (fst (unscope (fst (fst a)))) tn); intros; f_equal...
      exfalso. clear - H H0. unfold cfunsigs_filterfun_g in H. destruct a. destruct p. destruct s; try discriminate.
      cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
    }
    cbn. unfold rhs2. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
    induction l... cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros... cbn.
    rewrite eq_TypeName_symm. rewrite H. cbn. f_equal...
  }
  assert (rhs1 = map (fun x => (unscope (fst x), snd x))
    (filter (fun x => match fst x with global _ => true | _ => false end)
      (program_cfun_bods_for_type tn p'))) as Work1'.
  { rewrite Work1. rewrite Heqc. unfold program_cfun_bods_for_type.
    rewrite filter_filter. rewrite filter_app. erewrite (@filter_ext (ScopedName * cfun_bod)).
    { rewrite filter_map. f_equal; try reflexivity.
      match goal with [|- _ = _ _ (_ ++ ?l)] => replace l with (@nil (ScopedName * cfun_bod)) end.
      2:{ generalize (program_cfun_bods_l p'). induction c0... }
      rewrite app_nil_r. generalize (program_cfun_bods_g p'). induction c0...
      cbn. rewrite <- surjective_pairing. f_equal...
    }
    intros...
  }
  erewrite <- redefunc_preserves_cfuns with (p:=p) in Work1'...
  2:{ unfold p'... }
  rewrite (proj1 InFront). rewrite Work. rewrite Work1'. unfold rhs2.
  unfold program_cfun_bods_for_type. do 2 rewrite filter_app. do 2 rewrite filter_compose.
  rewrite map_app.
  match goal with [|- _ = (_ ?m (_ ?f1 ?l1) ++ _ ?m (_ ?f2 ?l2)) ++ _] =>
    replace (map m (filter f1 l1)) with
      (filter (fun x : QName * gfun_bod => eq_TypeName (fst (fst x)) tn) (map m l1));
    [ replace (filter f2 l2) with (@nil (ScopedName * gfun_bod)) |] end.
  2:{ generalize (program_cfun_bods_l p). induction c0... }
  2:{ generalize (program_cfun_bods_g p). induction c0... cbn.
    case_eq (eq_TypeName (fst (fst a)) tn); intros... cbn. f_equal...
  }
  cbn. rewrite app_nil_r. rewrite map_map. cbn. erewrite map_ext.
  2:{ intros. rewrite <- surjective_pairing. reflexivity. }
  rewrite map_id. f_equal.
  rewrite <- filter_map. rewrite map_map. cbn. rewrite map_ext_in with (g:=id).
  2:{ intros. destruct a. cbn. unfold id. f_equal. rewrite map_map. cbn.
    rewrite map_ext_in with (g:=id); [ rewrite map_id | ]...
    intros. rewrite redefunc_exp_inverse with (p:=p); try solve [apply refunc_dt_aux; eauto]...
    - unfold id. rewrite <- surjective_pairing...
    - clear - H H0. left. apply in_map. rewrite in_flat_map. unfold program_gfun_bods.
      rewrite filter_In in H. destruct H. exists (global q,l). split...
      apply in_or_app. left. rewrite in_map_iff. exists (q,l). split...
   }
   rewrite map_id. apply filter_ext. intros. f_equal. apply eq_TypeName_symm.
}
assert (program_cfun_bods_l p = program_cfun_bods_l pr2).
{ subst. match goal with [|- _ = ?rhs] => remember rhs end.
  match goal with [_ : c = _ ?p'' |- _] => set (p':=p'') in * end.
  pose proof Heqc as Work.
  cbn in Work. match goal with [_ : c = ?rhs1' ++ ?rhs2' |- _] =>
    set (rhs1:=rhs1') in Work; set (rhs2:=rhs2') in Work end.
  unfold RefuncIII.new_cfun_bods_l in *.
  assert (rhs1 = filter (fun x => eq_TypeName (fst (fst x)) tn) c) as Work1.
  { rewrite Work. rewrite filter_app. replace (filter _ rhs2) with (@nil (QName * cfun_bod)).
    2:{ unfold rhs2. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
      induction l... cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros... cbn.
      rewrite eq_TypeName_symm. rewrite H...
    }
    rewrite app_nil_r. unfold rhs1. match goal with [|- _ _ (_ _ ?l) = _] => generalize l end.
    clear. induction l... cbn. case_eq (cfunsigs_filterfun_l tn a); intros... cbn.
    case_eq (eq_TypeName (fst (unscope (fst (fst a)))) tn); intros; f_equal...
    exfalso. clear - H H0. unfold cfunsigs_filterfun_l in H. destruct a. destruct p. destruct s; try discriminate.
    cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
  }
  assert (rhs2 = filter (fun x => negb (eq_TypeName (fst (fst x)) tn)) c) as Work2.
  { rewrite Work. rewrite filter_app. replace (filter _ rhs1) with (@nil (QName * cfun_bod)).
    2:{ unfold rhs1. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
      induction l... cbn. case_eq (cfunsigs_filterfun_l tn a); intros... cbn.
      case_eq (eq_TypeName (fst (unscope (fst (fst a)))) tn); intros; f_equal...
      exfalso. clear - H H0. unfold cfunsigs_filterfun_l in H. destruct a. destruct p. destruct s; try discriminate.
      cbn in H0. rewrite eq_TypeName_symm in H0. rewrite H in H0. discriminate.
    }
    cbn. unfold rhs2. clear. match goal with [|- _ = _ _ (_ _ (_ _ ?l))] => generalize l end.
    induction l... cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros... cbn.
    rewrite eq_TypeName_symm. rewrite H. cbn. f_equal...
  }
  assert (rhs1 = map (fun x => (unscope (fst x), snd x))
    (filter (fun x => match fst x with global _ => false | _ => true end)
      (program_cfun_bods_for_type tn p'))) as Work1'.
  { rewrite Work1. rewrite Heqc. unfold program_cfun_bods_for_type.
    rewrite filter_filter. rewrite filter_app. erewrite (@filter_ext (ScopedName * cfun_bod)).
    { rewrite filter_map. f_equal; try reflexivity.
      match goal with [|- _ = _ _ (?l ++ _)] => replace l with (@nil (ScopedName * cfun_bod)) end.
      2:{ generalize (program_cfun_bods_g p'). induction c0... }
      generalize (program_cfun_bods_l p'). induction c0...
      cbn. rewrite <- surjective_pairing. f_equal...
    }
    intros...
  }
  erewrite <- redefunc_preserves_cfuns with (p:=p) in Work1'...
  2:{ unfold p'... }
  rewrite (proj2 InFront). rewrite Work. rewrite Work1'. unfold rhs2.
  unfold program_cfun_bods_for_type. do 2 rewrite filter_app. do 2 rewrite filter_compose.
  rewrite map_app.
  match goal with [|- _ = (_ ?m (_ ?f1 ?l1) ++ _ ?m (_ ?f2 ?l2)) ++ _] =>
    replace (map m (filter f2 l2)) with
      (filter (fun x : QName * cfun_bod => eq_TypeName (fst (fst x)) tn) (map m l2));
    [ replace (filter f1 l1) with (@nil (ScopedName * cfun_bod)) |] end.
  2:{ generalize (program_cfun_bods_g p). induction c0... }
  2:{ generalize (program_cfun_bods_l p). induction c0... cbn.
    case_eq (eq_TypeName (fst (fst a)) tn); intros... cbn. f_equal...
  }
  cbn. rewrite map_map. cbn. erewrite map_ext.
  2:{ intros. rewrite <- surjective_pairing. reflexivity. }
  rewrite map_id. f_equal.
  rewrite <- filter_map. rewrite map_map. cbn. rewrite map_ext_in with (g:=id).
  2:{ intros. destruct a. cbn. unfold id. f_equal. rewrite map_map. cbn.
    rewrite map_ext_in with (g:=id); [ rewrite map_id | ]...
    intros. rewrite redefunc_exp_inverse with (p:=p); try solve [apply refunc_dt_aux; eauto]...
    - unfold id. rewrite <- surjective_pairing...
    - clear - H H0. left. apply in_map. rewrite in_flat_map. unfold program_cfun_bods.
      rewrite filter_In in H. destruct H. exists (local q,l). split...
      apply in_or_app. right. rewrite in_map_iff. exists (q,l). split...
   }
   rewrite map_id. apply filter_ext. intros. f_equal. apply eq_TypeName_symm.
}
assert (program_gfun_bods_g p = program_gfun_bods_g pr2).
{ subst. match goal with [|- _ = ?rhs] => remember rhs end.
  match goal with [_ : g = _ ?p'' |- _] => set (p':=p'') in * end.
  pose proof Heqg as Work.
  cbn in Work.
  unfold RefuncIII.new_gfun_bods_g in *.
  rewrite map_app in Work. rewrite map_map in Work. rewrite filter_app in Work.
  match goal with [_ : g = ?rhs1' ++ ?rhs2' |- _] =>
    set (rhs1:=rhs1') in Work; set (rhs2:=rhs2') in Work end.
  assert (rhs1 = []) as Work1.
  { unfold rhs1. clear. generalize (skeleton_ctors (program_skeleton p)).
    induction c... cbn. case_eq (gfunsigs_filterfun_g tn a); intros...
    cbn. case_eq (eq_TypeName tn (fst (unscope (fst a)))); intros...
    exfalso. clear - H H0. unfold gfunsigs_filterfun_g in H. destruct a.
    destruct s; try discriminate. cbn in H0. rewrite H in H0. discriminate.
  }
  assert (rhs2 = program_gfun_bods_g p) as Work2.
  { unfold rhs2. rewrite map_map. cbn. rewrite map_ext_in with (g:=id).
    2:{ intros. rewrite map_map. rewrite map_ext_in with (g:=id).
      2:{ intros. cbn. unfold id.
          rewrite redefunc_exp_inverse with (p:=p); try solve [apply refunc_dt_aux; eauto]...
        - rewrite <- surjective_pairing...
        - clear - H H0. right. left. apply in_map. rewrite in_flat_map. unfold program_cfun_bods.
          destruct a. exists (global q,l). split...
          apply in_or_app. left. rewrite in_map_iff. exists (q,l). split...
      }
      unfold id. rewrite map_id. symmetry. apply surjective_pairing.
    }
    unfold id. rewrite map_id. clear - RefuncDt.
    assert (forall x, In x (program_gfun_bods_g p) -> In x (program_gfun_bods_g p)).
    { intros... }
    generalize dependent H. generalize (program_gfun_bods_g p) at - 2. induction g; intros...
    cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros.
    - exfalso. pose proof (H (q,g0) (in_eq (q,g0) g)). apply (in_map fst) in H1.
      cbn in H1. rewrite <- program_has_all_gfun_bods_g in H1.
      rewrite in_map_iff in H1. do 2 destruct H1.
      pose proof (skeleton_gfun_sigs_in_cdts_g (program_skeleton p)).
      unfold gfun_sigs_in_cdts in H3. rewrite Forall_forall in H3.
      apply H3 in H2. subst. rewrite eq_TypeName_eq in H0. subst.
      pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
      unfold dts_cdts_disjoint in H0. unfold not in H0. eapply H0...
    - cbn. f_equal. apply IHg. intros. apply H. right...
  }
  rewrite Work. rewrite Work1. rewrite Work2...
}
assert (program_gfun_bods_l p = program_gfun_bods_l pr2).
{ subst. match goal with [|- _ = ?rhs] => remember rhs end.
  match goal with [_ : g = _ ?p'' |- _] => set (p':=p'') in * end.
  pose proof Heqg as Work.
  cbn in Work.
  unfold RefuncIII.new_gfun_bods_l in *.
  rewrite map_app in Work. rewrite map_map in Work. rewrite filter_app in Work.
  match goal with [_ : g = ?rhs1' ++ ?rhs2' |- _] =>
    set (rhs1:=rhs1') in Work; set (rhs2:=rhs2') in Work end.
  assert (rhs1 = []) as Work1.
  { unfold rhs1. clear. generalize (skeleton_ctors (program_skeleton p)).
    induction c... cbn. case_eq (gfunsigs_filterfun_l tn a); intros...
    cbn. case_eq (eq_TypeName tn (fst (unscope (fst a)))); intros...
    exfalso. clear - H H0. unfold gfunsigs_filterfun_l in H. destruct a.
    destruct s; try discriminate. cbn in H0. rewrite H in H0. discriminate.
  }
  assert (rhs2 = program_gfun_bods_l p) as Work2.
  { unfold rhs2. rewrite map_map. cbn. rewrite map_ext_in with (g:=id).
    2:{ intros. rewrite map_map. rewrite map_ext_in with (g:=id).
      2:{ intros. cbn. unfold id.
          rewrite redefunc_exp_inverse with (p:=p); try solve [apply refunc_dt_aux; eauto]...
        - rewrite <- surjective_pairing...
        - clear - H H0. right. left. apply in_map. rewrite in_flat_map. unfold program_cfun_bods.
          destruct a. exists (local q,l). split...
          apply in_or_app. right. rewrite in_map_iff. exists (q,l). split...
      }
      unfold id. rewrite map_id. symmetry. apply surjective_pairing.
    }
    unfold id. rewrite map_id. clear - RefuncDt.
    assert (forall x, In x (program_gfun_bods_l p) -> In x (program_gfun_bods_l p)).
    { intros... }
    generalize dependent H. generalize (program_gfun_bods_l p) at - 2. induction g; intros...
    cbn. destruct a. case_eq (eq_TypeName tn (fst q)); intros.
    - exfalso. pose proof (H (q,g0) (in_eq (q,g0) g)). apply (in_map fst) in H1.
      cbn in H1. rewrite <- program_has_all_gfun_bods_l in H1.
      rewrite in_map_iff in H1. do 2 destruct H1.
      pose proof (skeleton_gfun_sigs_in_cdts_l (program_skeleton p)).
      unfold gfun_sigs_in_cdts in H3. rewrite Forall_forall in H3.
      apply H3 in H2. subst. rewrite eq_TypeName_eq in H0. subst.
      pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
      unfold dts_cdts_disjoint in H0. unfold not in H0. eapply H0...
    - cbn. f_equal. apply IHg. intros. apply H. right...
  }
  rewrite Work. rewrite Work1. rewrite Work2...
}
subst. unfold defunctionalize_program. destruct p. apply prog_split...
Qed.

Lemma global_before_local_dtors_refunc :
forall p tn P1 P2 P3 P4 P5 (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (RefuncDt : In tn (skeleton_dts (program_skeleton p))),
  global_before_local_dtors (skeleton_dtors (program_skeleton (refunctionalize_program p tn P1 P2 P3 P4 P5))).
Proof with eauto.
intros. unfold global_before_local_dtors in *. intros.
cbn. clear - GLd RefuncDt. case_eq (eq_TypeName tn tn0); intros.
- rewrite eq_TypeName_eq in H. subst. repeat rewrite filter_app.
  match goal with [|- (_ ++ ?l1) ++ (_ ++ ?l2) = _ ++ ?l3] =>
    replace l1 with (@nil Destructor); [ replace l2 with (@nil Destructor) |];
    [ replace l3 with (@nil Destructor) | |]
  end.
  2:{ case_eq (filter (fun x : ScopedName * list TypeName * TypeName => eq_TypeName (fst (unscope (fst (fst x)))) tn0)
        (skeleton_dtors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - H0 RefuncDt.
    rewrite filter_In in H0. destruct H0. pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)).
    unfold cdts_dtors_in_cdts in H1. rewrite Forall_forall in H1. apply H1 in H.
    rewrite eq_TypeName_eq in H0. subst. pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H0. unfold not in H0...
  }
  2:{ case_eq (filter (cfunsigs_filterfun_l tn0) (skeleton_dtors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - H0 RefuncDt.
    rewrite filter_In in H0. destruct H0. pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)).
    unfold cdts_dtors_in_cdts in H1. rewrite Forall_forall in H1. apply H1 in H.
    unfold cfunsigs_filterfun_l in H0. destruct p0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0. subst. pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H0. unfold not in H0...
  }
  2:{ case_eq (filter (cfunsigs_filterfun_g tn0) (skeleton_dtors (program_skeleton p))); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H in H0. clear - H0 RefuncDt.
    rewrite filter_In in H0. destruct H0. pose proof (skeleton_cdts_dtors_in_cdts (program_skeleton p)).
    unfold cdts_dtors_in_cdts in H1. rewrite Forall_forall in H1. apply H1 in H.
    unfold cfunsigs_filterfun_g in H0. destruct p0. destruct p0. destruct s; try discriminate.
    rewrite eq_TypeName_eq in H0. subst. pose proof (skeleton_dts_cdts_disjoint (program_skeleton p)).
    unfold dts_cdts_disjoint in H0. unfold not in H0...
  }
  repeat rewrite app_nil_r. unfold computeNewCoDatatype.
  generalize (skeleton_cfun_sigs_g (program_skeleton p)).
  generalize (skeleton_cfun_sigs_l (program_skeleton p)).
  clear. intros. repeat rewrite filter_app.
  match goal with [|- (_ ++ ?l1) ++ (?l2 ++ _) = _] =>
    replace l1 with (@nil Destructor); [ replace l2 with (@nil Destructor) |]
  end.
  2:{ induction c0... cbn.
    case_eq (eq_TypeName (fst (fst (fst a))) tn0); intros; unfold QName in *; rewrite H...
  }
  2:{ induction c... cbn.
    case_eq (eq_TypeName (fst (fst (fst a))) tn0); intros; unfold QName in *; rewrite H...
  }
  repeat rewrite app_nil_r. f_equal.
  + induction c0... cbn.
    case_eq (eq_TypeName (fst (fst (fst a))) tn0); intros; unfold QName in *; rewrite H...
    cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
  + cbn. induction c... cbn.
    case_eq (eq_TypeName (fst (fst (fst a))) tn0); intros; unfold QName in *; rewrite H...
    cbn. rewrite eq_TypeName_symm. rewrite H. f_equal...
- repeat rewrite filter_app.
  match goal with [|- (?l1 ++ _) ++ (?l2 ++ _) = ?l3 ++ _] =>
    replace l1 with (@nil Destructor); [ replace l2 with (@nil Destructor) |];
    [ replace l3 with (@nil Destructor) | |]
  end.
  2:{ case_eq (filter (fun x : ScopedName * list TypeName * TypeName => eq_TypeName (fst (unscope (fst (fst x)))) tn0)
        (computeNewCoDatatype p tn)); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H0 in H1. clear - H H1.
    rewrite filter_In in H1. destruct H1. unfold computeNewCoDatatype in H0. apply in_app_or in H0.
    destruct H0; rewrite in_map_iff in H0; do 2 destruct H0; subst;
      rewrite filter_In in H2; destruct H2; cbn in H1; rewrite eq_TypeName_eq in *; subst;
      rewrite eq_TypeName_refl in H; discriminate.
  }
  2:{ case_eq (filter (cfunsigs_filterfun_l tn0) (computeNewCoDatatype p tn)); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H0 in H1. clear - H H1.
    rewrite filter_In in H1. destruct H1. unfold computeNewCoDatatype in H0. apply in_app_or in H0.
    destruct H0; rewrite in_map_iff in H0; do 2 destruct H0; subst;
      rewrite filter_In in H2; destruct H2; cbn in H1; rewrite eq_TypeName_eq in *; subst;
      try rewrite eq_TypeName_refl in H; discriminate.
  }
  2:{ case_eq (filter (cfunsigs_filterfun_g tn0) (computeNewCoDatatype p tn)); intros...
    exfalso. pose proof (in_eq p0 l). rewrite <- H0 in H1. clear - H H1.
    rewrite filter_In in H1. destruct H1. unfold computeNewCoDatatype in H0. apply in_app_or in H0.
    destruct H0; rewrite in_map_iff in H0; do 2 destruct H0; subst;
      rewrite filter_In in H2; destruct H2; cbn in H1; rewrite eq_TypeName_eq in *; subst;
      try rewrite eq_TypeName_refl in H; discriminate.
  }
  eauto.
Qed.





(* Final results *)

Theorem derefunc_preserves_prog :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (* Necessary in case of empty codatatype to make sure no datatypes are defunc.ed. *)
  (DefuncCdt : In tn (skeleton_cdts (program_skeleton p)))
  (* In other words, the equality of programs only holds up to permutation of fundefs *)
  (InFront : gfun_bods_g_for_type_in_front p tn /\ gfun_bods_l_for_type_in_front p tn)
  (InFrontSigs : gfun_sigs_g_for_type_in_front (program_skeleton p) tn
    /\ gfun_sigs_l_for_type_in_front (program_skeleton p) tn
    /\ cdt_for_type_in_front (program_skeleton p) tn
    /\ dtors_for_type_in_front (program_skeleton p) tn),
  pr  = defunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = refunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  p = pr2.
Proof with eauto.
intros. eapply derefunc_preserves_prog_aux... apply global_before_local_ctors_defunc...
Qed.

Theorem redefunc_preserves_prog :
forall p tn P1 P2 P3 P4 P5 pr P1' P2' P3' P4' P5' pr2
  (GLd : global_before_local_dtors (skeleton_dtors (program_skeleton p)))
  (GLc : global_before_local_ctors (skeleton_ctors (program_skeleton p)))
  (* Necessary in case of empty datatype to make sure no codatatypes are defunc.ed. *)
  (RefuncDt : In tn (skeleton_dts (program_skeleton p)))
  (* In other words, the equality of programs only holds up to permutation of fundefs *)
  (InFront : cfun_bods_g_for_type_in_front p tn /\ cfun_bods_l_for_type_in_front p tn)
  (InFrontSigs : cfun_sigs_g_for_type_in_front (program_skeleton p) tn
    /\ cfun_sigs_l_for_type_in_front (program_skeleton p) tn
    /\ dt_for_type_in_front (program_skeleton p) tn
    /\ ctors_for_type_in_front (program_skeleton p) tn),
  pr  = refunctionalize_program p  tn P1  P2  P3  P4  P5  ->
  pr2 = defunctionalize_program pr tn P1' P2' P3' P4' P5' ->
  p = pr2.
Proof with eauto.
intros. eapply redefunc_preserves_prog_aux... apply global_before_local_dtors_refunc...
Qed.

Print Assumptions derefunc_preserves_prog.
Print Assumptions redefunc_preserves_prog.

