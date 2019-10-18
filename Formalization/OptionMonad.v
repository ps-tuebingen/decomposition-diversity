(**************************************************************************************************)
(* Total Constructor/Destructorization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: OptionMonad.v                                                                            *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Lists.List.
Import ListNotations.

(**************************************************************************************************)
(** ** Monadic operations for option                                                              *)
(**                                                                                               *)
(**************************************************************************************************)

Definition fmap {A B : Type} (f : A -> B) (a : option A) : option B :=
  match a with
  | None => None
  | Some a' => Some (f a')
  end.

Definition eta {A : Type} (a : A) : option A := Some a.

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
  | None => None
  | Some a' => f a'
  end.
Notation "a '>>=' f" := (bind a f) (at level 42, right associativity).

Definition mu {A : Type} : option (option A) -> option A := fun x => x >>= (fmap id).

Lemma monad_law1 : forall (A B : Type) (a : A) (f : A -> option B), eta a >>= f = f a.
Proof. intros. simpl. reflexivity. Qed.

Lemma monad_law2 : forall (A B : Type) (a : option A), a >>= eta = a.
Proof. intros. destruct a; reflexivity. Qed.

Lemma monad_law3 : forall (A B C : Type) (a : option A) (f : A -> option B) (g : B -> option C),
    (a >>= f) >>= g = a >>= (fun x => f x >>= g).
Proof. intros. destruct a; reflexivity. Qed.

Definition option_fail {A : Type} (a : option A) : bool :=
  match a with
  | None => false
  | Some _ => true
  end.

Theorem bind_some : forall {A B : Type} (f : option A) (g : A -> option B) (b : B),
    f >>= g = Some b -> exists a, f = Some a.
Proof.
  intros A B f g b H. destruct f; try (solve [inversion H]).
  exists a. reflexivity.
Qed.

Ltac option_bind_tac :=
  match goal with
    [ H : ?F >>= ?G = Some ?B |- _ ] => let bind := fresh "H_bind" in
                                        assert (bind := H);
                                        apply bind_some in bind
  end.

Lemma none_propagates : forall (A B : Type) (a : option A) (f : A -> option B),
    a = None -> a >>= f = None.
Proof.
  intros.  rewrite H. reflexivity.
Qed.

Lemma eta_always_something : forall (A B : Type) (ma : option A) (f : A -> B),
    ma >>= (fun a => eta (f a)) = None <-> ma = None.
Proof.
  intros.
  unfold iff. refine (conj _ _).
  -intros. unfold bind in H. induction ma.
   +unfold eta in H. discriminate H.
   +reflexivity.
  -intros. unfold bind. rewrite H. reflexivity.
Qed.

Lemma eta_composition : forall {A B C : Type} (ma : option A) (f : A -> B) (g : B -> C),
    ma >>= (fun a => eta (f a) >>= (fun b => eta (g b))) = ma >>= fun a => eta (g (f a)).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma eta_cong : forall {A B C : Type} (a : A) (ma : option A) (f : A -> B) (g : B -> C),
    ma >>= (fun a' => eta (f a')) = eta (f a) ->
    ma >>= (fun a' => eta (g (f a'))) = eta (g (f a)).
Proof.
  intros A B C a ma f g E.
  destruct ma; try solve [inversion E].
  simpl. apply f_equal with (f := eta). apply f_equal with (f := g). inversion E. reflexivity.
Qed.

Lemma eta_cong2 : forall {A B : Type} (a : A) (ma : option A) (f : A -> B),
    ma = eta a ->
    ma >>= (fun a' => eta (f a')) = eta (f a).
Proof.
  intros. apply eta_cong with (f0 := id). unfold id. rewrite monad_law2; try assumption.
Qed.


Definition isSome {A} (x : option A) : bool :=
  match x with
  | Some _ => true
  | None => false
  end.

(* Sequences monadic computation (option monad only) *)
Fixpoint sequence {A : Type} (l : list (option A)) : option (list A) :=
  match l with
  | nil   => Some nil
  | x::xs => match x with None => None | Some x' => sequence xs >>= fun xs' => Some (x' :: xs') end
  end.


Lemma Forall2_sequence : forall {A X} {P : A -> A -> X -> Prop} {Q: A -> X -> Prop} {ls ls' : list A} {f},
  Forall (fun a : A => forall args : X, Q a args -> forall a' : A, f a = Some a' -> P a a' args) ls ->
  sequence (map f ls) = Some ls' ->
  Forall2 (fun a1 a2 => forall args : X, Q a1 args -> P a1 a2 args) ls ls'.
Proof.
  intros. generalize dependent ls'. induction ls.
  * intros. simpl in H0. inversion H0. apply Forall2_nil.
  * intros.
    inversion H; subst.
    destruct ls'.
  + simpl in H0.
    case_eq (f a).
    intros. rewrite H1 in H0.
    case_eq (sequence (map f ls)); try (intros; rewrite H2 in H0; simpl in H0; discriminate).
    intros. rewrite H1 in H0. discriminate.
  + apply Forall2_cons.
    intros. pose proof (H3 args H1). apply H2.
    simpl in H0.
    case_eq (f a). intros. rewrite H5 in H0.
    case_eq (sequence (map f ls)). intros. rewrite H6 in H0. simpl in H0. inversion H0; subst. reflexivity.
    intros. rewrite H6 in H0. simpl in H0. discriminate.
    intros. rewrite H5 in H0. discriminate.
    apply IHls. assumption.
    simpl in H0. case_eq (sequence (map f ls)).
    intros. case_eq (f a).
    intros. rewrite H2 in H0. rewrite H1 in H0. simpl in H0. inversion H0; subst. reflexivity.
    intros. rewrite H2 in H0. discriminate.
    intros. case_eq (f a).
    intros. rewrite H2 in H0. rewrite H1 in H0. simpl in H0. discriminate.
    intros. rewrite H2 in H0. discriminate.
Qed.

Lemma sequence_map_fst : forall {A B : Type} es es' f,
  sequence (map (fun x : A * B =>
                   f (fst x) >>= (fun y : A => eta (y, snd x)))
                 es) = Some es' ->
  sequence (map f (map fst es)) = Some (map fst es').
Proof.
  intros. generalize dependent es'. induction es.
  * intros. simpl. destruct es'. simpl. reflexivity.
    simpl in H. discriminate.
  * intros. destruct es'. simpl in H.
    case_eq (f (fst a)).
    intros. rewrite H0 in H. simpl in H.
    case_eq (sequence
               (map
                  (fun x : A * B =>
                     f (fst x) >>=
                       (fun y : A => eta (y, snd x))) es)).
    intros. rewrite H1 in H. simpl in H. discriminate.
    intros. rewrite H1 in H. simpl in H. discriminate.
    intros. rewrite H0 in H. simpl in H. discriminate.
    simpl.
    case_eq (f (fst a)).
    intros. erewrite IHes. simpl. f_equal. f_equal.
    simpl in H. rewrite H0 in H. simpl in H.
    case_eq (sequence
               (map
                  (fun x : A * B =>
                     f (fst x) >>=
                       (fun y : A => eta (y, snd x))) es)).
    intros. rewrite H1 in H. simpl in H. inversion H; subst. simpl. reflexivity.
    intros. rewrite H1 in H. simpl in H. discriminate.
    simpl in H. rewrite H0 in H. simpl in H.
    case_eq (sequence
               (map
                  (fun x : A * B =>
                     f (fst x) >>=
                       (fun y : A => eta (y, snd x))) es) ).
    intros. rewrite H1 in H. simpl in H. inversion H; subst. reflexivity.
    intros. rewrite H1 in H. simpl in H. discriminate.
    intros. simpl in H. rewrite H0 in H. simpl in H. discriminate.
Qed.

Lemma sequence_map_snd : forall {A B : Type} es es' f,
  sequence (map (fun x : A * B =>
                   f (snd x) >>= (fun y : B => eta (fst x, y)))
                 es) = Some es' ->
  sequence (map f (map snd es)) = Some (map snd es').
Proof.
  intros. generalize dependent es'. induction es.
  * intros. simpl. destruct es'. simpl. reflexivity.
    simpl in H. discriminate.
  * intros. destruct es'. simpl in H.
    case_eq (f (snd a)).
    intros. rewrite H0 in H. simpl in H.
    case_eq (sequence
               (map
                  (fun x : A * B =>
                     f (snd x) >>=
                       (fun y : B => eta (fst x, y))) es)).
    intros. rewrite H1 in H. simpl in H. discriminate.
    intros. rewrite H1 in H. simpl in H. discriminate.
    intros. rewrite H0 in H. simpl in H. discriminate.
    simpl.
    case_eq (f (snd a)).
    intros. erewrite IHes. simpl. f_equal. f_equal.
    simpl in H. rewrite H0 in H. simpl in H.
    case_eq (sequence
               (map
                  (fun x : A * B =>
                     f (snd x) >>=
                       (fun y : B => eta (fst x, y))) es)).
    intros. rewrite H1 in H. simpl in H. inversion H; subst. simpl. reflexivity.
    intros. rewrite H1 in H. simpl in H. discriminate.
    simpl in H. rewrite H0 in H. simpl in H.
    case_eq (sequence
               (map
                  (fun x : A * B =>
                     f (snd x) >>=
                       (fun y : B => eta (fst x, y))) es) ).
    intros. rewrite H1 in H. simpl in H. inversion H; subst. reflexivity.
    intros. rewrite H1 in H. simpl in H. discriminate.
    intros. simpl in H. rewrite H0 in H. simpl in H. discriminate.
Qed.


Lemma sequence_some_forall_some : forall {X Y : Type} (f : X -> option Y) (xs : list X),
    Forall (fun x => exists y : Y, f x = Some y) xs <->
    exists ys : list Y, sequence (map f xs) = Some ys.
Proof.
  intros X Y f xs. split.
  - intro H. induction xs.
    + exists []. reflexivity.
    + simpl. inversion H as [|_x __x Ha_some Htail _y]; subst.
      inversion Ha_some as [y Ha_some']; subst. rewrite Ha_some'.
      apply IHxs in Htail. inversion Htail as [ys' Eseq].
      rewrite Eseq. simpl. exists (y :: ys'). reflexivity.
  - intros H. induction xs; try apply Forall_nil.
    simpl in H. destruct (f a) eqn:Ea; try solve [inversion H as [x' H']; inversion H'].
    apply Forall_cons.
    + exists y; rewrite Ea; reflexivity.
    + apply IHxs. destruct (sequence (map f xs)).
      * exists l; reflexivity.
      * simpl in H. inversion H as [ys H']; inversion H'.
Qed.

Lemma sequence_length : forall (A : Type)(ls : list (option A))(ls' : list A),
    sequence ls = Some ls' -> length ls = length ls'.
Proof.
  intros A ls ls' H.
  generalize dependent ls'. induction ls.
  - intros ls' H. simpl in *. inversion H. reflexivity.
  - intros ls' H. destruct ls'.
    + simpl in *. destruct a.
      *option_bind_tac. destruct H_bind. rewrite H0 in H. simpl in *.  inversion H.
      *inversion H.
    + simpl. f_equal. apply IHls. destruct a.
      *simpl in *. option_bind_tac. destruct H_bind. rewrite H0 in H. simpl in *. inversion H; subst. assumption.
      *simpl in *. inversion H.
Qed.

Lemma sequence_cons : forall (A B : Type) (f : A -> option B) (x : A) (xs : list A) (y : B) (ys : list B),
    sequence (map f (x :: xs)) = Some (y :: ys) ->
    f x = Some y /\
    sequence (map f xs) = Some ys.
Proof.
  intros A B f x xs y ys H. simpl in *. destruct (f x) eqn:E ; try inversion H.
  option_bind_tac. destruct H_bind. rewrite H0 in H. simpl in *. inversion H; subst. rewrite H0.
  split; reflexivity.
Qed.

Lemma sequence_contradiction : forall (A B : Type) (f : A -> option B) (x : A) (xs : list A),
    ~ (sequence (map f (x :: xs)) = Some []).
Proof.
  intros A B f x xs H. simpl in *. destruct (f x); try inversion H.
  option_bind_tac. destruct H_bind. rewrite H0 in H. simpl in *. inversion H.
Qed.

Lemma sequence_map_some : forall (A B: Type)(f : A -> option B) (ls : list A),
    Forall (fun x => exists y, f x = Some y)  ls ->
    exists ls', sequence (map f ls) = Some ls'.
Proof.
  intros A B f ls H_forall. induction ls.
  - exists []. simpl. reflexivity.
  - inversion H_forall; subst. destruct H1. apply IHls in H2. destruct H2. exists (x :: x0).
    simpl. rewrite H. rewrite H0. simpl. reflexivity.
Qed.

Lemma sequence_map_some' : forall (A B: Type)(f : A -> option B) (ls : list A)(ls' : list B),
    sequence (map f ls) = Some ls' ->
    Forall (fun x => match f x with None => False | Some _ => True end)  ls.
Proof.
  intros A B f ls ls'. generalize dependent ls'. induction ls; simpl; intros ls' H; try apply Forall_nil.
  apply Forall_cons.
  - destruct (f a) eqn:E; try (solve [inversion H]). auto.
  - destruct (f a) eqn:E; try (solve [inversion H]). option_bind_tac. destruct H_bind. rewrite H0 in H. apply IHls in H0.
    assumption.
Qed.


(**************************************************************************************************)
(** ** Definition of Injective                                                                    *)
(**                                                                                               *)
(**************************************************************************************************)

Definition Injective {A B} (f : A -> B) :=
  forall x y, f x = f y -> x = y.

Lemma eta_cong_inj : forall {A B C : Type} (ma : option A) (a : A) (g : A -> B) (f : B -> C),
    Injective f ->
    ma >>= (fun a' => eta (f (g a'))) = eta (f (g a)) ->
    ma >>= (fun a' => eta (g a')) = eta (g a).
Proof.
  intros. unfold Injective in H.
  destruct ma.
  -simpl. apply f_equal.  apply H. simpl in H0. inversion H0. reflexivity.
  -simpl in H0. inversion H0.
Qed.

Lemma eta_cong_inj2 : forall {A B : Type} (ma : option A) (a : A) (g : A -> A) (f : A -> B),
    Injective f ->
    Injective g ->
    ma >>= (fun a' => eta (f (g a'))) = eta (f (g a)) ->
    ma >>= (fun a' => eta (f a')) = eta (f a).
Proof.
  intros A B ma a g f HinjF HinjG H.
  destruct ma; try solve [inversion H].
  simpl. simpl in H. unfold Injective in *.
   do 2 apply f_equal. inversion H.
   apply HinjF in H1. apply HinjG in H1. assumption.
Qed.

Lemma eta_cong_inj_rev : forall {A B : Type} (ma : option A) (a : A) (g : A -> A) (f : A -> B),
    Injective f ->
    ma >>= (fun a' => eta (f a')) = eta (f a) ->
    ma >>= (fun a' => eta (f (g a'))) = eta (f (g a)).
Proof.
  intros A B ma a g f Hinj H.
  destruct ma; try solve [inversion H].
  simpl in *. apply f_equal. apply f_equal. inversion H.
  unfold Injective in Hinj. apply Hinj in H1. rewrite H1. reflexivity.
Qed.

Ltac combine_etas :=
  try rewrite monad_law3;
  rewrite eta_composition;
  try combine_etas.


(**************************************************************************************************)
(** ** bind prime                                                                                 *)
(**                                                                                               *)
(**************************************************************************************************)
Definition option_bind_prime {A B : Type} (a : option A) (f : {a' : A | a = Some a'} -> option B) : option B :=
  match a as q return a = q -> option B with
  | None => fun _ => None
  | Some a' => fun eq => f (exist (fun x => a = Some x) a' eq)
  end (eq_refl a).

Notation "a '>>==' f" := (option_bind_prime a f) (at level 42, right associativity).

Definition eta_prime {A : Type} (p : { a : A | Some a = Some a}) : option A :=
  match p with
  | exist _ a eq => eta a
  end.

Lemma bind_some_prime {A B : Type}: forall (ma : option A) (f : {a' : A | ma = Some a'} -> option B) (b : B),
    ma >>== f = Some b ->
    exists a : A, ma = Some a.
Proof.
  intros ma f b H.
  destruct ma as [a|].
  * simpl in H.
    exists a. reflexivity.
  * inversion H.
Qed.

Definition bind_some_prime_S {A B : Type} (ma : option A) (f : {a : A | ma = Some a} -> option B) (b : B) (eq : ma >>== f = Some b) : {a : A | ma = Some a}.
  destruct ma.
  - apply exist with (x := a). reflexivity.
  - inversion eq.
Defined.

Lemma bind_eta_prime {A B : Type} : forall (ma : option A) (f : {a' : A | ma = Some a'} -> B) (b : B),
    ma >>== (fun a => eta (f a)) = Some b ->
    exists (a : A) (eq: ma = Some a), f (exist (fun a => ma = Some a) a eq) = b.
Proof.
  intros ma f b H.
  destruct ma as [a|]; try solve [inversion H].
  simpl in H. inversion H.
  exists a. exists eq_refl. reflexivity.
Qed.

Lemma monad_law1_prime {A B : Type} : forall (a : A) (f : { a' : A | Some a = Some a'} -> option B),
    eta a >>== f = f (exist (fun a' => Some a = Some a') a eq_refl).
Proof.
  intros a f.
  reflexivity.
Qed.

Lemma monad_law2_prime {A B : Type} : forall (ma : option A),
    (ma >>== fun p => match p with
                  | exist _ a eq => eta a
                  end) = ma.
Proof.
  intros ma. destruct ma; try reflexivity.
Qed.
