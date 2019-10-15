Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Import ListNotations.

Require Import OptionMonad.
Require Import SumMonad.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import AST.
Require Import Names.
Require Import GenericLemmas.
Require Import BodyTypeDefs.
(* Require Import UtilsProgram. *)

Definition error := unit.
Definition dummy {A} : error + A := inl tt.

Fixpoint nth_sum  {A : Type} (n : nat) (ls : list A) : (error + A) :=
  match n, ls with
  | 0 , (x :: xs) => inr x
  | (S n) , (x :: xs) => nth_sum n xs
  | _ , [] => dummy
  end.

Fixpoint nth_option  {A : Type} (n : nat) (ls : list A) : (option A) :=
  match n, ls with
  | 0 , (x :: xs) => Some x
  | (S n) , (x :: xs) => nth_option n xs
  | _ , [] => None
  end.

(**************************************************************************************************)
(** * Typecheck Function                                                                          *)
(**                                                                                               *)
(** Typecheck is not an inductive relation but a computable function.                             *)
(**                                                                                               *)
(** ** Auxilliary functions and correctness proofs                                                *)
(**************************************************************************************************)

Definition sum_fail {A B} (x : A + B) : bool :=
  match x with
  | inl _ => false
  | inr _  => true
  end.

Definition wrap_sum {A} (x : option A) : error + A :=
  match x with
  | Some y => inr y
  | None => dummy
  end.

Definition ctxt := list TypeName.

(**************************************************************************************************)
(** ** The typecheck function                                                                     *)
(**************************************************************************************************)
Fixpoint typecheck (ps : skeleton) (ctx : ctxt) (e : expr) {struct e} : (error + TypeName)  :=
  let typecheck_eq p ctx e t : bool := match (typecheck p ctx e) with
                                       | inr t' => eq_TypeName t t'
                                       | inl _ => false
                                       end in
  let just_typecheck ps ctx e : bool := sum_fail (typecheck ps ctx e) in
  match e with
(**************************************************************************************************)
(** Typechecking Variables.                                                                       *)
(**************************************************************************************************)
  | E_Var v =>
    nth_sum v ctx
(**************************************************************************************************)
(** Typechecking Constructors.                                                                    *)
(**************************************************************************************************)
  | E_Constr sn args =>
    wrap_sum (lookup_ctor_sig ps sn) >>=_sum
    (fun ctor =>
    if
      andb
        (length (snd ctor) =? length args)
        (forallb
        (fun x => match x with
                  | (t1, inl _) => false
                  | (t1, inr t2) => eq_TypeName t1 t2
                  end)
        (List.combine (snd ctor) (List.map (typecheck ps ctx) args)))
    then inr (fst (unscope sn))
    else dummy)
(**************************************************************************************************)
(** Typechecking Destructor Calls.                                                                *)
(**************************************************************************************************)
  | E_DestrCall sn ex args =>
    wrap_sum (lookup_dtor ps sn) >>=_sum
    (fun dtor =>
       if andb
            (length (snd (fst dtor)) =? length args)
            (andb
               (typecheck_eq ps ctx ex (fst (unscope sn)))
               (forallb
                  (fun x => match x with
                            | (t1, inl _) => false
                            | (t1, inr t2) => eq_TypeName t1 t2
                            end)
                  (List.combine (snd (fst dtor)) (List.map (typecheck ps ctx) args))))
       then inr (snd dtor)
       else dummy)
(**************************************************************************************************)
(** Typechecking Function Calls.                                                                  *)
(**************************************************************************************************)
     | E_FunCall n args =>
       wrap_sum (lookup_fun_sig ps n) >>=_sum
       (fun fsig => if
            andb
              (length (snd (fst fsig)) =? length args)
              (forallb
                 (fun x => match x with
                           | (t1, inl _) => false
                           | (t1, inr t2) => eq_TypeName t1 t2
                           end)
                 (List.combine (snd (fst fsig)) (List.map (typecheck ps ctx) args)))
          then inr (snd fsig)
          else dummy)
(**************************************************************************************************)
(** Typechecking Global Generator Function Calls.                                                                  *)
(**************************************************************************************************)
     | E_GenFunCall (global qn) args =>
       wrap_sum (lookup_gfun_sig_g ps qn) >>=_sum
       (fun gfsig =>
          if andb
               (length (snd gfsig) =? length args)
               (forallb
                  (fun x => match x with
                            | (t1, inl _) => false
                            | (t1, inr t2) => eq_TypeName t1 t2
                            end)
                  (List.combine (snd gfsig) (List.map (typecheck ps ctx) args)))
          then inr (fst qn)
          else dummy)
(**************************************************************************************************)
(** Typechecking Local Generator Function Calls.                                                                  *)
(**************************************************************************************************)
     | E_GenFunCall (local qn) args =>
       wrap_sum (lookup_gfun_sig_l ps qn) >>=_sum
       (fun gfsig =>
          if andb
               (length (snd gfsig) =? length args)
               (forallb
                  (fun x => match x with
                            | (t1, inl _ ) => false
                            | (t1, inr t2) => eq_TypeName t1 t2
                            end)
                  (List.combine (snd gfsig) (List.map (typecheck ps ctx) args)))
          then inr (fst qn)
          else dummy)
(**************************************************************************************************)
(** Typechecking Global Destructor Function Calls.                                                                  *)
(**************************************************************************************************)
     | E_ConsFunCall (global qn) ex args =>
       wrap_sum (lookup_cfun_sig_g ps qn) >>=_sum
       (fun cfsig =>
          if andb
               (typecheck_eq ps ctx ex (fst qn))
               (andb
                  (length (snd (fst cfsig)) =? length args)
                  (forallb
                     (fun x => match x with
                               | (t1, inl _) => false
                               | (t1, inr t2) => eq_TypeName t1 t2
                               end
                     )
                     (List.combine (snd (fst cfsig)) (List.map (typecheck ps ctx) args))))
          then inr (snd cfsig)
          else dummy)
(**************************************************************************************************)
(** Typechecking Local Destructor Function Calls.                                                                  *)
(**************************************************************************************************)
     | E_ConsFunCall (local qn) ex args =>
       wrap_sum (lookup_cfun_sig_l ps qn) >>=_sum
       (fun cfsig =>
          if andb
               (typecheck_eq ps ctx ex (fst qn))
               (andb
                  (length (snd (fst cfsig)) =? length args)
                  (forallb
                     (fun x => match x with
                               | (t1, inl _) => false
                               | (t1, inr t2) => eq_TypeName t1 t2
                               end
                     )
                     (List.combine (snd (fst cfsig)) (List.map (typecheck ps ctx) args))))
          then inr (snd cfsig)
          else dummy)
(**************************************************************************************************)
(** Typechecking Pattern Matches.                                                                 *)
(** Assumes that cases are given in the order of the constructors in the program.                 *)
(**************************************************************************************************)
     | E_Match qn ex bs cases rtype =>
       let ex_type : error + TypeName := (typecheck ps ctx ex) in
       let bs_types : list TypeName := (List.map snd bs) in
       let bs_check : bool := forallb (fun x => typecheck_eq ps ctx (fst x) (snd x)) bs in
       let ctors : option (list (ScopedName * list TypeName)) := lookup_ctors ps (fst qn) in
       let fix typecheck_cases ps (ctxs : list ctxt) (cases : list (ScopedName * expr)) (rtype : TypeName)
               (bs_types : list TypeName) (ctors : list (ScopedName * list TypeName)) {struct cases}: bool :=
           match ctxs, cases, ctors with
           | [], [], [] => true
           | (ctx :: ctxs), ((name, body) :: cases'), (ctor :: ctors) =>
             andb
                (andb
                   (eq_ScopedName name (fst ctor))
                   (typecheck_eq ps ctx body rtype))
                (typecheck_cases ps ctxs cases' rtype bs_types ctors)
           | _ , _ , _ => false
           end in
       wrap_sum ctors  >>=_sum (fun ctors =>
                     if andb
                          (andb
                             bs_check
                             (typecheck_eq ps ctx ex (fst qn)))
                          (typecheck_cases ps (map (fun ctor => (snd ctor) ++ bs_types) ctors) cases rtype bs_types ctors)
           then inr rtype
           else dummy)
(**************************************************************************************************)
(** Typechecking CoMatches                                                                        *)
(**************************************************************************************************)
     | E_CoMatch qn bs cocases =>
       let bs_types : list TypeName := List.map snd bs in
       let bs_check : bool := forallb (fun x => typecheck_eq ps ctx (fst x) (snd x)) bs in
       let fix typecheck_cocases p (ctxs : list ctxt) (cocases : list (ScopedName * expr)) (bs_types : list TypeName)
               (dtors : list (ScopedName * list TypeName * TypeName)) {struct cocases} : bool :=
           match ctxs, cocases, dtors with
           | [], [], [] => true
           | (ctx :: ctxs), ((name, body) :: cocases'), (dtor :: dtors') =>
             andb
               (andb
                  (eq_ScopedName name (fst (fst dtor)))
                  (typecheck_eq ps ctx body (snd dtor)))
               (typecheck_cocases ps ctxs cocases' bs_types dtors')
           | _, _, _ => false
           end in
       wrap_sum (lookup_dtors ps (fst qn)) >>=_sum (fun dtors =>
       if
         andb
           bs_check
           (typecheck_cocases ps (map (fun dtor => (snd (fst dtor)) ++ bs_types) dtors) cocases bs_types dtors)
       then inr (fst qn)
       else dummy)
(**************************************************************************************************)
(** Typechecking Let Expressions.                                                                 *)
(**************************************************************************************************)
     | E_Let e1 e2 => (typecheck ps ctx e1) >>=_sum (fun t1 => typecheck ps (t1 :: ctx) e2)
end.

(**************************************************************************************************)
(** * Typing Derivations                                                                          *)
(**                                                                                               *)
(** TypeDeriv is an inductive relation, expressing that in the context of a given program and     *)
(** context of variable assignments, a given expression has a given type.                         *)
(**                                                                                               *)
(** We introduce two notations for Typing Derivations:                                            *)
(** - [prog /  ctx  |-  e :  t]                                                                   *)
(** - [prog // ctx ||- es :: ts]                                                                  *)
(** The first notation expresses that in program prog and context ctx, the expression e has       *)
(** type t. The second notation expresses the same for a list of expressions and a list of types. *)
(**************************************************************************************************)
Reserved Notation " p '/' c '|-' e ':' t" (at level 39, e at level 9, c at level 9, t at level 9).
Reserved Notation " p '//' c '||-' es '::' ts" (at level 40, es at level 10, c at level 10, ts at level 10).
Reserved Notation " p '///' cs '|||-' es ':::' ts" (at level 40, es at level 10, cs at level 10, ts at level 10).

Inductive TypeDeriv : skeleton -> ctxt -> expr -> TypeName -> Prop :=
(**************************************************************************************************)
(** The type of free variables is read from the context.                                          *)
(**************************************************************************************************)
  | T_Var : forall (prog : skeleton) (ctx : ctxt) (v : nat) (t : TypeName),
      Some t = (nth_option v ctx) ->
      prog / ctx |- (E_Var v) : t
(**************************************************************************************************)
(** The type of Constructors.                                                                     *)
(**************************************************************************************************)
  | T_Constr : forall (prog : skeleton) (ctx : ctxt) (args : list expr)
                      (sn : ScopedName)(cargs :list TypeName)(tn : TypeName),
      In (sn, cargs) (skeleton_ctors prog) ->
      prog // ctx ||- args :: cargs ->
      tn = (fst (unscope sn)) ->
      prog / ctx |- (E_Constr sn args) : tn
(**************************************************************************************************)
(** The type of Destructor Calls.                                                                 *)
(**************************************************************************************************)
  | T_DestrCall : forall (prog : skeleton) (ctx : ctxt) (args : list expr) (ex : expr)
                         (sn : ScopedName) (dargs : list TypeName) (rtype : TypeName),
      In ((sn,dargs),rtype) (skeleton_dtors prog) ->
      prog / ctx |- ex : (fst (unscope sn)) ->
      prog // ctx ||- args :: dargs ->
      prog / ctx |- (E_DestrCall sn ex args) : rtype
(**************************************************************************************************)
(** The type of Function Calls .                                                                  *)
(**************************************************************************************************)
  | T_FunCall : forall (prog : skeleton) (ctx : ctxt) (args : list expr)
                       (n : Name)(argts: list TypeName) (rtype : TypeName),
      In ((n,argts),rtype) (skeleton_fun_sigs prog) ->
      prog // ctx ||- args :: argts ->
      prog / ctx |- (E_FunCall n args) : rtype
(**************************************************************************************************)
(** The type of Global Consumer Function Calls.                                                          *)
(**************************************************************************************************)
  | T_GlobalConsFunCall : forall (prog : skeleton) (ctx : ctxt) (args : list expr) (ex : expr)
                            (qn : QName)(argts : list TypeName) (rtype : TypeName),
      In ((qn, argts), rtype) (skeleton_cfun_sigs_g prog) ->
      prog / ctx |- ex : (fst qn) ->
      prog // ctx ||- args :: argts ->
      prog / ctx |- (E_ConsFunCall (global qn) ex args) : rtype
(**************************************************************************************************)
(** The type of Local Consumer Function Calls.                                                          *)
(**************************************************************************************************)
  | T_LocalConsFunCall : forall (prog : skeleton) (ctx : ctxt) (args : list expr) (ex : expr)
                            (qn : QName)(argts : list TypeName) (rtype : TypeName),
      In ((qn, argts), rtype) (skeleton_cfun_sigs_l prog) ->
      prog / ctx |- ex : (fst qn) ->
      prog // ctx ||- args :: argts ->
      prog / ctx |- (E_ConsFunCall (local qn) ex args) : rtype
(**************************************************************************************************)
(** The type of Global Generator Function Calls.                                                         *)
(**************************************************************************************************)
  | T_GlobalGenFunCall : forall (prog : skeleton) (ctx : ctxt) (args : list expr)
                       (qn : QName) (argts : list TypeName),
      In (qn, argts) (skeleton_gfun_sigs_g prog) ->
      prog // ctx ||- args :: argts ->
      prog / ctx |- (E_GenFunCall (global qn) args) : (fst qn)
(**************************************************************************************************)
(** The type of Local Generator Function Calls.                                                         *)
(**************************************************************************************************)
  | T_LocalGenFunCall : forall (prog : skeleton) (ctx : ctxt) (args : list expr)
                       (qn : QName) (argts : list TypeName),
      In (qn, argts) (skeleton_gfun_sigs_l prog) ->
      prog // ctx ||- args :: argts ->
      prog / ctx |- (E_GenFunCall (local qn) args) : (fst qn)
(**************************************************************************************************)
(** The type of Match expressions.                                                                *)
(**************************************************************************************************)
  | T_Match : forall (prog : skeleton) (ctx : ctxt) (qn : QName) (ex : expr)
                     (bindings_exprs : list expr) (bindings_types : list TypeName) (bindings : list (expr * TypeName))
                     (cases : list (ScopedName * expr)) (tn : TypeName)(ctorlist : list (ScopedName * list TypeName)),
      prog / ctx |- ex : (fst qn) ->
      bindings = combine bindings_exprs bindings_types ->
      prog // ctx ||- bindings_exprs :: bindings_types ->
      lookup_ctors prog (fst qn) = Some ctorlist ->
      Forall (fun x => match x with ((sn, _), (sn',_)) => sn = sn' end) (combine cases ctorlist) ->
      prog /// (map (fun ctor => (snd ctor) ++ bindings_types) ctorlist) |||- (map snd cases) ::: (repeat tn (length cases)) ->
      prog / ctx |- (E_Match qn ex  bindings cases tn) : tn
(**************************************************************************************************)
(** The type of CoMatch expressions.                                                              *)
(**************************************************************************************************)
  | T_CoMatch : forall (prog : skeleton) (ctx : ctxt) (qn : QName) (dtorlist : list (ScopedName * (list TypeName) * TypeName))
                       (bindings_exprs : list expr) (bindings_types : list TypeName) (bindings : list (expr * TypeName))
                       (cocases : list (ScopedName * expr)),
      bindings = combine bindings_exprs bindings_types ->
      prog // ctx ||- bindings_exprs :: bindings_types ->
      lookup_dtors prog (fst qn) = Some dtorlist ->
      Forall (fun x => match x with ((sn, _), ((sn',_) , _)) => sn = sn' end) (combine cocases dtorlist) ->
      prog /// (map (fun dtor => (snd (fst dtor)) ++ bindings_types) dtorlist) |||- (map snd cocases) ::: (map snd  dtorlist) ->
      prog / ctx |- (E_CoMatch qn bindings cocases) : (fst qn)
(**************************************************************************************************)
(** The type of Let expressions.                                                                  *)
(**************************************************************************************************)
| T_Let : forall (prog : skeleton) (ctx : ctxt)
                 (e1 e2 : expr) (t1 t2 : TypeName),
    prog / ctx |- e1 : t1 ->
    prog / (t1 :: ctx) |- e2 : t2 ->
    prog / ctx |- ( E_Let e1 e2 ) : t2
with ListTypeDeriv : skeleton -> ctxt -> list expr -> list TypeName -> Prop :=
     | ListTypeDeriv_Nil : forall (p : skeleton) (ctx : ctxt),
         p // ctx ||- [] :: []
     | ListTypeDeriv_Cons : forall (p : skeleton) (ctx : ctxt)
                                   (e : expr) (es  : list expr) (t : TypeName) (ts : list TypeName),
         p / ctx |- e : t ->
         p // ctx ||- es :: ts ->
         p // ctx ||- (e :: es) :: (t :: ts)
with ListTypeDeriv' : skeleton -> list ctxt -> list expr -> list TypeName -> Prop :=
     | ListTypeDeriv'_Nil : forall (p : skeleton),
         p /// [] |||- [] ::: []
     | ListTypeDeriv'_Cons : forall (p : skeleton) (ctx : ctxt) (ctxs : list ctxt) (e : expr) (es : list expr)
                               (t : TypeName) (ts : list TypeName),
         p / ctx |- e : t ->
         p /// ctxs |||- es ::: ts ->
         p /// (ctx :: ctxs) |||- (e :: es) ::: (t :: ts)
where "p '/' c '|-' e ':' t" := (TypeDeriv p c e t)
   and " p '//' c '||-' es '::' ts" := (ListTypeDeriv p c es ts)
   and " p '///' cs '|||-' es ':::' ts" := (ListTypeDeriv' p cs es ts).

Scheme type_deriv_ind := Minimality for TypeDeriv Sort Prop
  with list_type_deriv_ind := Minimality for ListTypeDeriv Sort Prop
  with list_type_deriv'_ind := Minimality for ListTypeDeriv' Sort Prop.


(**************************************************************************************************)
(** Typecheck function bodies                                                                     *)
(**************************************************************************************************)

Fixpoint from_to (l h : nat) : list nat :=
  match l <=? h with
  | true => (fix from_to' l diff {struct diff} : list nat :=
               match diff with
               | 0 => [l]
               | S n => l :: (from_to' (S l) n)
               end) l (h-l)
  | false => []
  end.


Notation " '[-' l '..' h '-]' " := (from_to l h) (at level 0, l at level 9, h at level 9) : list_scope .


(* Lemma from_to_length : forall (n m : nat), *)
(*     m <=? n = true -> *)
(*     List.length [- m .. n -] = S n - m. *)
(* Proof. *)
(*   intros n m Hle. *)
(*   unfold from_to. induction n. *)
(*   - assert (E: m = 0). *)
(*     { apply leb_complete in Hle; omega. } *)
(*     rewrite E. reflexivity. *)
(*   - simpl. destruct m; rewrite Hle. *)
(*     + assert (Le: 0 <= n). omega. apply leb_correct in Le. specialize (IHn Le). rewrite Le in IHn. *)
(*       simpl. f_equal.  *)

(*   assert (H : forall m d, List.length ((fix from_to' (h diff : nat) {struct diff} : list nat := *)
(*                                      match diff with *)
(*                                      | 0 => [h] *)
(*                                      | S n0 => h - diff :: from_to' h n0 *)
(*                                      end) m d) = S d). *)
(*   - intros. induction d; try reflexivity. *)
(*    simpl. f_equal. apply IHd. *)
(*   - unfold from_to. destruct m. *)
(*     + simpl. rewrite <- minus_n_O. apply H. *)
(*     + rewrite Hle. rewrite <- minus_Sn_m. apply H. *)
(*       apply leb_complete. assumption. *)
(* Qed. *)

(* Lemma from_to_length_1_n : forall (n : nat), *)
(*     List.length [- 1 .. n -] = n. *)
(* Proof. *)
(*   intros. induction n; try reflexivity. *)
(*   rewrite from_to_length with (n := S n) (m := 1); reflexivity. *)
(* Qed. *)

Fixpoint index_list {A : Type} (n : nat) (ls : list A) : list (expr * A) :=
  match ls with
  | [] => []
  | head :: tail => (E_Var n, head) :: index_list (S n) tail
  end.

Definition fun_bods_typecheck (sk : skeleton) (bodies : fun_bods) :=
  Forall (fun body => exists n (args : list TypeName) (t : TypeName),
              lookup_fun_sig sk (fst body) = Some (n, args, t) /\
              sk / args |- (snd body) : t) bodies.

Definition cfun_bods_g_typecheck (sk : skeleton) (bodies : cfun_bods) :=
  Forall (fun body =>
            exists qn (args : list TypeName) (t : TypeName),
              lookup_cfun_sig_g sk (fst body) = Some (qn, args, t) /\
              sk / (fst (fst body) :: args) |- (E_Match (fst body)
                                                      (E_Var 0)
                                                      (index_list 1 args)
                                                      (snd body)
                                                      t)
                                             : t)
         bodies.

Definition cfun_bods_l_typecheck (sk : skeleton) (bodies : cfun_bods) :=
  Forall (fun body =>
            exists qn (args : list TypeName) (t : TypeName),
              lookup_cfun_sig_l sk (fst body) = Some (qn, args, t) /\
              sk / (fst (fst body) :: args) |- (E_Match (fst body)
                                                      (E_Var 0)
                                                      (index_list 1 args)
                                                      (snd body)
                                                      t)
                                             : t)
         bodies.

Definition gfun_bods_g_typecheck (sk : skeleton) (bodies : gfun_bods) :=
  Forall (fun body =>
            exists qn (args : list TypeName), lookup_gfun_sig_g sk (fst body) = Some (qn, args) /\
                                         sk / args |- (E_CoMatch (fst body)
                                                                (index_list 0 args)
                                                                (snd body))
                                                     : (fst (fst body)))
         bodies.

Definition gfun_bods_l_typecheck (sk : skeleton) (bodies : gfun_bods) :=
  Forall (fun body =>
            exists qn (args : list TypeName), lookup_gfun_sig_l sk (fst body) = Some (qn, args) /\
                                         sk / args |- (E_CoMatch (fst body)
                                                                (index_list 0 args)
                                                                (snd body))
                                                     : (fst (fst body)))
         bodies.

(**************************************************************************************************)
(** * Correctness of typecheck                                                                    *)
(**                                                                                               *)
(**************************************************************************************************)
Ltac if_then_else_tac :=
  match goal with
  | [ H : (if ?x then inr ?t1 else inl _) = inr ?t2 |- _] =>
    let H_ite := fresh "H_ite" in
    assert (H_ite : x = true /\ t1 = t2);
    try solve[destruct x; split;
              try inversion H;
              try reflexivity];
    let H_ite1 := fresh "H_ite" in
    let H_ite2 := fresh "H_ite" in
    destruct H_ite as [H_ite1 H_ite2]
  end.

Ltac andb_true_tac :=
  match goal with
    [ H : (andb _ _) = true |- _] =>
    repeat rewrite Bool.andb_true_iff in H;
    match goal with
    | [H : (_ /\ _) /\ _ |- _] => let H1 := fresh "H_conj" in
                                  let H2 := fresh "H_conj" in
                                  let H3 := fresh "H_conj" in
                                  destruct H as [[H1 H2] H3]
    | [H : _ /\ (_ /\ _) |- _] => let H1 := fresh "H_conj" in
                                  let H2 := fresh "H_conj" in
                                  let H3 := fresh "H_conj" in
                                  destruct H as [H1 [H2 H3]]
    | [H : _ /\ _  |- _] => let H1 := fresh "H_conj" in
                            let H2 := fresh "H_conj" in
                            destruct H as [H1 H2]
    end
  end; try assumption.

Lemma nth_sum_iff_nth_option: forall {A} (l : list A) (a : A) (n : nat),
    nth_option n l = Some a <-> nth_sum n l = inr a.
Proof.
  intros A l a n.
  generalize dependent l;
    induction n; intros; destruct l; auto; split; intro; auto; simpl in *; try solve [inversion H; auto].
  - apply IHn; auto.
  - apply IHn; auto.
Qed.

Theorem typecheck_correct : forall (prog : skeleton) (ctx : ctxt) (e : expr) (t : TypeName),
    typecheck prog ctx e = inr t ->
    prog / ctx |- e : t.
Proof.
  intros prog ctx e. generalize dependent ctx. induction e using expr_strong_ind; intros ctx tc_name H_tc; simpl in H_tc.
  - (* E_Var *)
    apply T_Var. rewrite <- nth_sum_iff_nth_option in H_tc. rewrite -> H_tc. reflexivity.
  - (* E_Constr *)
    destruct (lookup_ctor_sig prog n) eqn:E ; simpl in H_tc; try (solve [inversion H_tc]).
    unfold dummy in *.
    if_then_else_tac.
    andb_true_tac.
    apply T_Constr with (cargs := snd c).
    +clear H_tc H_conj H_conj0 H_ite1 H.
     unfold lookup_ctor_sig in E.
     induction (skeleton_ctors prog).
     *simpl in E. inversion E.
     *simpl in E. destruct a. simpl in *. destruct (eq_ScopedName n s) eqn:E'.
      name_eq_tac. simpl in E. inversion E. subst.
      simpl. left. reflexivity.
      simpl. right. apply IHc0. apply E.
    +rename ls into args. destruct c as [cname argts]. simpl. (* rename l into argts. *)
     clear H_tc E H_ite1.
     symmetry in H_conj.
     apply beq_nat_eq in H_conj.
     generalize dependent argts.
     induction args.
     *intros argts H_length Hx. induction argts; try inversion H_length.
      apply ListTypeDeriv_Nil.
     *intros argts H_length Hx. induction argts; try inversion H_length.
      apply ListTypeDeriv_Cons.
      **simpl in Hx. andb_true_tac.
        destruct (typecheck prog ctx a) eqn:E; try inversion H_conj. inversion H; subst.
        apply H4 in E. name_eq_tac. assumption.
      **inversion H; subst. apply IHargs.
        ***apply H4.
        ***simpl in H_length. inversion H_length. reflexivity.
        ***simpl in Hx. andb_true_tac.
    +symmetry. assumption.
  - (* E_DestrCall *)
    destruct (lookup_dtor prog n) eqn:E; simpl in H_tc; try (solve [inversion H_tc]).
    unfold dummy in *.
    if_then_else_tac; clear H_tc.
    andb_true_tac.
    symmetry in H_conj. apply beq_nat_eq in H_conj. destruct d as [[dname argts] rtype]. simpl in *; subst.
    destruct (typecheck prog ctx e) eqn:E'; try (solve [inversion H_conj0]).
    name_eq_tac.
    apply T_DestrCall with (dargs := argts).
    +clear H_conj H_conj1 E' H IHe. unfold lookup_dtor in E.
     induction (skeleton_dtors prog).
     *simpl in E. inversion E.
     *destruct a as [[a1 a2] a3]. simpl in *.
      destruct (eq_ScopedName n a1) eqn:E'; simpl in E.
      **name_eq_tac. inversion E; subst. left. reflexivity.
      **right. apply IHd. apply E.
    +apply IHe. assumption.
    +rename ls into args.
     clear E' E IHe.
     generalize dependent argts. induction args.
     *intros argts H_length Hx. induction argts; try inversion H_length.
      apply ListTypeDeriv_Nil.
     *intros argts H_length Hx. induction argts; try inversion H_length; clear H_length.
      inversion H; subst. simpl in Hx. andb_true_tac.
      apply ListTypeDeriv_Cons.
      **apply H3. destruct (typecheck prog ctx a); try inversion H_conj. name_eq_tac.
      **apply IHargs; auto.
  - (* E_FunCall *)
    destruct (lookup_fun_sig prog n) eqn:E; try (solve [inversion H_tc]); simpl in H_tc.
    unfold dummy in *.
    if_then_else_tac. clear H_tc.
    destruct f as [[fname argts] rtype]; simpl in *.
    andb_true_tac; subst.
    symmetry in H_conj; apply beq_nat_eq in H_conj. rename ls into args.
    apply T_FunCall with (argts := argts).
    +clear H H_conj H_conj0. unfold lookup_fun_sig in E.
     induction (skeleton_fun_sigs prog); simpl in *.
     * inversion E.
     * destruct a as [[a0 a1] a2]; simpl in *.
       destruct (eq_Name n a0) eqn:E'; simpl in E.
       ** left. name_eq_tac. inversion E; subst. reflexivity.
       ** right. apply IHf. apply E.
    +clear E. generalize dependent argts.
     induction args.
     * intros argts H_length Hx. induction argts; try inversion H_length.
       apply ListTypeDeriv_Nil.
     * intros argts H_length Hx. induction argts; try inversion H_length.
       simpl in Hx. andb_true_tac.
       inversion H;subst.
       apply ListTypeDeriv_Cons.
       **destruct (typecheck prog ctx a) eqn:E; try inversion H_conj.
         name_eq_tac.
         apply H3. apply E.
       **apply IHargs; auto.
  - (* E_ConsFunCall *)
    destruct sn.
    + destruct (lookup_cfun_sig_l prog q) eqn:E; try (solve [inversion H_tc]); simpl in H_tc.
      unfold dummy in *.
      if_then_else_tac.
      clear H_tc. andb_true_tac.
      symmetry in H_conj0. apply beq_nat_eq in H_conj0. destruct c as [[cname argts] rtype]. simpl in *.
      rename ls into args. destruct (typecheck prog ctx e) eqn:E'; try (solve [inversion H_conj]).
      name_eq_tac.
      apply T_LocalConsFunCall with (argts := argts).
      *clear IHe H E' H_conj0 H_conj1. unfold lookup_cfun_sig_l in E.
       induction (skeleton_cfun_sigs_l prog); simpl in *.
       --inversion E.
       --destruct a as [[a0 a1] a2]; simpl in *. destruct (eq_QName q a0) eqn:E'.
         ++left. name_eq_tac. simpl in E. inversion E; subst. reflexivity.
         ++right. apply IHc. apply E.
      *apply IHe. assumption.
      *clear E E' IHe. generalize dependent argts. induction args.
       --intros argts H_length Hx. induction argts; try (solve [inversion H_length]).
         apply ListTypeDeriv_Nil.
       --intros argts H_length Hx. induction argts; try (solve [inversion H_length]).
         inversion H; subst.
         apply ListTypeDeriv_Cons.
         ++apply H2. simpl in Hx. andb_true_tac.
           destruct (typecheck prog ctx a); try inversion H_conj. name_eq_tac.
         ++apply IHargs; simpl in *; try andb_true_tac; auto.
    + destruct (lookup_cfun_sig_g prog q) eqn:E; try (solve [inversion H_tc]); simpl in H_tc.
      unfold dummy in *.
      if_then_else_tac.
      clear H_tc. andb_true_tac.
      symmetry in H_conj0. apply beq_nat_eq in H_conj0. destruct c as [[cname argts] rtype]. simpl in *.
      rename ls into args. destruct (typecheck prog ctx e) eqn:E'; try (solve [inversion H_conj]).
      name_eq_tac.
      apply T_GlobalConsFunCall with (argts := argts).
      *clear IHe H E' H_conj0 H_conj1. unfold lookup_cfun_sig_g in E.
       induction (skeleton_cfun_sigs_g prog); simpl in *.
       --inversion E.
       --destruct a as [[a0 a1] a2]; simpl in *. destruct (eq_QName q a0) eqn:E'.
         ++left. name_eq_tac. simpl in E. inversion E; subst. reflexivity.
         ++right. apply IHc. apply E.
      *apply IHe. assumption.
      *clear E E' IHe. generalize dependent argts. induction args.
       --intros argts H_length Hx. induction argts; try (solve [inversion H_length]).
         apply ListTypeDeriv_Nil.
       --intros argts H_length Hx. induction argts; try (solve [inversion H_length]).
         inversion H; subst.
         apply ListTypeDeriv_Cons.
         ++apply H2. simpl in Hx. andb_true_tac.
           destruct (typecheck prog ctx a); try inversion H_conj. name_eq_tac.
         ++apply IHargs; simpl in *; try andb_true_tac; auto.
  - (* E_GenFunCall *)
    destruct sn.
    + destruct (lookup_gfun_sig_l prog q) eqn:E; try (solve [inversion H_tc]).
      rename ls into args. destruct g as [gname argts]. (*rename l into argts.*) simpl in *.
      unfold dummy in *.
      if_then_else_tac. clear H_tc.
      andb_true_tac; subst.
      apply T_LocalGenFunCall with (argts := argts).
      *clear H_conj H_conj0 H. unfold lookup_gfun_sig_l in E. induction (skeleton_gfun_sigs_l prog).
       --simpl in E. inversion E.
       --destruct a as [a0 a1]; simpl in *. destruct (eq_QName q a0) eqn:E'; simpl in *.
         ++left. name_eq_tac. inversion E; subst. reflexivity.
         ++right. apply IHg. apply E.
      *clear E. generalize dependent argts. induction args.
       --intros argts H_length Hx. induction argts; try (solve [inversion H_length]).
         apply ListTypeDeriv_Nil.
       --intros argts H_length Hx. induction argts; try (solve [inversion H_length]).
         inversion H; subst. simpl in Hx. andb_true_tac.
         apply ListTypeDeriv_Cons.
         ++apply H2. destruct (typecheck prog ctx a) eqn:E'; try (solve [inversion H_conj]).
           name_eq_tac.
         ++apply IHargs; auto.
    + destruct (lookup_gfun_sig_g prog q) eqn:E; try (solve [inversion H_tc]).
      rename ls into args. destruct g as [gname argts]. (*rename l into argts.*) simpl in *.
      unfold dummy in *.
      if_then_else_tac. clear H_tc.
      andb_true_tac; subst.
      apply T_GlobalGenFunCall with (argts := argts).
      *clear H_conj H_conj0 H. unfold lookup_gfun_sig_g in E. induction (skeleton_gfun_sigs_g prog).
       --simpl in E. inversion E.
       --destruct a as [a0 a1]; simpl in *. destruct (eq_QName q a0) eqn:E'; simpl in *.
         ++left. name_eq_tac. inversion E; subst. reflexivity.
         ++right. apply IHg. apply E.
      *clear E. generalize dependent argts. induction args.
       --intros argts H_length Hx. induction argts; try (solve [inversion H_length]).
         apply ListTypeDeriv_Nil.
       --intros argts H_length Hx. induction argts; try (solve [inversion H_length]).
         inversion H; subst. simpl in Hx. andb_true_tac.
         apply ListTypeDeriv_Cons.
         ++apply H2. destruct (typecheck prog ctx a) eqn:E'; try (solve [inversion H_conj]).
           name_eq_tac.
         ++apply IHargs; auto.
  - (* E_Match *)
    destruct (lookup_ctors prog (fst n)) eqn: E_lookup; try (solve [inversion H_tc]). simpl in H_tc.
    unfold dummy in *.
    if_then_else_tac; clear H_tc; subst. rename es into bindings. rename ls into cases. rename tc_name into rtype.
    rename H into IH_cases. rename H0 into IH_bindings. rename IHe into IH_e. rename c into ctorlist.
    andb_true_tac.
    rename H_conj into H_bindings. rename H_conj0 into H_e. rename H_conj1 into H_cases.
    apply T_Match with (bindings_exprs := (map fst bindings))(bindings_types := (map snd bindings))(ctorlist := ctorlist).
    +apply IH_e. destruct (typecheck prog ctx e); try (solve [inversion H_e]). name_eq_tac.
    +clear H_cases H_e H_bindings IH_cases IH_bindings IH_e. induction bindings; try reflexivity. simpl. f_equal.
     *destruct a; reflexivity.
     *apply IHbindings.
    +clear H_cases H_e E_lookup IH_cases IH_e. induction bindings.
     *simpl. apply ListTypeDeriv_Nil.
     *simpl.
      inversion IH_bindings; subst.
      simpl in H_bindings. andb_true_tac.
      apply ListTypeDeriv_Cons.
      **apply H1. destruct a as [a0 a1]. simpl in *. destruct (typecheck prog ctx a0); try (solve [inversion H_conj]).
        name_eq_tac.
      **apply IHbindings; auto.
    +assumption.
    +clear - H_cases. generalize dependent ctorlist. induction cases; intros ctorlist H_cases; destruct ctorlist; simpl in *;
                                                       try inversion H_cases; try apply Forall_nil.
     destruct a as [a' a''']. destruct c as [cname p]. (*destruct p as [p p'].*)
     apply Forall_cons.
     *simpl in *. andb_true_tac. name_eq_tac.
     *apply IHcases. andb_true_tac.
    +clear E_lookup. generalize dependent ctorlist. induction cases; intros.
     *simpl. induction ctorlist.
      **simpl. apply ListTypeDeriv'_Nil.
      **simpl in H_cases. inversion H_cases.
     *simpl. induction ctorlist.
      **simpl. simpl in H_cases. inversion H_cases.
      **simpl. apply ListTypeDeriv'_Cons.
        ***simpl in H_cases. destruct a as [a'  a''']. andb_true_tac.
           clear IHctorlist IHcases H_e H_bindings IH_bindings H_conj1.
           destruct (typecheck prog (snd a0 ++ map snd bindings) a''') eqn:E; try (solve [inversion H_conj0]).
           simpl. inversion IH_cases;subst. apply H1. name_eq_tac.  assumption.
        ***inversion IH_cases; subst. apply IHcases.
           ****apply H2.
           ****simpl in H_cases. destruct a as [a'  a''']. andb_true_tac.
  - (* E_CoMatch *)
    destruct (lookup_dtors prog (fst n)) eqn: E_lookup; try (solve [inversion H_tc]). simpl in H_tc.
    unfold dummy in *.
    if_then_else_tac. clear H_tc.
    andb_true_tac.
    rename d into dtors. rename es into bindings. rename ls into cocases. rewrite <- H_ite1.
    apply T_CoMatch with (dtorlist := dtors)(bindings_exprs := map fst bindings) (bindings_types := map snd bindings).
    +clear H_conj H_conj0 H H0. induction bindings; try reflexivity. simpl. f_equal.
     *destruct a; reflexivity.
     *apply IHbindings.
   +clear H_conj0 H E_lookup. induction bindings.
     *simpl. apply ListTypeDeriv_Nil.
     *simpl.
      inversion H_conj; subst.
      simpl in H_conj. andb_true_tac.
      apply ListTypeDeriv_Cons.
      **destruct (typecheck prog ctx (fst a)) eqn:E; try (solve [inversion H_conj]). name_eq_tac.
        inversion H0; subst. apply H2. destruct a. apply E.
      **apply IHbindings.
        ***inversion H0;subst. apply H3.
        ***andb_true_tac.
   +assumption.
   +clear - H_conj0. generalize dependent dtors. induction cocases; intros; simpl; destruct dtors; try inversion H_conj0.
    *apply Forall_nil.
    *simpl in *. apply Forall_cons.
     **destruct a as [a'  a''']. destruct d as [[dname p] p']. (*destruct p as [[p' p''] p'''].*) simpl in *. andb_true_tac. name_eq_tac.
     **apply IHcocases. destruct a as [a' a''']. destruct d as [[dname p] p']. (*destruct p as [[p' p''] p'''].*) andb_true_tac.
   +(* Check cocases *)
     subst.
     clear E_lookup. generalize dependent dtors. induction cocases; intros.
     * simpl. destruct dtors.
       **apply ListTypeDeriv'_Nil.
       **inversion H_conj0.
     *simpl. destruct dtors.
      **inversion H_conj0.
      **simpl.
        destruct a as [a' a''']. destruct d as [[dname p''] p''']. (*destruct p as [[p' p''] p'''].*) simpl in *.
        apply ListTypeDeriv'_Cons; simpl in *; andb_true_tac; inversion H; subst.
        ***apply H3. destruct (typecheck prog (p'' ++ map snd bindings) a'''); try inversion H_conj2.
           name_eq_tac.
        ***apply IHcocases; assumption.
  - (* E_Let *)
    destruct (typecheck prog ctx e1) eqn:E1; try (solve [inversion H_tc]); simpl in H_tc.
    apply IHe1 in E1.
    apply IHe2 in H_tc.
    eapply T_Let; auto.
    +apply E1.
    +apply H_tc.
Qed.



Lemma listTypeDeriv_lemma : forall (prog : skeleton)(ctx: ctxt)(args : list expr)(argts : list TypeName),
    prog // ctx ||- args :: argts ->
    length argts =? length args  = true.
Proof.
  intros prog ctx args. induction args; intro argts; induction argts; intro H; try reflexivity; try inversion H; subst.
  simpl. apply IHargs. assumption.
Qed.

Definition P (prog : skeleton) (ctx : ctxt) (e : expr) (tn : TypeName) : Prop := typecheck prog ctx e = inr tn.
Definition P0 (prog : skeleton) (ctx :ctxt) (es : list expr) (tns : list TypeName) : Prop :=
  Forall (fun x => P prog ctx (fst x) (snd x)) (combine es tns).
Definition P1 (prog : skeleton) (ctxs : list ctxt) (es : list expr) (tns : list TypeName) : Prop :=
  Forall (fun x => P prog (fst (fst x)) (snd (fst x)) (snd x)) (combine (combine ctxs es) tns).

Ltac length_tac := match goal with
                     [ H : _ // _ ||- ?es :: ?ts |- _ ] =>
                     let H_length := fresh "H_length" in
                     assert (H_length : length ts =? length es = true);
                     try (solve [apply listTypeDeriv_lemma in H; assumption]);
                     rewrite H_length; simpl
                   end.

Ltac simple_ih_tac := match goal with
                        [ H : P ?p ?c ?e ?t |- _ ] =>
                        unfold P in H; rewrite H; name_refl_tac; simpl
                      end.
Ltac list_ih_tac := match goal with
                      [H1 : P0 ?p ?c ?es ?ts |- _] =>
                      unfold P0 in H1; unfold P in H1; clear - H1;
                      generalize dependent ts; induction es; intros;
                      destruct ts; try auto; simpl in *
                    end.

Ltac ite_option_tac := match goal with
                         [ |- (if ?b then inr ?c else inl _) = inr ?c ] =>
                         let H := fresh "H_ite_true" in
                         assert (H : b = true); repeat (rewrite Bool.andb_true_iff); repeat split
                       end.

Theorem typecheck_complete : forall (prog : skeleton) (ctx : ctxt) (e : expr) (tn : TypeName),
    prog / ctx |- e : tn ->
    typecheck prog ctx e = inr tn.
Proof.
  intros prog ctx e tn H_typechecks.
  apply type_deriv_ind with (P := P) (P0 := P0)(P1 := P1); intros; subst; unfold P; simpl.
  -(* E_Var*)
    rewrite <- nth_sum_iff_nth_option. 
    rewrite H. reflexivity.
  -(* E_Constr *)
    apply In_constructor_lookupsig in H. rewrite H. simpl.
    length_tac.
    list_ih_tac.
    inversion H1; subst. simpl in H2. rewrite H2. name_refl_tac. simpl.
    apply IHargs; auto.
  -(* E_DestrCall *)
    apply In_destructor_lookupsig in H. rewrite H. simpl.
    length_tac.
    simple_ih_tac.
    list_ih_tac.
    inversion H3; subst. simpl in H1. rewrite H1. name_refl_tac. simpl.
    apply IHargs; auto.
  -(* E_FunCall *)
    apply In_fun_sig_lookup_fun_sig in H. rewrite H. simpl.
    length_tac.
    list_ih_tac.
    inversion H1; subst. simpl in H2. rewrite H2. name_refl_tac. simpl.
    apply IHargs; auto.
  -(* E_ConsFunCall global *)
    apply In_cfun_sig_lookup_cfun_sig_g in H. rewrite H. simpl.
    simple_ih_tac.
    length_tac.
    list_ih_tac.
    inversion H3; subst. simpl in H1. rewrite H1. name_refl_tac. simpl.
    apply IHargs; auto.
  -(* E_ConsFunCall local *)
    apply In_cfun_sig_lookup_cfun_sig_l in H. rewrite H. simpl.
    simple_ih_tac.
    length_tac.
    list_ih_tac.
    inversion H3; subst. simpl in H1. rewrite H1. name_refl_tac. simpl.
    apply IHargs; auto.
  -(* E_GenFunCall global *)
    apply In_gfun_sig_lookup_gfun_sig_g in H. rewrite H. simpl.
    length_tac.
    list_ih_tac.
    inversion H1; subst. simpl in H2. rewrite H2. name_refl_tac. simpl.
    apply IHargs; auto.
  -(* E_GenFunCall local *)
    apply In_gfun_sig_lookup_gfun_sig_l in H. rewrite H. simpl.
    length_tac.
    list_ih_tac.
    inversion H1; subst. simpl in H2. rewrite H2. name_refl_tac. simpl.
    apply IHargs; auto.
  -(* E_Match *)
    rewrite H4; simpl.
    unfold dummy.
    ite_option_tac.
    +list_ih_tac.
     inversion H3; subst. simpl in H1. rewrite H1. name_refl_tac. simpl.
     apply IHbindings_exprs. apply H2.
    +simple_ih_tac.
    +clear H4 H3 H. generalize dependent ctorlist. induction cases; intros.
     *induction ctorlist; try reflexivity.
      simpl in *. inversion H6.
     *induction ctorlist.
      **simpl in *. inversion H6.
      **simpl in *. destruct a as [a'  a''']. simpl in *.
        clear IHctorlist.
        inversion H5; subst.
        repeat rewrite Bool.andb_true_iff. repeat split.
        ***destruct a0 as [b b']. simpl in *. subst. name_refl_tac.
        ***simpl in H6. unfold P1 in H7. unfold P in H0.  simpl in H7. inversion H7; subst.
           unfold P in H3. simpl in H3. apply listTypeDeriv_lemma in H2. rewrite map_snd_combine.
           ****destruct a0 as [b b']; subst. simpl in *. inversion H6; subst. unfold P in H8. subst.
               rewrite H8. name_refl_tac.
           ****rewrite Nat.eqb_eq in H2. symmetry. assumption.
        ***apply IHcases; try assumption.
           ****inversion H6; subst. assumption.
           ****clear - H7. unfold P1 in *. inversion H7; subst. assumption.
    +rewrite H_ite_true. reflexivity.
  -(* E_CoMatch *)
    rewrite H2. simpl.
    unfold dummy.
    ite_option_tac.
    +list_ih_tac.
     inversion H1; subst. simpl in H2. rewrite H2. name_refl_tac.  simpl.
     apply IHbindings_exprs; auto.
    +clear H2.
     generalize dependent dtorlist. induction cocases; intros.
     *destruct dtorlist; try reflexivity.
      inversion H4.
     *destruct dtorlist.
      **inversion H4.
      **simpl in *. destruct a as [a' a''']. destruct p as [[p' p''] p''']. simpl in *.
        repeat rewrite Bool.andb_true_iff. repeat split.
        ***inversion H3; subst. name_refl_tac.
        ***unfold P1 in H5. unfold P in H5. inversion H5; subst. apply listTypeDeriv_lemma in H0. clear - H6 H0.
           simpl in *. rewrite map_snd_combine.
           ****rewrite H6. name_refl_tac.
           ****rewrite Nat.eqb_eq in H0. symmetry. assumption.
        ***apply IHcocases; try assumption.
           ****inversion H3; subst; assumption.
           ****inversion H4; subst; assumption.
           **** unfold P1. unfold P1 in H5. inversion H5; subst; assumption.
    +rewrite H_ite_true. reflexivity.
  -(* E_Let *)
    unfold P in H0. rewrite H0. simpl.
    unfold P in H2. rewrite H2. reflexivity.
  -(* ListTypeDerivNil *)
    apply Forall_nil.
  -(* ListTypeDerivCons *)
    apply Forall_cons.
    +simpl. assumption.
    +unfold P0 in H2. assumption.
  -(* ListTypeDeriv'_Nil *)
    unfold P1. apply Forall_nil.
  -(* ListTypeDeriv'_Cons *)
    unfold P1 in *; apply Forall_cons; assumption.
  -assumption.
Qed.
