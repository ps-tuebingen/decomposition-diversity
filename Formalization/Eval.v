Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Require Import AST.
Require Import Names.
Require Import GenericLemmas.
Require Import ProgramDef.
Require Import UtilsSkeleton.
Require Import UtilsProgram.
Require Import BodyTypeDefs.
Require Import OptionMonad.
(**************************************************************************************************)
(** * Values                                                                                      *)
(** ** The value_b function                                                                       *)
(**************************************************************************************************)
Fixpoint value_b (e : expr) : bool :=
  match e with
  | E_Var _  => false
  | E_Constr _ args => forallb value_b args
  | E_DestrCall _ _ _ => false
  | E_FunCall _ _ => false
  | E_GenFunCall _ es => forallb value_b es
  | E_ConsFunCall _ _ _ => false
  | E_Match _ _ _ _ _  => false
  | E_CoMatch _ bs _ => forallb (compose value_b fst) bs
  | E_Let _ _ => false
  end.

(**************************************************************************************************)
(** ** The inductive relation value                                                               *)
(**************************************************************************************************)
Inductive value : expr -> Prop :=
| V_Constr : forall (sn : ScopedName) (ls : list expr),
    Forall value ls ->
    value (E_Constr sn ls)
| V_CoMatch : forall (qn : QName)(b : list (expr * TypeName)) (ls : list (ScopedName * expr)),
    Forall value (List.map fst b) ->
    value (E_CoMatch qn b ls)
| V_GenFunCall : forall (sn : ScopedName) (es : list expr),
    Forall value es ->
    value (E_GenFunCall sn es).

(**************************************************************************************************)
(** ** The reflection proof for value and value_b.                                                *)
(**************************************************************************************************)
Fixpoint value_reflect (e : expr) : reflect (value e) (value_b e).
  induction e; simpl; try (apply ReflectF; intro H; inversion H).
  -destruct (forallb value_b l) eqn:E.
   +apply ReflectT.
    apply V_Constr. induction l.
    *apply Forall_nil.
    *simpl in E. apply andb_true_iff in E. destruct E as [E1 E2].
     apply Forall_cons.
     **specialize (value_reflect a).
       inversion value_reflect;subst. assumption. rewrite E1 in H. inversion H.
     **apply IHl. apply E2.
   +apply ReflectF. intro Hv.
    inversion Hv; subst. induction l.
    *simpl in E. inversion E.
    *simpl in E. rewrite andb_false_iff in E. destruct E.
     **inversion H0; subst. specialize (value_reflect a). rewrite H in value_reflect.
       inversion value_reflect. contradiction.
     **apply IHl; auto. inversion H0; subst. apply V_Constr. assumption. inversion H0. assumption.
  -destruct (forallb value_b l) eqn:E.
   +apply ReflectT.
    apply V_GenFunCall. induction l.
    *apply Forall_nil.
    *simpl in E. apply andb_true_iff in E. destruct E as [E1 E2].
     apply Forall_cons.
     **specialize (value_reflect a).
       inversion value_reflect;subst. assumption. rewrite E1 in H. inversion H.
     **apply IHl. apply E2.
   +apply ReflectF. intro Hv.
    inversion Hv; subst. induction l.
    *simpl in E. inversion E.
    *simpl in E. rewrite andb_false_iff in E. destruct E.
     **inversion H0; subst. specialize (value_reflect a). rewrite H in value_reflect.
       inversion value_reflect. contradiction.
     **apply IHl; auto. inversion H0; subst. apply V_GenFunCall. assumption. inversion H0. assumption.
  -destruct (forallb (compose value_b fst) l) eqn:E.
   +apply ReflectT.
    apply V_CoMatch. induction l; try (apply Forall_nil).
    simpl in E. apply andb_true_iff in E. destruct E as [E1 E2].
    apply Forall_cons.
    *specialize (value_reflect (fst a)).
     inversion value_reflect; subst. assumption. destruct a. unfold compose in E1. rewrite <- H in E1. inversion E1.
    *apply IHl. assumption.
   +apply ReflectF. intro Hv. inversion Hv;subst. induction l.
    *simpl in E. inversion E.
    *simpl in E. apply andb_false_iff in E. destruct E.
     **inversion H0; subst. specialize (value_reflect (fst a)). destruct a. unfold compose in H. rewrite H in value_reflect.
       inversion value_reflect. contradiction.
     **apply IHl; auto. inversion H0; subst. apply V_CoMatch; assumption. inversion H0; assumption.
Defined.

Lemma Forall_value_forall : forall (ls : list expr),
    forallb value_b ls = true <->
    Forall value ls.
Proof.
  intro ls.
  unfold iff. split.
  -intro H. induction ls.
   +apply Forall_nil.
   +simpl in H. rewrite Bool.andb_true_iff in H. destruct H as [H1 H2].
    apply Forall_cons.
    *rewrite <- (Bool.reflect_iff (value a) (value_b a) (value_reflect a)) in H1. assumption.
    *apply IHls. apply H2.
  -intro H. induction ls; try reflexivity.
   simpl. inversion H. rewrite (Bool.reflect_iff (value a) (value_b a) (value_reflect a)) in H2.
   rewrite H2. simpl.
   apply IHls; try assumption.
Qed.

Ltac value_tac :=
  match goal with
  | [ H : value ?e  |- (value_b ?e = true) ] =>
    rewrite (Bool.reflect_iff (value e) (value_b e) (value_reflect e)) in H; assumption
  | [ H : value_b ?e = true  |- (value ?e) ] =>
    rewrite <- (Bool.reflect_iff (value e) (value_b e) (value_reflect e)) in H; assumption
  | [ H : Forall value ?ls |- forallb value_b ?ls = true ] =>
    apply Forall_value_forall in H; assumption
  | [ H : forallb value_b ?ls = true |- Forall value ?ls ] =>
    apply Forall_value_forall in H; assumption
  | [ H : value_b ?e = false |- _ ] =>
    rewrite -> (Bool.reflect_iff (value e) (value_b e) (value_reflect e)) in H
  end.

Lemma value_iff_valueb : forall (e : expr),
    value e <-> value_b e = true.
Proof.
  intros.
  pose proof (value_reflect e) as HReflect.
  unfold iff. split.
  -inversion HReflect; try reflexivity; try contradiction.
  -intros. inversion HReflect; try reflexivity; try contradiction; try assumption.
   rewrite <- H0 in H. discriminate H.
Qed.

Lemma forall_valueb_extract_single : forall (e : expr) (left right : list expr),
    forallb value_b (left ++ [e] ++ right) = true ->
    value e.
Proof.
  intros e left right EallVal. induction left.
  -simpl in EallVal. apply andb_true_iff in EallVal. apply proj1 in EallVal.
   pose proof (value_reflect e). inversion H; try assumption.
   rewrite <- H0 in EallVal. discriminate EallVal.
  -apply IHleft. simpl in EallVal. apply andb_true_iff in EallVal. apply proj2 in EallVal. assumption.
Qed.


(**************************************************************************************************)
(** * Single Step Evaluation                                                                      *)
(** ** The one-step eval function                                                                 *)
(**************************************************************************************************)
Fixpoint one_step_eval (p : program) (e : expr) {struct e} : option expr :=
  match e with
(**************************************************************************************************)
(** Evaluating Variables. (This case shouldn't occur when evaluating closed terms.)               *)
(**************************************************************************************************)
  | E_Var n => None
(**************************************************************************************************)
(** Evaluating Constructors.                                                                      *)
(**************************************************************************************************)
  | E_Constr n args =>
    (fix apply_to_first_nonvalue (es : list expr) {struct es} : option (list expr) :=
       match es with
       | [] => None
       | (arg :: args') =>
         if (value_b arg)
         then apply_to_first_nonvalue args' >>= fun args'' =>
              eta (arg :: args'')
         else one_step_eval p arg >>= fun arg' =>
              eta (arg' :: args')
       end) args >>= fun args' => eta (E_Constr n args')
(**************************************************************************************************)
(** Evaluating Destructors.                                                                       *)
(**************************************************************************************************)
  | E_DestrCall sn ex args =>
    if (value_b ex)
    then if (forallb value_b) args
         then match ex with
              | E_Var _ => None
              | E_Constr _ _ => None
              | E_DestrCall _ _ _ => None
              | E_FunCall _ _ => None
              | E_GenFunCall comatchfunname cargs =>
                lookup_gfun_bods_scoped p comatchfunname >>= (fun cocases =>
                lookup_cocase (snd cocases) sn  >>= (fun body =>
                Some (multi_subst (args ++ cargs) (snd  body))))
              | E_ConsFunCall _ _ _ => None
              | E_Match  _ _ _ _ _ => None
              | E_CoMatch comatchname bindings cocases =>
                lookup_cocase cocases sn
                >>= fun body =>
                     Some (multi_subst (args ++ (List.map fst bindings)) (snd body))
              | E_Let _ _ => None
              end
         else (fix apply_to_first_nonvalue (es : list expr) {struct es} : option (list expr) :=
                              match es with
                              | [] => None
                              | (arg :: args') =>
                                if (value_b arg)
                                then apply_to_first_nonvalue args' >>= fun args'' =>
                                     Some (arg :: args'')
                                else one_step_eval p arg >>= fun arg' =>
                                     Some (arg' :: args')
                              end) args
              >>= fun args' => Some (E_DestrCall sn ex args')
    else one_step_eval p ex >>= fun ex' =>
         Some (E_DestrCall sn ex' args)
(**************************************************************************************************)
(** Evaluating function calls.                                                                    *)
(**************************************************************************************************)
  | E_FunCall n args =>
    if (forallb value_b args)
    then
      lookup_fun_bods p n >>= fun body =>
      Some (multi_subst args body)
    else (fix apply_to_first_nonvalue (es : list expr) {struct es} : option (list expr) :=
                         match es with
                         | [] => None
                         | (arg :: args') =>
                           if (value_b arg)
                           then apply_to_first_nonvalue args' >>=fun args'' =>
                                Some (arg :: args'')
                           else one_step_eval p arg >>= fun arg' =>
                                Some (arg' :: args')
                         end) args
         >>= fun args' => Some (E_FunCall n args')
(**************************************************************************************************)
(** Evaluating constructor function calls.                                                        *)
(**************************************************************************************************)
  | E_GenFunCall qn args =>
    if (forallb value_b args)
    then None
    else (fix apply_to_first_nonvalue (ars : list expr) {struct ars} : option (list expr) :=
            match ars with
            | [] => None
            | arg :: args' =>
              if (value_b arg)
              then apply_to_first_nonvalue args' >>= fun args'' =>
                   Some (arg :: args'')
              else one_step_eval p arg >>= fun arg' =>
                   Some (arg' :: args')
            end) args
          >>= fun args' => Some (E_GenFunCall qn args')
(**************************************************************************************************)
(** Evaluating desctructor function calls.                                                        *)
(**************************************************************************************************)
  | E_ConsFunCall sn ex args =>
    if (value_b ex)
    then if (forallb value_b args)
         then match ex with
              | E_Var _ => None
              | E_Constr name cargs =>
                lookup_cfun_bods_scoped p sn >>=
                                        fun body => lookup_case (snd body) name
                >>= fun c => Some (multi_subst (cargs ++ args) (snd c))
              | E_DestrCall _ _ _ => None
              | E_FunCall _ _ => None
              | E_GenFunCall _ _ => None
              | E_ConsFunCall _ _ _ => None
              | E_Match _ _ _ _ _ => None
              | E_CoMatch _ _ _ => None
              | E_Let _ _ => None
              end
         else (fix apply_to_first_nonvalue (ars : list expr) {struct ars} : option (list expr) :=
                 match ars with
                 | [] => None
                 | (arg :: args') =>
                   if (value_b arg)
                   then apply_to_first_nonvalue args' >>= fun args'' =>
                        Some (arg :: args'')
                   else one_step_eval p arg >>= fun arg' =>
                        Some (arg' :: args')
                 end) args
              >>= fun args' => Some (E_ConsFunCall sn ex args')
    else one_step_eval p ex >>= fun ex' =>
         Some (E_ConsFunCall sn ex' args)
(**************************************************************************************************)
(** Evaluating pattern matches.                                                                   *)
(**************************************************************************************************)
  | E_Match matchname ex bindings cases type =>
    if (value_b ex)
    then let args := map fst bindings
         in if (forallb value_b args)
            then match ex with
                 | E_Var _ => None
                 | E_Constr name cargs =>
                   lookup_case cases name
                    >>= fun c => Some (multi_subst (cargs ++ args) (snd c))
                 | E_DestrCall _ _ _ => None
                 | E_FunCall _ _ => None
                 | E_GenFunCall _ _ => None
                 | E_ConsFunCall _ _ _ => None
                 | E_Match _ _ _ _ _ => None
                 | E_CoMatch _ _ _ => None
                 | E_Let _ _ => None
                 end
            else (fix apply_to_first_nonvalue (bs : list (expr * TypeName)) {struct bs} : option (list (expr * TypeName)) :=
                    match bs with
                    | [] => None
                    | ((arg, argt) :: args') =>
                      if (value_b arg)
                      then apply_to_first_nonvalue args' >>= fun args'' =>
                           Some ((arg, argt) :: args'')
                      else one_step_eval p arg >>= fun arg' =>
                           Some ((arg', argt) :: args')
                    end) bindings
                 >>= fun bindings' =>
                   Some (E_Match matchname ex bindings' cases type)
    else one_step_eval p ex >>= fun ex' =>
         Some (E_Match matchname ex' bindings cases type)
(**************************************************************************************************)
(** Evaluating copattern matches.                                                                 *)
(**************************************************************************************************)
  | E_CoMatch comatchname bindings cocases =>
    if (forallb value_b (map fst bindings))
    then None
    else (fix apply_to_first_nonvalue (bs : list (expr * TypeName)) {struct bs} : option (list (expr * TypeName)) :=
            match bs with
            | [] => None
            | ((arg, argt) :: args') =>
              if (value_b arg)
              then apply_to_first_nonvalue args' >>= fun args'' =>
                   Some ((arg, argt) :: args'')
              else one_step_eval p arg  >>= fun arg' =>
                   Some ((arg', argt) :: args')
            end) bindings
         >>= fun bindings' =>
           Some (E_CoMatch comatchname bindings' cocases)
(**************************************************************************************************)
(** Evaluating Let Expressions.                                                                   *)
(**************************************************************************************************)
  | E_Let e1 e2 =>
    if (value_b e1)
    then Some (substitute e1 e2)
    else one_step_eval p e1 >>= fun e1' =>
         Some (E_Let e1' e2)
  end.

(**************************************************************************************************)
(** ** Single step eval relation.                                                                 *)
(**                                                                                               *)
(** The semantic of our language is given in the smallstep style. We first present all the        *)
(** congruence rules and then the reduction rules.                                                *)
(**                                                                                               *)
(** We use the following notation for a one-step reduction:                                       *)
(**                                                                                               *)
(** - [[ prog |- e ==> e' ]]                                                                      *)
(**                                                                                               *)
(** i.e. in the programm prog, e reduces to e' in one step.                                       *)
(**************************************************************************************************)
Reserved Notation "'[' prog '|-' e '==>' e' ']'" (at level 0, e at level 10, e' at level 10).

Inductive step : program -> expr -> expr -> Prop :=
(**************************************************************************************************)
(** Arguments of a constructor evaluate from left to right.                                       *)
(**************************************************************************************************)
  | STEP_ConstrCongr : forall (prog : program)
                              (left right args args': list expr) (e e': expr) (sn : ScopedName),
      Forall value left ->
      [prog |- e ==> e'] ->
      args  = left ++ (e  :: nil) ++ right ->
      args' = left ++ (e' :: nil) ++ right ->
      [prog |- (E_Constr sn args) ==> (E_Constr sn args')]
(**************************************************************************************************)
(** The expression to which a destructor is applied is evaluated before the arguments of the      *)
(** destructor are evaluated.                                                                     *)
(**************************************************************************************************)
  | STEP_DestrCongr1 : forall (prog : program)
                              (args : list expr) (e e': expr) (sn : ScopedName),
      [prog |- e ==> e'] ->
      [prog |- (E_DestrCall sn  e args) ==> (E_DestrCall sn e' args)]
(**************************************************************************************************)
(** Arguments of a destructor evaluate from left to right. This presupposes that the expression   *)
(** to which the destructor is applied is already evaluated to a value.                           *)
(**************************************************************************************************)
  | STEP_DestrCongr2 : forall (prog : program)
                              (left right args args': list expr) (ex e e': expr) (sn : ScopedName),
      Forall value left ->
      value ex ->
      [prog |- e ==> e'] ->
      args  = left ++ (e  :: nil) ++ right ->
      args' = left ++ (e' :: nil) ++ right ->
      [prog |- (E_DestrCall sn  ex args) ==> (E_DestrCall sn ex args')]
(**************************************************************************************************)
(** The arguments of a function are evaluated from left to right.                                 *)
(**************************************************************************************************)
  | STEP_FunCallCongr : forall (prog : program)
                               (left right args args': list expr) (e e' : expr) (n : Name),
      Forall value left ->
      [prog |- e ==> e'] ->
      args  = left ++ (e  :: nil) ++ right ->
      args' = left ++ (e' :: nil) ++ right ->
      [prog |- (E_FunCall n args) ==> (E_FunCall n args')]
(**************************************************************************************************)
(** The arguments of a generator function are evaluated from left to right.                       *)
(**************************************************************************************************)
  | STEP_GenFunCallCongr : forall (prog : program)
                                      (left right args args': list expr) (e e' : expr) (sn : ScopedName),
      Forall value left ->
      [prog |- e ==> e'] ->
      args = left ++ (e :: nil) ++ right ->
      args' = left ++ (e' :: nil) ++ right ->
      [prog |- (E_GenFunCall sn args) ==> (E_GenFunCall sn args')]
(**************************************************************************************************)
(** The expression to which a consumer function  is applied is evaluated before the arguments     *)
(** of the consumer function are evaluated.                                                       *)
(**************************************************************************************************)
  | STEP_ConsFunCallCongr1 : forall (prog : program)
                              (args : list expr) (e e': expr) (sn : ScopedName),
      [prog |- e ==> e'] ->
      [prog |- (E_ConsFunCall sn  e args) ==> (E_ConsFunCall sn e' args)]
(**************************************************************************************************)
(** Arguments of a consumer function evaluate from left to right. This presupposes that the       *)
(** expression to which the consumer function is applied is already evaluated to a value.         *)
(**************************************************************************************************)
  | STEP_ConsFunCallCongr2 : forall (prog : program)
                              (left right args args': list expr) (ex e e': expr) (sn : ScopedName),
      Forall value left ->
      value ex ->
      [prog |- e ==> e'] ->
      args  = left ++ (e  :: nil) ++ right ->
      args' = left ++ (e' :: nil) ++ right ->
      [prog |- (E_ConsFunCall sn  ex args) ==> (E_ConsFunCall sn ex args')]
(**************************************************************************************************)
(** The expression on which we pattern match is evaluated before the expressions in the bindings- *)
(** list are evaluated.                                                                           *)
(**************************************************************************************************)
  | STEP_MatchCongr1 : forall (prog : program) (qn : QName) (e e' : expr) (rtype : TypeName)
                              (bs : list (expr * TypeName)) (cases : list (ScopedName * expr)),
      [prog |- e ==> e'] ->
      [prog |- (E_Match qn e bs cases rtype) ==> (E_Match qn e' bs cases rtype)]
(*************************************************************************************************)
(** The expressions in the bindings list are evaluated from left to right.                       *)
(*************************************************************************************************)
  | STEP_MatchCongr2 : forall (prog : program) (rtype : TypeName)
                              (e e' ex : expr) (left right : list expr) (bs bs': list (expr * TypeName))
                              (cases : list (ScopedName * expr)) (qn : QName),
      Forall value left ->
      value ex ->
      [prog |- e ==> e'] ->
      (List.map fst bs)  = left ++ (e  :: nil) ++ right ->
      (List.map fst bs') = left ++ (e' :: nil) ++ right ->
      (List.map snd bs)  = (List.map snd bs') ->
      [prog |- (E_Match qn ex bs cases rtype) ==> (E_Match qn ex bs' cases rtype)]
(**************************************************************************************************)
(** The expression in the bindings list are evaluated from left to right.                         *)
(**************************************************************************************************)
  | STEP_CoMatchCongr : forall (prog : program) (qn : QName)
                               (e e' : expr) (left right : list expr)
                               (bs bs' : list (expr * TypeName))
                               (cocases : list (ScopedName * expr)),
      Forall value left ->
      [prog |- e ==> e'] ->
      (List.map fst bs)  = left ++ (e  :: nil) ++ right ->
      (List.map fst bs') = left ++ (e' :: nil) ++ right ->
      (List.map snd bs)  = (List.map snd bs') ->
      [prog |- (E_CoMatch qn bs cocases) ==> (E_CoMatch qn bs' cocases)]
(**************************************************************************************************)
(** The expression of a let binding can be evaluated.                                             *)
(**************************************************************************************************)
  | STEP_LetCongr : forall (prog : program)
                           (e e' ex : expr),
      [prog |- e ==> e'] ->
      [prog |- (E_Let e ex) ==> (E_Let e' ex)]
(**************************************************************************************************)
(** Once the expression of a let binding is evaluated to a value, it can be substituted.          *)
(**************************************************************************************************)
  | STEP_Let : forall (prog : program)
                      (v e : expr),
      value v ->
      [prog |- (E_Let v e) ==> substitute v e]
(**************************************************************************************************)
(** Once all the arguments of a function call are evaluated to values, they can be substituted    *)
(** into the body of the function. We have to look up the body in the program.                    *)
(**************************************************************************************************)
  | STEP_FunCall : forall (prog : program) (n : Name) (args : list expr)(fbody : expr),
      Forall value args ->
      is_first (n, fbody) (program_fun_bods prog) (fun x y => eq_Name (fst x) (fst y)) ->
      [prog |- (E_FunCall n args) ==> multi_subst args fbody]
(**************************************************************************************************)
(** Once all the arguments of a constructor are evaluated to values, and this constructor is      *)
(** pattern matched on, then the arguments of the constructor, together with the values of the    *)
(** binding list, can be substituted in the correct case of the pattern match.                    *)
(**************************************************************************************************)
  | STEP_Match : forall (prog : program)(matchname: QName) (sn : ScopedName)
                   (args : list expr) (bs : list (expr * TypeName))
                   (cases : list (ScopedName * expr)) (body : expr)(tn : TypeName),
      Forall value args ->
      Forall (fun binding => value (fst binding)) bs ->
      is_first (sn, body) cases (fun x y => eq_ScopedName (fst x) (fst y)) ->
      [ prog |- (E_Match matchname (E_Constr sn args) bs cases tn) ==> multi_subst (args ++ (List.map fst bs)) body]
(**************************************************************************************************)
(** ConsFun *)
(**************************************************************************************************)
  | STEP_ConsFunCallG : forall (prog : program)(sn : ScopedName)(qn : QName) (args cargs: list expr)(e : expr)
                               (cfun_body : QName * list (ScopedName * expr)),
      is_first cfun_body (program_cfun_bods_g prog) (fun x y => eq_QName (fst x) (fst y)) ->
      qn = (fst cfun_body) ->
      is_first (sn,e) (snd cfun_body) (fun x y => eq_ScopedName (fst x) (fst y)) ->
      Forall value args ->
      Forall value cargs ->
      [prog |- (E_ConsFunCall (global qn) (E_Constr sn cargs)  args) ==> multi_subst (cargs ++ args) e]
  | STEP_ConsFunCallL : forall (prog : program)(sn : ScopedName)(qn : QName) (args cargs: list expr)(e : expr)
                               (cfun_body : QName * list (ScopedName * expr)),
      is_first cfun_body (program_cfun_bods_l prog) (fun x y => eq_QName (fst x) (fst y)) ->
      qn = (fst cfun_body) ->
      is_first (sn,e) (snd cfun_body) (fun x y => eq_ScopedName (fst x) (fst y)) ->
      Forall value args ->
      Forall value cargs ->
      [prog |- (E_ConsFunCall (local qn) (E_Constr sn cargs)  args) ==> multi_subst (cargs ++ args) e]
(**************************************************************************************************)
(** Once all the arguments of a destructor are evaluated to values, and this destructor is        *)
(** applied to a copattern match, then the arguments of the destructor, together with the values  *)
(** of the binding list, can be substituted in the correct case of the copattern match.           *)
(**************************************************************************************************)
  | STEP_DestrComatch : forall (prog : program)(args : list expr) (bs : list (expr * TypeName))
                             (cocases : list (ScopedName * expr))
                             (body : expr) (matchname : QName)(sn : ScopedName),
      Forall value args ->
      Forall (fun binding => value (fst binding)) bs ->
      is_first (sn, body) cocases (fun x y => eq_ScopedName (fst x) (fst y)) ->
      [prog |- (E_DestrCall sn (E_CoMatch matchname bs cocases) args) ==> multi_subst (args ++ (List.map fst bs)) body]
(**************************************************************************************************)
(** Once all the arguments of a destructor are evaluated to values, and this destructor is        *)
(** applied to a copattern match, then the arguments of the destructor, together with the values  *)
(** of the binding list, can be substituted in the correct case of the copattern match.           *)
(**************************************************************************************************)
  | STEP_DestrGenFunCallG : forall (prog : program)(fargs dargs : list expr)
                             (cocases : list (ScopedName * expr))
                             (body : expr)(sn : ScopedName)(qn : QName),
      Forall value fargs ->
      Forall value dargs ->
      is_first (sn,body) cocases (fun x y => eq_ScopedName (fst x) (fst y)) ->
      is_first (qn, cocases) (program_gfun_bods_g prog) (fun x y => eq_QName (fst x) (fst y)) ->
      [prog |- (E_DestrCall sn (E_GenFunCall (global qn) fargs) dargs) ==> multi_subst (dargs ++ fargs) body]
  | STEP_DestrGenFunCallL : forall (prog : program)(fargs dargs : list expr)
                              (cocases : list (ScopedName * expr))
                              (body : expr)(sn : ScopedName)(qn : QName),
      Forall value fargs ->
      Forall value dargs ->
      is_first (sn,body) cocases (fun x y => eq_ScopedName (fst x) (fst y)) ->
      is_first (qn, cocases) (program_gfun_bods_l prog) (fun x y => eq_QName (fst x) (fst y)) ->
      [prog |- (E_DestrCall sn (E_GenFunCall (local qn) fargs) dargs) ==> multi_subst (dargs ++ fargs) body]
where "'[' prog '|-' e '==>' e' ']'" := (step prog e e') : eval_scope.

(**************************************************************************************************)
(** * Theorems about Values.                                                                      *)
(**************************************************************************************************)

Open Scope eval_scope.

Lemma forall_value_app : forall (ls ls' : list expr) (e : expr),
    Forall value (ls ++ (e :: []) ++ ls') ->
    value e.
Proof.
  intros ls ls' e H.
  induction ls.
  -simpl in H. inversion H; subst. assumption.
  -apply IHls. simpl in H. inversion H. assumption.
Qed.


Lemma Forall_value_forall_false : forall (ls :list expr),
    forallb value_b ls = false ->
    ~ Forall value ls.
Proof.
  intros ls H Habs.
  induction ls; simpl in H.
  -inversion H.
  -rewrite Bool.andb_false_iff in H. destruct H.
   *inversion Habs; subst.
    rewrite (Bool.reflect_iff (value a) (value_b a) (value_reflect a)) in H2.
    rewrite H2 in H. inversion H.
   *inversion Habs; subst.
    apply IHls; assumption.
Qed.

Lemma value_normal_form : forall (prog : program) (e : expr),
    value e ->
    ~ (exists e',
          [prog |- e ==> e']).
Proof.
  intros prog e H_value Habs. destruct Habs.
  inversion H_value; subst.
  -induction H; subst; try (solve [inversion H_value]).
   +apply IHstep. inversion H_value; subst. apply forall_value_app with (ls := left) (ls' := right); assumption.
   +apply IHstep. inversion H_value; subst. apply forall_value_app with (ls := left) (ls' := right); assumption.
   +apply IHstep. inversion H_value; subst. rewrite H2 in H6. apply forall_value_app with (ls := left) (ls' := right) in H6.
    assumption.
  -induction H; subst; try (solve [inversion H_value]).
   +apply IHstep. inversion H_value; subst. apply forall_value_app with (ls := left) (ls' := right); assumption.
   +apply IHstep. inversion H_value; subst. apply forall_value_app with (ls := left) (ls' := right); assumption.
   +apply IHstep. inversion H_value; subst. apply forall_value_app with (ls := left) (ls' := right). rewrite H2 in H6. assumption.
  -induction H; subst; try (solve [inversion H_value]).
   +apply IHstep. inversion H_value; subst. apply forall_value_app with (ls := left) (ls' := right); assumption.
   +apply IHstep. inversion H_value; subst. apply forall_value_app with (ls := left) (ls' := right); assumption.
   +apply IHstep. inversion H_value; subst. apply forall_value_app with (ls := left) (ls' := right). rewrite H2 in H6. assumption.
Qed.

Ltac values_non_eval_tac prog e Hvalue :=
  apply value_normal_form with (prog := prog) in Hvalue; case Hvalue; exists e; assumption.

(**************************************************************************************************)
(** * Theorems and Lemmas about Evaluation.                                                       *)
(**************************************************************************************************)

(**************************************************************************************************)
(** * Monotonicity Lemmas.                                                                        *)
(**************************************************************************************************)
Ltac step_congr_tac :=
  try (solve [reflexivity]);
  try (solve [assumption]);
  try (solve [apply Forall_nil]);
  try (solve [auto]).

Lemma constr_eval_monotone : forall (prog : program) (e : expr) (n : ScopedName) (args args' : list expr),
    value e ->
    [prog |- (E_Constr n args) ==> (E_Constr n args')] <->
    [prog |- (E_Constr n (e :: args)) ==> (E_Constr n (e :: args'))].
Proof.
  intros prog e n args args' H_value.
  unfold iff. split.
  -intro H.
   inversion H; subst.
   apply STEP_ConstrCongr with (left := e :: left) (right := right)(e := e0) (e' := e'); step_congr_tac.
  -intro H.
   inversion H; subst.
   induction left.
   +simpl in *. inversion H6. inversion H7. subst.
    values_non_eval_tac prog e' H_value.
   +inversion H6; inversion H7; inversion H3.
    apply STEP_ConstrCongr with (left := left) (right := right) (e := e0) (e' := e'); try assumption; try reflexivity.
Qed.

Lemma funcall_eval_monotone : forall (prog : program) (e : expr) (n : Name) (args args' : list expr),
    value e ->
    ~ Forall value args ->
    [prog |- (E_FunCall n args) ==> (E_FunCall n args')] <->
    [prog |- (E_FunCall n (e :: args)) ==> (E_FunCall n (e :: args'))].
Proof.
  intros prog e n args args' H_value H_nonvalue.
  unfold iff. split.
  -intro H.
   inversion H; subst.
   apply STEP_FunCallCongr with (left := e :: left) (right := right)(e := e0) (e' := e'); step_congr_tac.
   apply H_nonvalue in H4. contradiction.
  -intro H. inversion H; subst.
   +induction left.
    *simpl in *. inversion H6. rewrite H1 in *.
     values_non_eval_tac prog e' H_value.
    *inversion H6; inversion H7; inversion H3.
     apply STEP_FunCallCongr with (left := left) (right := right) (e := e0) (e' := e'); step_congr_tac.
   +inversion H4. contradiction.
Qed.

Lemma destrCall_eval_monotone : forall (prog : program) (ex e : expr) (sn : ScopedName)(args args' : list expr),
    value ex ->
    value e ->
    ~ Forall value args ->
    [prog |- (E_DestrCall sn ex args) ==> (E_DestrCall sn ex args')] <->
    [prog |- (E_DestrCall sn ex (e :: args)) ==> (E_DestrCall sn ex (e :: args'))].
Proof.
  intros prog ex e sn args args' H_value_ex H_value_e H_not_all_values.
  unfold iff. split.
  - intro H.
    inversion H;subst.
    + apply value_normal_form with (prog := prog) in H_value_ex.
      assert (H_exists : exists e', [prog |- ex ==> e']).
      * exists ex. assumption.
      * apply H_value_ex in H_exists. contradiction.
    + apply STEP_DestrCongr2 with (left := e :: left) (right := right) (e := e0) (e' := e'); step_congr_tac.
    + apply H_not_all_values in H5. contradiction.
    + exfalso. apply H_not_all_values; assumption.
    + exfalso. apply H_not_all_values; assumption.
  - intro H.
    inversion H; subst.
    + values_non_eval_tac prog ex H_value_ex.
    + induction left.
      * simpl in *. inversion H8. inversion H9. subst.
        values_non_eval_tac prog e' H_value_e.
      * inversion H8; inversion H9; inversion H4.
        apply STEP_DestrCongr2 with (left := left) (right := right) (e := e0) (e' := e'); try assumption; try reflexivity.
    + inversion H5; subst. contradiction.
    + inversion H6; subst. contradiction.
    + inversion H6; subst. contradiction.
Qed.

Lemma comatch_eval_monotone : forall (prog : program) (e : expr * TypeName) (qn : QName) (bs bs' : list (expr * TypeName))
  (cocases : list (ScopedName * expr)),
    value (fst e) ->
    [prog |- (E_CoMatch qn bs cocases) ==> (E_CoMatch qn bs' cocases)] <->
    [prog |- (E_CoMatch qn (e :: bs) cocases) ==> (E_CoMatch qn (e :: bs') cocases)].
Proof.
  intros prog e qn bs bs' cocases H_value.
  unfold iff. split.
  -intro H. inversion H; subst.
   apply map_app3 in H7. apply map_app3 in H8.
   destruct H7 as [left' [e0' [right' G]]].
   apply STEP_CoMatchCongr with (e := e0) (e' := e')(left := (fst e) :: left)(right := right); step_congr_tac.
   +destruct G as [G1 [G2 [G3 G4]]]. rewrite <- G4. simpl. repeat (rewrite map_app).
    rewrite G1. rewrite G2. rewrite G3. reflexivity.
   +simpl. f_equal.
    destruct H8 as [left'' [e'' [right'' F]]]. destruct F as [F1 [F2 [F3 F4]]].
    rewrite <- F4. repeat (rewrite map_app). rewrite F1. rewrite F2. rewrite F3. simpl. reflexivity.
   +simpl. f_equal. assumption.
  -intro H. inversion H; subst.
   destruct e as [e_ex e_t]. simpl in *.
   induction left.
   *simpl in *. inversion H7; subst. values_non_eval_tac prog e' H_value.
   *inversion H7; inversion H8; inversion H9; inversion H4; subst.
   apply STEP_CoMatchCongr with (e := e0) (e' := e')(left := left)(right := right); step_congr_tac.
Qed.

Lemma match_eval_monotone : forall (prog : program) (ex e : expr) (qn : QName)(tn rtype : TypeName)
                              (cases : list (ScopedName * expr)) (bs bs' : list (expr * TypeName)),
    value e ->
    value ex ->
    ~ (Forall (compose value fst) bs) ->
    [prog |- (E_Match qn ex bs cases rtype) ==> (E_Match qn ex bs' cases rtype)] <->
    [prog |- (E_Match qn ex ((e,tn):: bs) cases rtype) ==> (E_Match qn ex ((e,tn) :: bs') cases rtype)].
Proof.
  intros prog ex e qn tn rtype cases bs bs' H_value_e H_value_ex H_not_all_value.
  unfold iff. split; intro H.
  -inversion H; subst.
   +apply value_normal_form with (prog := prog) in H_value_ex.
    assert (H_exists : exists e', [prog |- ex ==> e']).
    *exists ex; assumption.
    *apply H_value_ex in H_exists. contradiction.
   +apply map_app3 in H10. apply map_app3 in H11.
    destruct H10 as [left' [e0' [right' G]]].
    destruct H11 as [left'' [e'' [right'' F]]].
    apply STEP_MatchCongr2 with (e := e0) (e' := e')(left :=(e :: left))(right := right); step_congr_tac.
    *simpl. f_equal. destruct G as [G1 [G2 [G3 G4]]]. rewrite <- G4. repeat (rewrite map_app).
     rewrite G1. rewrite G2. rewrite G3. reflexivity.
    *simpl. f_equal. destruct F as [F1 [F2 [F3 F4]]]. rewrite <- F4. repeat (rewrite map_app).
     rewrite F1. rewrite F2. rewrite F3. reflexivity.
    *simpl. f_equal. assumption.
   +exfalso. clear - H_not_all_value H8. induction bs.
    *apply H_not_all_value. apply Forall_nil.
    *inversion H8; subst. apply IHbs.
     --intro H. apply H_not_all_value. apply Forall_cons.
       ++unfold compose. assumption.
       ++assumption.
     --assumption.
  -inversion H; subst.
   +values_non_eval_tac prog ex H_value_ex.
   +induction left.
    *simpl in *. inversion H10; subst. values_non_eval_tac prog e' H_value_e.
    *inversion H10; inversion H11; inversion H12; inversion H7; subst.
     apply STEP_MatchCongr2 with (e := e0) (e' := e')(left := left)(right := right); step_congr_tac.
   +inversion H8. contradiction.
Qed.

Lemma matchFunCall_eval_monotone : forall (prog : program)(ex e : expr)(sn : ScopedName) (args args' : list expr),
    value ex ->
    value e ->
    ~ Forall value args ->
    [prog |- (E_ConsFunCall sn ex args) ==> (E_ConsFunCall sn ex args')] <->
    [prog |- (E_ConsFunCall sn ex (e :: args)) ==> (E_ConsFunCall sn ex (e :: args'))].
Proof.
  intros prog ex e qn args args' H_value_ex H_value_e H_not_value.
  unfold iff. split.
  -intro H.
  inversion H; subst.
  +apply value_normal_form with (prog := prog) in H_value_ex.
   assert (H_exists : exists e', [prog |- ex ==> e']).
   *exists ex. assumption.
   *apply H_value_ex in H_exists. contradiction.
  +apply STEP_ConsFunCallCongr2 with (left := e :: left) (right := right) (e := e0) (e' := e'); step_congr_tac.
  +contradiction.
  + contradiction.
  -intro H. inversion H; subst.
   +values_non_eval_tac prog ex H_value_ex.
   +induction left.
    *inversion H8. subst. values_non_eval_tac prog e' H_value_e.
    *inversion H8; inversion H9; inversion H4.
     apply STEP_ConsFunCallCongr2 with (left := left) (right := right) (e := e0) (e' := e'); step_congr_tac.
   +inversion H8. contradiction.
   +inversion H8. contradiction.
Qed.

Lemma comatchFunCall_eval_monotone : forall (prog : program) (e : expr) (sn : ScopedName) (args args' : list expr),
    value e ->
    [prog |- (E_GenFunCall sn args) ==> (E_GenFunCall sn args')] <->
    [prog |- (E_GenFunCall sn (e :: args)) ==> (E_GenFunCall sn (e :: args'))].
Proof.
  intros prog e qn args args' H_value.
  unfold iff. split.
  -intro H. inversion H; subst.
   apply STEP_GenFunCallCongr with (left := e :: left) (right := right) (e := e0) (e' := e'); step_congr_tac.
  -intro H. inversion H; subst.
   induction left.
   +inversion H6. subst. values_non_eval_tac prog e' H_value.
   +inversion H6; inversion H7; inversion H3.
    apply STEP_GenFunCallCongr with (left := left) (right := right) (e := e0) (e' := e'); step_congr_tac.
Qed.

(**************************************************************************************************)
(** *Theorem: Eval function is complete w.r.t. inductive relation                                 *)
(**************************************************************************************************)
Theorem eval_complete : forall (prog : program) (e1 e2 : expr),
    [ prog |- e1 ==> e2 ] ->
    one_step_eval prog e1 = Some e2.
Proof.
  intros prog e1 e2 Heval.
  generalize dependent e2. induction e1 using expr_strong_ind; intros;
      inversion Heval as [ p left right argsStep args' e e' snStep HValLeft HStepInd Eargs Eargs' (* STEP_ConstrCongr *)
                         | p argsStep e e' snStep HStepInd (* STEP_DestrCongr1 *)
                         | p left right argsStep args' exStep e e' snStep HValLeft HValEx HStepInd Eargs Eargs' (* STEP_DestrCongr2 *)
                         | p left right argsStep args' e e' name HValLeft HStepInd Eargs Eargs' (* STEP_FunCallCongr *)
                         | p left right argsStep args' e e' qnStep HValLeft HStepInd Eargs Eargs' (* STEP_GenFunCallCongr *)
                         | p argsStep e e' qnStep HStepInd (* STEP_ConsFunCallCongr1 *)
                         | p left right argsStep args' exStep e e' qnStep HValLeft HValEx HStepInd Eargs Eargs' (* STEP_ConsFunCallCongr2 *)
                         | p qnStep e e' rtype  bsStep cases HStepInd (* STEP_MatchCongr1 *)
                         | p rtype e e' exStep left right bsStep bs' cases qnStep
                                HValLeft HValEx HStepInd Ebs Ebs' Ebs_snd (* STEP_MatchCongr2 *)
                         | p qnStep e e' left right bsStep bs' cocases
                                HValLeft HStepInd Ebs Ebs' Ebs_snd (* STEP_CoMatchCongr *)
                         | p e e' exStep HStepInd (* STEP_LetCongr *)
                         | p var e HValV (* STEP_Let *)
                         | p name argsStep fbody HValArgs HisFirst En_body (* STEP_FunCall *)
                         | p matchname snStep argsStep bsStep cases body tnStep HValArgs HValBs HinStep (* STEP_Match *)
                         | p qnStep snStep argsStep cargsStep e mfbody HisFirstMbds Eqn_mbody HisFirstMbd HValArgs HValCargs (* STEP_ConsFunCallG *)
                         | p qnStep snStep argsStep cargsStep e mfbody HisFirstMbds Eqn_mbody HisFirstMbd HValArgs HValCargs (* STEP_ConsFunCallL *)
                         | p argsStep bsStep cocases body matchname snStep HValArgs HValBs HinStep (* STEP_DestrComatch *)
                         | p fargs dargsStep cocases body snStep qnStep HValFargs HValDargs HisFirstCcs HisFirstCbds (* STEP_DestrGenFunCallG *)
                         | p fargs dargsStep cocases body snStep qnStep HValFargs HValDargs HisFirstCcs HisFirstCbds (* STEP_DestrGenFunCallL *)
                         ].
  (* e2 = E_Constr, STEP_ConstrCongr *)
  -subst. induction left.
   +simpl. inversion H; subst.
    destruct (value_b e) eqn:Ee.
    *pose proof (value_reflect e) as HvalE.
     inversion HvalE; try solve [rewrite <- H0 in Ee; inversion Ee].
     apply value_normal_form with (prog := prog) in H1.
     exfalso. apply H1. exists e'. assumption.
    *unfold bind. specialize H2 with e'. apply H2 in HStepInd. rewrite HStepInd. reflexivity.
   +simpl. destruct (value_b a) eqn:Ea.
    assert (HCInj : Injective (E_Constr n)). apply constr_injective.
    *combine_etas. simpl in IHleft. apply eta_cong_inj_rev with (f := E_Constr n); try assumption.
     apply IHleft.
     --inversion H. assumption.
     --clear - Heval Ea.
       apply constr_eval_monotone with (e := a); try assumption.
       pose proof (value_reflect a) as HValA.
       inversion HValA; try assumption.
       rewrite <- H in Ea; discriminate Ea.
     --inversion HValLeft. assumption.
    *inversion HValLeft; subst.
     pose proof (value_reflect a) as HValA.
     inversion HValA.
     --rewrite <- H0 in Ea. discriminate Ea.
     --exfalso. apply H1. assumption.
  (* e2 = E_DestrCall, STEP_DestrCongr1 *)
  -subst. simpl.
   destruct (value_b e1) eqn:Ee1.
   +pose proof (value_reflect e1).
    inversion H0.
    *values_non_eval_tac prog e' H2.
    *rewrite <- H1 in Ee1. discriminate Ee1.
   +apply IHe1 in HStepInd. rewrite HStepInd. reflexivity.
  (* e2 = E_DestrCall, STEP_DestrCongr2 *)
  -subst. simpl.
   assert (HValExb : value_b e1 = true). apply value_iff_valueb in HValEx; assumption.
   rewrite HValExb.
   destruct (forallb value_b (left ++ e :: right)) eqn:EallVal.
   +apply forall_valueb_extract_single with (left := left) (e := e) (right := right) in EallVal.
    values_non_eval_tac prog e' EallVal.
   +induction left.
    *simpl. inversion H; subst.
     destruct (value_b e) eqn:Ee.
     --pose proof (value_reflect e) as HValE.
       inversion HValE; try solve [rewrite <- H0 in Ee; inversion Ee].
       apply value_normal_form with (prog := prog) in H1.
       exfalso. apply H1. exists e'. assumption.
     --simpl. unfold bind. specialize H2 with e'. apply H2 in HStepInd. rewrite HStepInd. reflexivity.
    *simpl. destruct (value_b a) eqn:Ea.
     assert (HCInj : Injective (E_DestrCall n e1)). apply destr_injective.
     --combine_etas. simpl in IHleft. apply eta_cong_inj_rev with (f := E_DestrCall n e1); try assumption.
       simpl in EallVal. rewrite Ea in EallVal. simpl in EallVal.
       apply IHleft; try assumption.
       ++inversion H. assumption.
       ++clear - Heval HValEx Ea EallVal.
         apply destrCall_eval_monotone with (e := a); try assumption.
         **pose proof (value_reflect a) as HValA.
           inversion HValA; try assumption.
           rewrite <- H in Ea; discriminate Ea.
         **intro.
           apply Forall_value_forall_false in EallVal. contradiction.
       ++inversion HValLeft. assumption.
     --inversion HValLeft; subst.
       pose proof (value_reflect a) as HValA.
       inversion HValA.
       ++rewrite <- H0 in Ea. discriminate Ea.
       ++exfalso. apply H1. assumption.
  (* e = (E_DestrCall ... (E_CoMatch ...) ...), STEP_DestrComatch *)
  -subst. simpl. destruct (forallb (compose value_b fst) bsStep) eqn:EallValBs.
   +assert (EallValLs : forallb value_b ls = true). value_tac; assumption.
    rewrite EallValLs.
    apply lookup_cocase_is_first in HinStep. rewrite HinStep. reflexivity.
   +apply Forall_compose_map in HValBs.
    rewrite forallb_compose_map in EallValBs.
    apply Forall_value_forall_false in EallValBs. contradiction.
  (* e = (E_DestrCall ... (E_GenFunCall (global ..) ...) ...), STEP_DestrGenFunCall *)
  -subst. simpl.
   assert (EallValFargs : forallb value_b fargs = true). value_tac; assumption.
   rewrite EallValFargs.
   assert (EallValLs : forallb value_b ls = true). value_tac; assumption.
   rewrite EallValLs.
   assert (H_lookup: lookup_gfun_bods_scoped prog (global qnStep) = Some (qnStep, cocases)).
   { apply lookup_gfun_bods_scoped_is_first. exists qnStep. split; eauto. }
   apply lookup_cocase_is_first in HisFirstCcs. rewrite H_lookup; clear H_lookup. simpl.
   rewrite HisFirstCcs; simpl.
   reflexivity.
  (* e = (E_DestrCall ... (E_GenFunCall (local ..)  ...) ...), STEP_DestrGenFunCall *)
  -subst. simpl.
   assert (EallValFargs : forallb value_b fargs = true). value_tac; assumption.
   rewrite EallValFargs.
   assert (EallValLs : forallb value_b ls = true). value_tac; assumption.
   rewrite EallValLs.
   assert (H_lookup : lookup_gfun_bods_scoped prog (local qnStep) = Some (qnStep, cocases)).
   { apply lookup_gfun_bods_scoped_is_first. exists qnStep. split; auto. }
   apply lookup_cocase_is_first in HisFirstCcs. rewrite H_lookup; simpl.
   rewrite HisFirstCcs; simpl.
   reflexivity.
   (* e = E_FunCall, STEP_FunCallCongr *)
  -subst. simpl.
   destruct (forallb value_b (left ++ e :: right)) eqn:EallVal.
   +apply forall_valueb_extract_single in EallVal.
    values_non_eval_tac prog e' EallVal.
   +apply forallb_app_false in EallVal; try solve [apply Forall_value_forall in HValLeft; assumption].
    induction left.
    *simpl. destruct (value_b e) eqn:Ee.
     --assert (HValE : value e). value_tac. values_non_eval_tac prog e' HValE.
     --combine_etas.
       inversion H. apply H2 in HStepInd. rewrite HStepInd. simpl.
       reflexivity.
    *simpl. assert (HValA : value_b a = true). inversion HValLeft; value_tac.
     rewrite HValA. combine_etas. apply eta_cong_inj_rev; try solve [apply funcall_injective].
     apply IHleft; try solve [inversion H; inversion HValLeft; assumption].
     apply funcall_eval_monotone with (e := a); try assumption.
       --inversion HValLeft; assumption.
       --intro Hneg. apply Forall_value_forall_false in EallVal. inversion HValLeft; subst.
         clear - EallVal H2 Hneg.
         induction left; try contradiction.
         apply IHleft. inversion Hneg. assumption.
   (* e = E_FunCall, STEP_FunCall *)
  -subst. simpl.
   assert (EallValLs : forallb value_b ls = true). value_tac; assumption.
   rewrite EallValLs.
   apply lookup_fun_bods_is_first in HisFirst. rewrite HisFirst.
   reflexivity.
   (* e = E_ConsFunCall, STEP_ConsFunCallCongr1 *)
  -subst. simpl. destruct (value_b e1) eqn:Ee.
   +assert (HValE : value e1). value_tac; assumption.
    values_non_eval_tac prog e' HValE.
   +apply IHe1 in HStepInd. rewrite HStepInd. reflexivity.
  (* e = E_ConsFunCall, STEP_ConsFunCallCongr2 *)
  -subst. simpl.
   assert (HValE1 : value_b e1 = true). value_tac; assumption.
   rewrite HValE1.
   destruct (forallb value_b (left ++ e :: right)) eqn:EallVal.
   +apply forall_valueb_extract_single in EallVal.
    values_non_eval_tac prog e' EallVal.
   +apply forallb_app_false in EallVal; try solve [apply Forall_value_forall in HValLeft; assumption].
    induction left.
    *simpl. destruct (value_b e) eqn:Ee.
     --assert (HValE : value e). value_tac. values_non_eval_tac prog e' HValE.
     --combine_etas.
       inversion H. apply H2 in HStepInd. rewrite HStepInd. simpl.
       reflexivity.
    *simpl. assert (HValA : value_b a = true). inversion HValLeft; value_tac.
     rewrite HValA. combine_etas. apply eta_cong_inj_rev; try solve [apply matchfuncall_injective].
     apply IHleft; try solve [inversion H; inversion HValLeft; assumption].
     apply matchFunCall_eval_monotone with (e := a); try assumption.
     --inversion HValLeft; assumption.
       --intro Hneg. apply Forall_value_forall_false in EallVal. inversion HValLeft; subst.
         clear - EallVal H2 Hneg.
         induction left; try contradiction.
         apply IHleft. inversion Hneg. assumption.
   (* e = (E_ConsFunCall (global ..) ... (E_Constr ...) ...) , STEP_ConsFunCall *)
  -subst. simpl.
   assert (EallValCargs : forallb value_b cargsStep = true). value_tac; assumption.
   rewrite EallValCargs.
   assert (EallValLs : forallb value_b ls = true). value_tac; assumption.
   rewrite EallValLs.
   destruct mfbody as [qn ctor]. simpl in *.
   apply (fun x => conj x (eq_refl qn)) in HisFirstMbds.
   assert (H_lookup: lookup_cfun_bods_scoped prog (global qn) = Some (qn, ctor)).
   { apply lookup_cfun_bods_scoped_is_first. exists qn. inversion HisFirstMbds. split; auto. }
   rewrite H_lookup; simpl.
   apply lookup_case_is_first in HisFirstMbd. rewrite HisFirstMbd; simpl.
   reflexivity.
  (* e = (E_ConsFunCall (local ..) ... (E_Constr ...) ...) , STEP_ConsFunCall *)
  -subst. simpl.
   assert (EallValCargs : forallb value_b cargsStep = true). value_tac; assumption.
   rewrite EallValCargs.
   assert (EallValLs : forallb value_b ls = true). value_tac; assumption.
   rewrite EallValLs.
   destruct mfbody as [qn ctor]. simpl in *.
   assert (H_lookup: lookup_cfun_bods_scoped prog (local qn) = Some (qn, ctor)).
   { apply lookup_cfun_bods_scoped_is_first. exists qn. split; auto. }
   rewrite H_lookup; simpl.
   apply lookup_case_is_first in HisFirstMbd. rewrite HisFirstMbd; simpl.
   reflexivity.
   (* e = E_GenFunCall, STEP_GenFunCallCongr *)
  -subst. simpl.
   destruct (forallb value_b (left ++ e :: right)) eqn:EallVal.
   +apply forall_valueb_extract_single in EallVal.
    values_non_eval_tac prog e' EallVal.
   +apply forallb_app_false in EallVal; try solve [apply Forall_value_forall in HValLeft; assumption].
    induction left.
        *simpl. destruct (value_b e) eqn:Ee.
     --assert (HValE : value e). value_tac. values_non_eval_tac prog e' HValE.
     --combine_etas.
       inversion H. apply H2 in HStepInd. rewrite HStepInd. simpl.
       reflexivity.
    *simpl. assert (HValA : value_b a = true). inversion HValLeft; value_tac.
     rewrite HValA. combine_etas. apply eta_cong_inj_rev; try solve [apply comatchfuncall_injective].
     apply IHleft; try solve [inversion H; inversion HValLeft; assumption].
     apply comatchFunCall_eval_monotone with (e := a); try assumption.
     inversion HValLeft; assumption.
   (* e = E_Match, STEP_MatchCongr1 *)
  -subst. simpl. destruct (value_b e1) eqn:Ee1.
   +apply value_iff_valueb in Ee1. values_non_eval_tac prog e' Ee1.
   +apply IHe1 in HStepInd. rewrite HStepInd.
    simpl. reflexivity.
   (* e = E_Match, STEP_MatchCongr2 *)
  -subst. simpl.
   assert (HValExb : value_b e1 = true). apply value_iff_valueb in HValEx; assumption.
   rewrite HValExb.
   destruct (forallb value_b (map fst es)) eqn:EallVal.
   +rewrite Ebs in EallVal.
    apply forall_valueb_extract_single in EallVal.
    values_non_eval_tac prog e' EallVal.
   +rewrite Ebs in EallVal.
    generalize dependent es.
    generalize dependent bs'.
    induction left.
    *intros. destruct es eqn:Ees; try solve [inversion Ebs]. destruct bs' eqn:Ebs''; try solve [inversion Ebs'].
     destruct p as [e_p t_p]; destruct p0 as [e_p' t_p']. simpl in *.
     inversion Ebs; subst. inversion Ebs'; subst.
     destruct (value_b e) eqn:Ee.
     --apply value_iff_valueb in Ee. values_non_eval_tac prog e' Ee.
     --clear EallVal HValLeft Ebs Ebs'. combine_etas.
       inversion H0; subst. apply H4 in HStepInd. rewrite HStepInd. simpl.
       inversion Ebs_snd. subst.
       assert (El_l0 : l = l0).
       ++clear - H3 H6. symmetry in H3.
         generalize dependent l0. induction l; intros.
         **destruct l0; try reflexivity. inversion H3.
         **induction l0; try solve [inversion H3].
           f_equal.
           ---destruct a; destruct a0. simpl in *. inversion H3; inversion H6.
              f_equal; try assumption.
           ---inversion H3; inversion H6. apply IHl; try assumption.
       ++rewrite El_l0. reflexivity.
    *intros. destruct es eqn:Ees; try solve [inversion Ebs]. destruct bs' eqn:Ebs''; try solve [inversion Ebs'].
     destruct p as [e_p t_p]; destruct p0 as [e_p' t_p']. simpl in *.
     inversion Ebs; subst. inversion Ebs'; subst.
     inversion_clear HValLeft. apply value_iff_valueb in H1. rewrite H1 in *. simpl in *.
     combine_etas. inversion Ebs_snd; subst.
     apply eta_cong_inj_rev with (f := fun x => E_Match n e1 x ls tn) (g := fun x => (a, t_p') :: x).
     apply match_injective.
     apply IHleft; try assumption.
     --inversion H0. assumption.
     --apply match_eval_monotone with (e := a) (tn := t_p'); try assumption.
       ++simpl. apply value_iff_valueb. assumption.
       ++clear - H3 EallVal. intro H.
         apply Forall_value_forall_false in EallVal. rewrite <- H3 in EallVal.
         apply Forall_compose_map in H.
         contradiction.
   (* e = (E_Match ... (E_Const ...) ...), STEP_Match *)
  -subst. simpl. destruct (forallb value_b argsStep) eqn:EallVal; try solve [apply Forall_value_forall_false in EallVal; contradiction].
   destruct (forallb value_b (map fst es)) eqn:EallValEs; try solve [apply Forall_value_forall_false in EallValEs; apply Forall_compose_map in HValBs; contradiction].
   apply lookup_case_is_first in HinStep. rewrite HinStep. reflexivity.
   (* e = E_CoMatch, STEP_CoMatchCongr *)
  -subst. simpl.
   destruct (forallb value_b (map fst es)) eqn:EallVal.
   +rewrite Ebs in EallVal.
    apply forall_valueb_extract_single in EallVal.
    values_non_eval_tac prog e' EallVal.
   +rewrite Ebs in EallVal.
    generalize dependent es.
    generalize dependent bs'.
    induction left.
    *intros. destruct es eqn:Ees; try solve [inversion Ebs]. destruct bs' eqn:Ebs''; try solve [inversion Ebs'].
     destruct p as [e_p t_p]; destruct p0 as [e_p' t_p']. simpl in *.
     inversion Ebs; subst. inversion Ebs'; subst.
     destruct (value_b e) eqn:Ee.
     --apply value_iff_valueb in Ee. values_non_eval_tac prog e' Ee.
     --clear EallVal HValLeft Ebs Ebs'. combine_etas.
       inversion H0; subst. apply H4 in HStepInd. rewrite HStepInd. simpl.
       inversion Ebs_snd. subst.
       assert (El_l0 : l = l0).
       ++clear - H3 H6. symmetry in H3.
         generalize dependent l0. induction l; intros.
         **destruct l0; try reflexivity. inversion H3.
         **induction l0; try solve [inversion H3].
           f_equal.
           ---destruct a; destruct a0. simpl in *. inversion H3; inversion H6.
              f_equal; try assumption.
           ---inversion H3; inversion H6. apply IHl; try assumption.
       ++rewrite El_l0. reflexivity.
    *intros. destruct es eqn:Ees; try solve [inversion Ebs]. destruct bs' eqn:Ebs''; try solve [inversion Ebs'].
     destruct p as [e_p t_p]; destruct p0 as [e_p' t_p']. simpl in *.
     inversion Ebs; subst. inversion Ebs'; subst.
     inversion_clear HValLeft. apply value_iff_valueb in H1. rewrite H1 in *. simpl in *.
     combine_etas. inversion Ebs_snd; subst.
     apply eta_cong_inj_rev with (f := fun x => E_CoMatch n x ls) (g := fun x => (a, t_p') :: x).
     apply comatch_injective.
     apply IHleft; try assumption.
     --inversion H0. assumption.
     --apply comatch_eval_monotone with (e := (a, t_p')); try assumption.
       simpl. apply value_iff_valueb. assumption.
   (* e = E_Let, STEP_LetCongr *)
  -simpl. destruct (value_b e1_1) eqn:EValE1_1.
   +apply value_iff_valueb in EValE1_1.
    values_non_eval_tac prog e' EValE1_1.
   +apply IHe1_1 in HStepInd. rewrite HStepInd.
    reflexivity.
   (* e = E_Let, STEP_Let *)
  -simpl. assert (HValVb : value_b e1_1 = true). apply value_iff_valueb in HValV. assumption.
   rewrite HValVb. reflexivity.
Qed.

(**************************************************************************************************)
(** *Theorem: Eval function is correct w.r.t. inductive relation                                  *)
(**************************************************************************************************)
Theorem eval_correct : forall (prog : program) (e e' : expr),
    one_step_eval prog e = Some e' ->
    [ prog |- e ==> e' ].
Proof.
  intros prog e.
  induction e using expr_strong_ind; intros e' H_eval; simpl in H_eval.
  -(* E_Var *)
    inversion H_eval.
  -(* E_Constr *)
    option_bind_tac.
    destruct H_bind. rename ls into args. rename x into args'.
    rewrite H0 in H_eval. simpl in H_eval.
    unfold eta in H_eval. inversion H_eval; subst. clear H_eval.
    generalize dependent args'.
    induction args; intros args' H0.
    *inversion H0.
    *destruct (value_b a) eqn:E.
     **option_bind_tac. destruct H_bind as [args'' Hargs''].
       rewrite Hargs'' in H0. simpl in H0. unfold eta in H0. inversion H0.
       clear H2 H0. inversion H; subst. clear H2.
       specialize (IHargs H3 args'' Hargs''). clear H3.
       apply constr_eval_monotone.
       value_tac.
       assumption.
     **option_bind_tac. destruct H_bind.
       apply STEP_ConstrCongr with (left := []) (right := args) (e := a) (e' := x); step_congr_tac.
       ***inversion H; subst. apply H4. apply H1.
       ***simpl. rewrite H1 in H0. simpl in H0. unfold eta in H0. inversion H0. reflexivity.
  -(* E_DestrCall *)
    destruct (value_b e) eqn:H_value_e.
    +(* e is value *)
      destruct (forallb value_b ls) eqn:H_values_ls.
      *  (* All ls are values *)
        destruct e; try (solve [inversion H_eval]).
        -- (* Destructor called on GenFuncall *)
          option_bind_tac. destruct H_bind. rewrite H0 in H_eval. simpl in H_eval.
          option_bind_tac. destruct H_bind. rewrite H1 in H_eval. simpl in H_eval.
          inversion H_eval; subst.
          destruct s as [qn | qn].
          ++ apply STEP_DestrGenFunCallL with (cocases := (snd x)).
             ** simpl in H_value_e. apply Forall_value_forall in H_value_e. assumption.
             ** apply Forall_value_forall in H_values_ls. assumption.
             ** apply lookup_cocase_is_first. rewrite H1. destruct x0 as [x_sn x_body].
                simpl. repeat f_equal.
                apply lookup_cocase_In in H1. destruct H1 as [Hin Heq]. simpl in Heq. symmetry. assumption.
             ** apply lookup_gfun_bods_x_is_first. assumption.
          ++ apply STEP_DestrGenFunCallG with (cocases := (snd x)).
             ** simpl in H_value_e. apply Forall_value_forall in H_value_e. assumption.
             ** apply Forall_value_forall in H_values_ls. assumption.
             ** apply lookup_cocase_is_first. rewrite H1. destruct x0 as [x_sn x_body].
                simpl. repeat f_equal.
                apply lookup_cocase_In in H1. destruct H1 as [Hin Heq]. simpl in Heq. symmetry. assumption.
             ** apply lookup_gfun_bods_x_is_first. assumption.
        -- (* Destructor called on Comatch *)
          option_bind_tac. destruct H_bind. rewrite H0 in H_eval. simpl in H_eval.
          inversion H_eval; subst.
          apply STEP_DestrComatch.
          ++ apply Forall_value_forall in H_values_ls. assumption.
          ++ simpl in H_value_e. clear H_values_ls H IHe H_eval H0 l0 ls x prog n q.
             induction l; try apply Forall_nil.
             simpl in H_value_e. rewrite Bool.andb_true_iff in H_value_e. destruct H_value_e. destruct a.
             unfold compose in H. simpl in H.
             apply Forall_cons.
             ****value_tac.
             ****apply IHl. assumption.
          ++ apply lookup_cocase_is_first. rewrite H0. destruct x as [x_sn x_body]. simpl.
             apply lookup_cocase_In in H0. destruct H0 as [Hin Heq]. simpl in Heq. symmetry in Heq.
             repeat f_equal; try assumption.
      * (* At least one element of ls is not a value *)
        option_bind_tac. destruct H_bind. rewrite H0 in H_eval. simpl in H_eval. inversion H_eval;subst.
        clear H_eval. generalize dependent x.
        induction ls.
        **intros x Hx. inversion Hx.
        **intros x Hx. destruct (value_b a) eqn:E_value_a.
          ***option_bind_tac. destruct H_bind. rewrite H0 in Hx. simpl in Hx. inversion Hx; subst.
             apply destrCall_eval_monotone.
             ****value_tac.
             ****value_tac.
             ****simpl in H_values_ls. rewrite Bool.andb_false_iff in H_values_ls.
                 destruct H_values_ls.
                 *****rewrite H1 in E_value_a. inversion E_value_a.
                 *****apply Forall_value_forall_false in H1. assumption.
             ****apply IHls.
                 *****inversion H; subst. assumption.
                 *****simpl in H_values_ls. rewrite Bool.andb_false_iff in H_values_ls.
                 destruct H_values_ls.
                 ******rewrite H1 in E_value_a. inversion E_value_a.
                 ******assumption.
                 *****assumption.
          ***option_bind_tac. destruct H_bind. rewrite H0 in Hx. simpl in Hx. inversion Hx; subst.
             apply STEP_DestrCongr2 with (left := []) (right := ls) (e := a) (e' := x0); step_congr_tac.
             ****value_tac.
             ****inversion H; subst. apply H3. assumption.
    +(* e isn't a value*)
      option_bind_tac. destruct H_bind. rewrite H0 in H_eval. simpl in H_eval. inversion H_eval; subst.
      apply IHe in H0.
      apply STEP_DestrCongr1; step_congr_tac.
  - (* E_FunCall *)
    destruct (forallb value_b ls) eqn:E.
    +(*Evaluate Function call *)
      option_bind_tac.
      destruct H_bind as [fbody H_fbody]. rewrite H_fbody in H_eval. simpl in H_eval.
      inversion H_eval. apply lookup_fun_bods_is_first in H_fbody.
      assert (H_eq : snd (n, fbody) = fbody); try reflexivity.
      rewrite <- H_eq.
      apply STEP_FunCall.
      *apply Forall_value_forall. assumption.
      *assumption.
    +(*Evaluate arguments *)
      option_bind_tac. destruct H_bind. rewrite H0 in H_eval. simpl in H_eval. inversion H_eval; subst.
      rename ls into args. rename x into args'. clear H_eval.
      generalize dependent args'. induction args; intros args' Hx.
      *inversion Hx.
      *destruct(value_b a) eqn: E';option_bind_tac; destruct H_bind as [args'' Hargs''].
       **rewrite Hargs'' in Hx. simpl in Hx. inversion Hx.
         simpl in E. rewrite E' in E. simpl in E.
         inversion H; subst. specialize (IHargs H4 E args'' Hargs'').
         apply Forall_value_forall_false in E.
         apply funcall_eval_monotone; try assumption.
         value_tac.
       **rewrite Hargs'' in Hx. simpl in Hx. inversion Hx.
         apply STEP_FunCallCongr with (left := []) (right := args) (e := a) (e' := args'');step_congr_tac.
         inversion H; subst. apply H3. assumption.
  -(* E_ConsFunCall *)
    destruct (value_b e) eqn:E_value_e.
    + (* e is value *)
      destruct (forallb value_b ls) eqn:E_value_ls.
      * (* All args are values *)
        destruct e; try (solve [inversion H_eval]).
        option_bind_tac.
        destruct H_bind as [ctors H_lookup_ctors]. rewrite H_lookup_ctors in H_eval. simpl in H_eval.
        option_bind_tac.
        destruct H_bind as [body H_lookup_body]. rewrite H_lookup_body in H_eval. simpl in H_eval.
        inversion H_eval.
        destruct sn.
        -- apply STEP_ConsFunCallL with (cfun_body := (q, snd ctors)).
           ++ apply lookup_cfun_bods_x_is_first. assumption.
           ++ reflexivity.
           ++ pose proof H_lookup_body as H_lookup_body2.
              apply lookup_case_In in H_lookup_body. destruct H_lookup_body. simpl. subst.
              destruct body as [b0 b2]. simpl.
              apply lookup_case_is_first in H_lookup_body2. assumption.
           ++ apply Forall_value_forall in E_value_ls. assumption.
           ++ simpl in E_value_e. apply Forall_value_forall in E_value_e. assumption.
        -- apply STEP_ConsFunCallG with (cfun_body := (q, snd ctors)).
           ++ apply lookup_cfun_bods_x_is_first. assumption.
           ++ reflexivity.
           ++ pose proof H_lookup_body as H_lookup_body2.
              apply lookup_case_In in H_lookup_body. destruct H_lookup_body. simpl. subst.
              destruct body as [b0 b2]. simpl.
              apply lookup_case_is_first in H_lookup_body2. assumption.
           ++ apply Forall_value_forall in E_value_ls. assumption.
           ++ simpl in E_value_e. apply Forall_value_forall in E_value_e. assumption.
      * (* One arg is not yet value *)
        option_bind_tac. destruct H_bind.
        rewrite H0 in H_eval. simpl in H_eval. inversion H_eval. subst. clear H_eval.
        generalize dependent x.
        induction ls as [|arg args IHargs]; try ( solve[inversion E_value_ls]).
        intros x Hx. destruct (value_b arg) eqn:E_arg.
        **(* arg is a value *)
          option_bind_tac. destruct H_bind. rewrite H0 in Hx. simpl in Hx. inversion Hx; subst.
          apply matchFunCall_eval_monotone; try value_tac.
          ***simpl in E_value_ls. rewrite Bool.andb_false_iff in E_value_ls. destruct E_value_ls.
             ****rewrite H1 in E_arg. inversion E_arg.
             ****apply Forall_value_forall_false in H1. assumption.
          ***apply IHargs.
             inversion H; subst. assumption. simpl in E_value_ls. rewrite Bool.andb_false_iff in E_value_ls.
             destruct E_value_ls; try assumption.
             ****rewrite H1 in E_arg. inversion E_arg.
             ****assumption.
        **(* arg is not a value *)
          option_bind_tac. destruct H_bind. rewrite H0 in Hx. simpl in Hx. inversion Hx; subst.
          apply STEP_ConsFunCallCongr2 with (left := []) (right := args) (e := arg) (e' := x0);step_congr_tac.
          ***value_tac.
          ***inversion H; subst. apply H3. assumption.
    + (* e isn't value *)
      option_bind_tac.
      destruct H_bind. rewrite H0 in H_eval. simpl in H_eval. inversion H_eval.
      apply STEP_ConsFunCallCongr1;step_congr_tac.
  -(* E_CoConsFunCall *)
    destruct (forallb value_b ls) eqn:E_values_ls; try (solve [inversion H_eval]).
    option_bind_tac. destruct H_bind. rewrite H0 in H_eval. simpl in H_eval. inversion H_eval; subst.
    clear H_eval. generalize dependent x. induction ls.
    +intros x Hx. inversion Hx.
    +intros x Hx. destruct (value_b a) eqn:E_value_a.
     *option_bind_tac. destruct H_bind. rewrite H0 in Hx. simpl in Hx. inversion Hx; subst.
      apply comatchFunCall_eval_monotone.
      **value_tac.
      **apply IHls.
        ***inversion H; subst. assumption.
        ***simpl in E_values_ls. rewrite Bool.andb_false_iff in E_values_ls. destruct E_values_ls.
           rewrite H1 in E_value_a. inversion E_value_a. assumption.
        ***assumption.
     *option_bind_tac. destruct H_bind. rewrite H0 in Hx. simpl in Hx. inversion Hx; subst.
      inversion H; subst. apply H3 in H0.
      apply STEP_GenFunCallCongr with (left := []) (right := ls) (e := a) (e' := x0);step_congr_tac.
  -(* E_Match *)
    destruct (value_b e) eqn:E_value_e.
    +(* e is a value *)
      destruct (forallb value_b (map fst es)) eqn:E_values_es.
      *(*All es are values *)
        destruct e; try (solve [inversion H_eval]).
        option_bind_tac. destruct H_bind. rewrite H1 in H_eval. simpl in H_eval. inversion H_eval; subst.
        (* apply STEP_Match*)
        apply STEP_Match.
        **simpl in E_value_e. apply Forall_value_forall in E_value_e. assumption.
        **apply Forall_value_forall in E_values_es. clear - E_values_es.
          induction es; try apply Forall_nil. inversion E_values_es; subst.
          apply Forall_cons; try assumption.
          apply IHes. assumption.
        **apply lookup_case_is_first with (sn := s). rewrite H1. f_equal. destruct x as [x1 x3]. simpl.  f_equal. f_equal. apply lookup_case_In in H1. destruct H1. simpl in H2. symmetry. assumption.
      *(* At least one of es is not a value *)
        option_bind_tac. destruct H_bind. rewrite H1 in H_eval. simpl in H_eval. inversion H_eval; subst.
        clear - H1 E_value_e E_values_es H0.
        generalize dependent x. induction es.
        ** intros x H; inversion H.
        ** intros x H. destruct a. destruct (value_b e0) eqn:E_value_e0.
           ***option_bind_tac. destruct H_bind. rewrite H1 in H. simpl in H. inversion H; subst.
              apply match_eval_monotone; try value_tac.
              ****clear - E_values_es E_value_e0. simpl in *. rewrite Bool.andb_false_iff in E_values_es. destruct E_values_es.
                  ***** rewrite E_value_e0 in H. inversion H.
                  ***** apply Forall_value_forall_false in H. unfold compose. intro G. apply H. clear H. induction es.
                  apply Forall_nil. inversion G; subst. simpl. apply Forall_cons. assumption. apply IHes. assumption.
              ****apply IHes.
                  *****simpl in E_values_es. rewrite Bool.andb_false_iff in E_values_es. destruct E_values_es.
                  ****** rewrite H2 in E_value_e0. inversion E_value_e0.
                  ******inversion H0; subst. assumption.
                  *****simpl in E_values_es. rewrite Bool.andb_false_iff in E_values_es.
                  destruct E_values_es. rewrite H2 in E_value_e0. inversion E_value_e0. assumption.
                  *****assumption.
           ***option_bind_tac. destruct H_bind. rewrite H1 in H. simpl in H. inversion H; subst.
              apply STEP_MatchCongr2 with (e := e0)(e' := x0)(left := [])(right := (map fst es));step_congr_tac.
              ****value_tac.
              ****inversion H0; subst. apply H4. assumption.
    +(* e isn't a value*)
      option_bind_tac. destruct H_bind. rewrite H1 in H_eval. simpl in H_eval. inversion H_eval; subst.
      apply STEP_MatchCongr1; step_congr_tac.
  -(* E_CoMatch *)
    destruct (forallb value_b (map fst es)) eqn:H_values_es; try (solve [inversion H_eval]).
    option_bind_tac. destruct H_bind. rewrite H1 in H_eval. simpl in H_eval. inversion H_eval; subst.
    clear H_eval H. generalize dependent x.
    induction es.
    *inversion H_values_es.
    *intros x H. destruct a as [a0 a1]. simpl in *.
     destruct (value_b a0) eqn:E_value_a0.
    +option_bind_tac. destruct H_bind. rewrite H1 in H. simpl in H. inversion H; subst.
     apply comatch_eval_monotone.
     **value_tac.
     **apply IHes; try assumption.
       inversion H0; subst. assumption.
    +option_bind_tac. destruct H_bind. rewrite H1 in H. simpl in H. inversion H; subst.
     inversion H0;subst. apply H4 in H1.
     apply STEP_CoMatchCongr with (left := [])(right := (map fst es)) (e := a0) (e' := x0); step_congr_tac.
  -(* E_Let *)
    destruct (value_b e1) eqn:E.
    *inversion H_eval.
     apply STEP_Let.
     value_tac.
    *option_bind_tac. destruct H_bind.
     rewrite H in H_eval. simpl in H_eval. inversion H_eval.
     apply STEP_LetCongr; step_congr_tac.
Defined.

