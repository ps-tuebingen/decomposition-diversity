Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Import ListNotations.

Require Import OptionMonad.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import UtilsProgram.
Require Import AST.
Require Import Names.
Require Import GenericLemmas.
Require Import BodyTypeDefs.
Require Import Typechecker.
Require Import ProgramDef.


(* Within Coq we can only construct programs with the property that all functions typecheck.
The functions exported from this module serve to typecheck user-supplied programs for the extracted code. *)

Fixpoint collapseList {a : Type} (ls : list (option a)) : list a :=
  match ls with
    [] => []
  | (None :: ls') => collapseList ls'
  | (Some a :: ls') => a :: collapseList ls'
  end.

(**************************************************************************************************)
(** * Typechecking Functions.                                                                     *)
(**                                                                                               *)
(**************************************************************************************************)
(* Return a list of the names of all functions which don't typecheck *)
(* Fixpoint typecheck (ps : skeleton) (ctx : ctxt) (e : expr) {struct e} : option TypeName  := *)
Definition typecheckFunctions (prog : program) : list string :=
  let skeleton := program_skeleton prog in
  let functionBodies := program_fun_bods prog in
  let functionSigs := skeleton_fun_sigs skeleton in
  let typecheckSingleFunction : Name * list TypeName * TypeName -> option string :=
      fun fun_sig => match fun_sig with
                    (fname, args, rtype) =>
                    match (lookup_fun_bods prog fname) with
                    | None => None
                    | Some bod =>
                      match typecheck skeleton args bod with
                      | inl _ => Some fname
                      | inr tc_type => if eq_TypeName tc_type rtype then None else Some fname
                      end
                    end
                  end in
  collapseList (map typecheckSingleFunction functionSigs) .


(**************************************************************************************************)
(** * Typechecking Generator Functions.                                                           *)
(**                                                                                               *)
(**************************************************************************************************)
(* Definition gfun_bods_g_typecheck (sk : skeleton) (body : gfun_bod_named) := *)
(*   exists qn (args : list TypeName), lookup_gfun_sig_g sk (fst body) = Some (qn, args) /\ *)
(*                                sk / args |- (E_CoMatch (fst body) *)
(*                                                       (index_list 0 args) *)
(*                                                       (snd body)) *)
(*                                            : (fst (fst body)). *)

(*  | E_CoMatch : QName -> list (expr * TypeName) ->  list (ScopedName * expr) -> expr *)
Fixpoint typecheckGfunBod (sk : skeleton) (qn : QName) (ctx : ctxt) (g : gfun_bod) : bool :=
  let bindingList : list (expr * TypeName) := index_list 0 ctx  in
  let x : expr := E_CoMatch qn bindingList g in
  match typecheck sk ctx x with
  | inl _ => false
  | inr tc_type => if eq_TypeName (fst qn) tc_type then true else false
  end.

(* Return a list of the names of all generator functions which don't typecheck *)
Definition typecheckGeneratorFunctions (prog : program) : list string :=
  let skeleton := program_skeleton prog in
  let gfunBodies := program_gfun_bods_g prog in
  let gfunSigs := skeleton_gfun_sigs_g skeleton in
  let typecheckSingleFunction : QName * list TypeName -> option string :=
      fun gfun_sig => match gfun_sig with
                   | ((tn,n), args) =>
                     match (lookup_gfun_bods_g prog (tn,n)) with
                     | None => None
                     | Some (qn, bod) => if typecheckGfunBod skeleton qn args bod then None else Some n
                     end
                   end in
  collapseList (map typecheckSingleFunction gfunSigs).

(**************************************************************************************************)
(** * Typechecking Consumer Functions.                                                            *)
(**                                                                                               *)
(**************************************************************************************************)

(* Definition cfun_bods_l_typecheck (sk : skeleton) (body : cfun_bod_named) := *)
(*   exists qn (args : list TypeName) (t : TypeName), *)
(*     lookup_cfun_sig_l sk (fst body) = Some (qn, args, t) /\ *)
(*     sk / (fst (fst body) :: args) |- (E_Match (fst body) *)
(*                                              (E_Var 0) *)
(*                                              (index_list 1 args) *)
(*                                              (snd body) *)
(*                                              t) *)
(*                                     : t. *)

Fixpoint typecheckCfunBod (sk : skeleton) (qn: QName) (ctx : ctxt) (c : cfun_bod) (rtype : TypeName) : bool :=
  let bindingList : list (expr * TypeName) := index_list 1 ctx in
  let x : expr := E_Match qn (E_Var 0) bindingList c rtype in
  match typecheck sk (fst qn :: ctx) x with
  | inl _ => false
  | inr tc_type => eq_TypeName tc_type rtype
  end.

(* Return a list of the names of all consumer functions which don't typecheck *)
Definition typecheckConsumerFunctions (prog : program) : list string :=
  let skeleton := program_skeleton prog in
  let cfunBodies := program_cfun_bods_g prog in
  let cfunSigs := skeleton_cfun_sigs_g skeleton in
  let typecheckSingleFunction : QName * list TypeName  * TypeName -> option string :=
      fun cfun_sig => match cfun_sig with
                   |(((tn,n), args),rtype) =>
                    match (lookup_cfun_bods_g prog (tn,n)) with
                    | None => None
                    | Some (qn,bod) => if typecheckCfunBod skeleton qn args bod rtype then None else Some n
                    end
                   end in
  collapseList (map typecheckSingleFunction cfunSigs).


(**************************************************************************************************)
(** * Typechecking whole program.                                                                 *)
(**                                                                                               *)
(**************************************************************************************************)

(* Return a list of all (generator / consumer / ordinary) functions which don't typecheck *)
Definition typecheckProgram (prog : program) : list string * list string * list string :=
  let funsTC := typecheckFunctions prog in
  let gfunsTC := typecheckGeneratorFunctions prog in
  let cfunsTC := typecheckConsumerFunctions prog in
  ((funsTC, gfunsTC),cfunsTC).
