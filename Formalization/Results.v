(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(* Note: This file (and the whole formalization) uses the terms de- and refunctionalization       *)
(* instead of the terms constructorization and destructorization used in the paper                *)
(*                                                                                                *)
(* File: Results.v                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Basics.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Require Import GenericLemmas.
Require Import GenericTactics.
Require Import Names.
Require Import AST.
Require Import Skeleton.
Require Import UtilsSkeleton.
Require Import ProgramDef.
Require Import BodyTypeDefs.
Require Import Program.
Require Import Eval.
Require Import Typechecker.
Require Import Progress.
Require Import Preservation.
Require Import DefuncIV.
Require Import RefuncIV.
Require Import InlineMatch.
Require Import InlineComatch.
Require Import InlineLiftMatch.
Require Import InlineLiftComatch.

(* Note: This file (and the whole formalization) uses the terms de- and refunctionalization       *)
(* instead of the terms constructorization and destructorization used in the paper                *)

(* Since we extract functions to Haskell, we need proofs stating that the implemented functions reflect the inductive relations *)
Theorem typecheck_correct_complete : forall (prog : skeleton) (ctx : ctxt) (e : expr) (tn : TypeName),
    prog / ctx |- e : tn <->
    typecheck prog ctx e = inr tn.
Proof.
  split;
  [ apply typecheck_complete | apply typecheck_correct ].
Qed.
Print Assumptions typecheck_correct_complete.

Theorem eval_correct_complete : forall (prog : program) (e1 e2 : expr),
    [ prog |- e1 ==> e2 ] <->
    one_step_eval prog e1 = Some e2.
Proof.
  split; [apply eval_complete | apply eval_correct ].
Qed.
Print Assumptions eval_correct_complete.

Lemma valueb_correct_complete : forall (e : expr),
    value e <-> value_b e = true.
Proof.
  apply value_iff_valueb.
Qed.
Print Assumptions valueb_correct_complete.

(**************************************************************************************************)
(* Soundness properties of the language.                                                          *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

(* Progress *)

Theorem progress : forall (e : expr) (p : program) (tc : exists t, (program_skeleton p) / [] |- e : t),
    value_b e = true <-> one_step_eval p e = None.
Proof.
  apply progress.
Qed.
Print Assumptions progress.

(* Preservation *)

Theorem preservation : forall (p : program) (e1 e2 : expr) (t : TypeName),
    ((program_skeleton p) / [] |- e1 : t) ->
    [ p |- e1 ==> e2 ] ->
    (program_skeleton p) / [] |- e2 : t.
Proof.
  apply preservation.
Qed.
Print Assumptions preservation.

(**************************************************************************************************)
(* General Prerequisites                                                                          *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

(*
    We use a sorting function [sort_by_index] which takes to lists and a comparison function as an
    argument and sorts the second list according to the first, using the comparison function.
    This function needs to fulfil the following property:
    Permutations.sort_by_index_list_sorted_like_index :
         forall (A B : Type) (f : A -> B -> bool) (index : list A) 
                (to_sort : list B) (g : B -> A),
                Unique.unique index ->
                Permutation.Permutation index (map g to_sort) /\
                (forall (a : A) (b : B), a = g b <-> f a b = true) ->
                map g (Permutations.sort_by_index_list f index to_sort) = index
    i.e. it should sort the list according to the index (modulo function g)
*)

(**************************************************************************************************)
(* Defunctionalization (Constructorization)                                                       *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

(* Defunctionalization is formalized as a three part process:                             *)
(*                                                                                        *)
(*  ----------              ----------              ----------              ----------    *)
(*  |        | liftComatch  |        | defunc       |        | inlineMatch  |        |    *)
(*  |  P1    | ---------->  |  P2    | ---------->  |   P3   | -----------> |   P4   |    *)
(*  |        |              |        |              |        |              |        |    *)
(*  ----------              ----------              ----------              ----------    *)

(* All three parts preserve well-formedness. They are defined by [defunctionalize_program_with_lift], *)
(* which combines the first two parts (lifting and core defunc), and [inline_cfuns_to_program] for    *)
(* the third part. Since well-formedness is part of the program definition, these algorithms are      *)
(* responsible for maintaining it.                                                                    *)
(*                                                                                                    *)
(* liftComatch extracts local comatches as "local gfuns", i.e. gfuns with a "local" annotation, while *)
(* inlineMatch inlines the "local cfuns" as local matches                                             *)
(*                                                                                                    *)
(* To combine them, we need two prerequisites which involve tedious to prove in Coq, but not very     *)
(* interesting, "plumbing" lemmas. For these we do not have Coq proofs but provide an explanation why *)
(* they hold; see the "Prerequisites" section below.                                                  *)


(* Prerequisites *)

(* 1. Uniqueness of local destructor names *)
(* Background: For a program to be well-formed, we require that names of local matches and comatches
   are unique. After defunctionalization, a local destructor call is turned into a local match.
   
   Therefore, we require that before defunctionalization, a local destructor is only called once in the
   entire program. This ensures that the local matches created by defunctionalization from the local
   destructors have unique names.

   This property [defunc_preserves_local_cfuns] (see below) is among the "plumbing lemmas".
 *)

(* Collect the names of local destructors called in the given expression. *)
Fixpoint collect_called_local_destructor_names (e : expr) : list QName :=
  match e with
  | E_Var x => []
  | E_Constr _ x0 => List.concat (List.map collect_comatch_names x0)
  | E_DestrCall (local q) x0 x1 => q :: List.concat (List.map collect_comatch_names (x0 :: x1))
  | E_DestrCall _ x0 x1 => List.concat (List.map collect_comatch_names (x0 :: x1))
  | E_FunCall _ x => List.concat (List.map collect_comatch_names x)
  | E_GenFunCall _ x0 => List.concat (List.map collect_comatch_names x0)
  | E_ConsFunCall x x0 x1 => List.concat (List.map collect_comatch_names (x0 :: x1))
  | E_Match _ x0 x2 x3 _ => let bs_names := List.map (fun x => collect_comatch_names ( fst x)) x2 in
                               let case_names := List.map (fun x => collect_comatch_names (snd x)) x3 in
                               (collect_comatch_names x0) ++ List.concat (bs_names ++ case_names)
  | E_CoMatch _  x1 x2 => let bs_names := List.map (fun x => collect_comatch_names (fst x)) x1 in
                           let case_names := List.map (fun x => collect_comatch_names (snd x)) x2 in
                           List.concat (bs_names ++  case_names)
  | E_Let x x0 => (collect_comatch_names x) ++ (collect_comatch_names x0)
  end.

(* The names of local destructors called in the given function bodies are unique. *)
Definition called_local_destructor_names_unique (fbt : fun_bods) (mfbt : cfun_bods) (cmfbt : gfun_bods) : Prop :=
  let fbodies : list expr := List.map snd fbt in
  let mfbodies : list expr := List.map snd (List.concat (List.map snd mfbt)) in
  let cmfbodies := List.map snd (List.concat (List.map snd cmfbt)) in
  Unique.unique (List.concat (List.map collect_called_local_destructor_names (fbodies ++ mfbodies ++ cmfbodies))).

(* The names of local destructors called in the given program are unique. *)
Definition called_local_destructor_names_unique_in_prog p :=
  called_local_destructor_names_unique
    (program_fun_bods p)
    (program_cfun_bods_g p ++ program_cfun_bods_l p)
    (program_gfun_bods_g p ++ program_gfun_bods_l p).

(* note: defunctionalization = constructorization *)
(* After defunctionalization, each local consumer function is only called once. *)
(* Defunctionalization redistributes the bodies of cocases to the newly created
   consumer functions, but does not delete or add new such bodies.
   Since it also only creates local consumer function calls for the relevant type
   where there had previously been a local destructor call with the same name,
   this property holds given that names of called local destructors are unique.
 *)
Theorem defunc_preserves_local_cfuns : forall (p : program) (tn : TypeName),
    called_local_destructor_names_unique_in_prog p ->
    local_cfuns_only_used_once (defunctionalize_program_with_lift p tn).
Proof.
Admitted. (* check Results.v for details on missing proofs *)

(* 2. Ordering for inline *)
(* In order to be able to inline the cfuns which result from defunctionalization, we need to ensure   *)
(* that there is an ordering of these functions that allows sequential inlining.                      *)
(* This is required since in general, there might be recursive "loops", e.g. a local cfun foo() which *)
(* calls itself in its body.                                                                          *)
(* This would result in a loop when inlining, since this would correspond to something like this:     *)
(* match _foo ... with                                                                                *)
(* ... match _foo ... with                                                                            *)
(*     ... match _foo ... with ...                                                                    *)
(*                                                                                                    *)
(* Fortunately, these cases are not in the image of the defunctionalization function, since programs  *)
(* can only contain one call to every local destructor and since local cfun calls are in 1:1-corres-  *)
(* pondence with destructor calls in the original program                                             *)

(* We need two more assumptions for the following theorems:
    sort_cfuns_for_inline_permutes:
        forall p : program,
            Permutation.Permutation (program_cfun_bods_l p) (sort_cfuns_for_inline p (program_cfun_bods_l p))
    i.e. that sorting the cfuns of a program is a permutation of the original

    sort_cfuns_for_inline_ordered_cfun :
        forall p : program,
                local_cfuns_only_used_once p ->
                inline_ordered_cfun (sort_cfuns_for_inline_bods p)
    i.e. that sorting cfuns for inlining will result in an ordering that can be inlined

    Additionally, we need two assumptions which are not directly related to the correctness of the
    theorems below, but concern the preservation of two well-formedness conditions by the inlining
    function:
    match_names_unique_after_inline_match :
        forall p : program,
                match_names_unique (program_fun_bods p) (program_cfun_bods_g p ++ program_cfun_bods_l p)
                                   (program_gfun_bods_g p ++ program_gfun_bods_l p) ->
                match_names_unique (InlineMatch.new_fun_bods p)
                    (InlineMatch.new_cfun_bods_g p ++ InlineMatch.new_cfun_bods_l p)
                    (InlineMatch.new_gfun_bods_g p ++ InlineMatch.new_gfun_bods_l p)
    i.e. that after inlining, the names of all local matches will still be unique

    comatch_names_unique_after_inline_match :
        forall p : program,
                comatch_names_unique (program_fun_bods p) (program_cfun_bods_g p ++ program_cfun_bods_l p)
                                     (program_gfun_bods_g p ++ program_gfun_bods_l p) ->
                comatch_names_unique (InlineMatch.new_fun_bods p)
                    (InlineMatch.new_cfun_bods_g p ++ InlineMatch.new_cfun_bods_l p)
                    (InlineMatch.new_gfun_bods_g p ++ InlineMatch.new_gfun_bods_l p)
    i.e. that after inlining, the names of all local comatches will still be unique
            *)

Theorem sort_cfuns_preserves_local_cfuns : forall (p : program) (tn : TypeName),
    called_local_destructor_names_unique_in_prog p ->
    local_cfuns_only_used_once (sort_cfuns_for_inline_program (defunctionalize_program_with_lift p tn)).
Proof.
  intros.
  apply sort_cfuns_for_inline_preserves_local_cfuns_only_used_once.
  apply defunc_preserves_local_cfuns. auto.
Qed.
Print Assumptions sort_cfuns_preserves_local_cfuns.
(* This theorem has the following assumptions:
   - [sort_cfuns_for_inline_permutes]
   - [Permutations.sort_by_index_list_sorted_like_index]
   - [defunc_preserves_local_cfun]
   These are explained in the prerequisites above
   *)

Theorem defunc_generates_inline_ordered_cfuns : forall (p : program) (tn : TypeName),
    called_local_destructor_names_unique_in_prog p ->
    inline_ordered_cfun (program_cfun_bods_l (sort_cfuns_for_inline_program (defunctionalize_program_with_lift p tn))).
Proof.
  intros p tn H.
  apply sort_cfuns_for_inline_ordered_cfun.
  apply defunc_preserves_local_cfuns; assumption.
Qed.
Print Assumptions defunc_generates_inline_ordered_cfuns.
(* This theorem has the following assumptions:
   - [defunc_preserves_local_cfuns]
   - [sort_cfuns_for_inline_ordered_cfun]
   These are explained in the prerequisites above
   *)

(* End Prerequisites *)

(* Complete defunctionalization algorithm *)
Definition defunc_complete (p : program) (tn: TypeName)
    (pr : program_cfun_bods_l p = [])  (pr' : program_gfun_bods_l p = [])
    (Uniq : called_local_destructor_names_unique_in_prog p)
  : program :=
  let x := defunctionalize_program_with_lift p tn in
  let y := sort_cfuns_for_inline_program x in
  inline_cfuns_to_program y (sort_cfuns_preserves_local_cfuns p tn Uniq)
    (defunc_generates_inline_ordered_cfuns p tn Uniq).

Print Assumptions defunc_complete.
(* This theorem has the following assumptions:
   - [sort_cfuns_for_inline_permutes ]
   - [sort_cfuns_for_inline_ordered_cfun]
   - [Permutations.sort_by_index_list_sorted_like_index]
   - [match_names_unique_after_inline_match]
   - [comatch_names_unique_after_inline_match]
   - [defunc_preserves_local_cfuns]
   These are explained in the prerequisites above
   *)


(**************************************************************************************************)
(* Refunctionalization (Destructorization)                                                        *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

(* Refunctionalization is formalized as a three part process:                             *)
(*                                                                                        *)
(*  ----------              ----------              ----------              ----------    *)
(*  |        | liftMatch    |        | refunc       |        |inlineComatch |        |    *)
(*  |  P1    | ---------->  |  P2    | ---------->  |   P3   | -----------> |   P4   |    *)
(*  |        |              |        |              |        |              |        |    *)
(*  ----------              ----------              ----------              ----------    *)

(* All three parts preserve well-formedness. They are defined by [refunctionalize_program_with_lift], *)
(* which combines the first two parts (lifting and core refunc), and [inline_cfuns_to_program] for    *)
(* the third part. Since well-formedness is part of the program definition, these algorithms are      *)
(* responsible for maintaining it.                                                                    *)
(*                                                                                                    *)
(* liftMatch extracts local comatches as "local cfuns", i.e. cfuns with a "local" annotation, while   *)
(* inlineCoMatch inlines the "local gfuns" as local comatches                                         *)
(*                                                                                                    *)
(* To combine them, we need two prerequisites which involve tedious to prove in Coq, but not very     *)
(* interesting, "plumbing" lemmas. For these we do not have Coq proofs but provide an explanation why *)
(* they hold; see the "Prerequisites" section below.                                                  *)


(* Prerequisites (analogous to defunctionalization prerequisites) *)

(* 1. Uniqueness of local constructor names *)
(* Background: For a program to be well-formed, we require that names of local matches and comatches
   are unique. After refunctionalization, a local constructor call is turned into a local comatch.
   
   Therefore, we require that before refunctionalization, a local constructor is only called once in the
   entire program. This ensures that the local comatches created by refunctionalization from the local
   constructors have unique names.

   This property [refunc_preserves_local_gfuns] (see below) is among the tedious to prove in Coq, but not
   very interesting, "plumbing" lemmas. 
 *)

(* Collect the names of local constructors called in the given expression. *)
Fixpoint collect_called_local_constructor_names (e : expr) : list QName :=
  match e with
  | E_Var x => []
  | E_Constr (local q) x0 => q :: List.concat (List.map collect_comatch_names x0)
  | E_Constr _ x0 => List.concat (List.map collect_comatch_names x0)
  | E_DestrCall _ x0 x1 => List.concat (List.map collect_comatch_names (x0 :: x1))
  | E_FunCall _ x => List.concat (List.map collect_comatch_names x)
  | E_GenFunCall _ x0 => List.concat (List.map collect_comatch_names x0)
  | E_ConsFunCall x x0 x1 => List.concat (List.map collect_comatch_names (x0 :: x1))
  | E_Match _ x0 x2 x3 _ => let bs_names := List.map (fun x => collect_comatch_names ( fst x)) x2 in
                               let case_names := List.map (fun x => collect_comatch_names (snd x)) x3 in
                               (collect_comatch_names x0) ++ List.concat (bs_names ++ case_names)
  | E_CoMatch _  x1 x2 => let bs_names := List.map (fun x => collect_comatch_names (fst x)) x1 in
                           let case_names := List.map (fun x => collect_comatch_names (snd x)) x2 in
                           List.concat (bs_names ++  case_names)
  | E_Let x x0 => (collect_comatch_names x) ++ (collect_comatch_names x0)
  end.

(* The names of local constructors called in the given function bodies are unique. *)
Definition called_local_constructor_names_unique (fbt : fun_bods) (mfbt : cfun_bods) (cmfbt : gfun_bods) : Prop :=
  let fbodies : list expr := List.map snd fbt in
  let mfbodies : list expr := List.map snd (List.concat (List.map snd mfbt)) in
  let cmfbodies := List.map snd (List.concat (List.map snd cmfbt)) in
  Unique.unique (List.concat (List.map collect_called_local_constructor_names (fbodies ++ mfbodies ++ cmfbodies))).

(* The names of local constructors called in the given program are unique. *)
Definition called_local_constructor_names_unique_in_prog p :=
  called_local_constructor_names_unique
    (program_fun_bods p)
    (program_cfun_bods_g p ++ program_cfun_bods_l p)
    (program_gfun_bods_g p ++ program_gfun_bods_l p).

(* note: defunctionalization = destructorization *)
(* After refunctionalization, each local generator function is only called once. *)
(* Refunctionalization redistributes the bodies of cases to the newly created
   generator functions, but does not delete or add new such bodies.
   Since it also only creates local generator function calls for the relevant type
   where there had previously been a local constructor call with the same name,
   this property holds given that names of called local constructors are unique.
 *)
Theorem refunc_preserves_local_gfuns : forall (p : program) (tn : TypeName),
    called_local_constructor_names_unique_in_prog p ->
    local_gfuns_only_used_once (refunctionalize_program_with_lift p tn).
Proof.
Admitted. (* check Results.v for details on missing proofs *)


(* 2. Ordering for inline *)
(* In order to be able to inline the gfuns which result from refunctionalization, we need to ensure   *)
(* that there is an ordering of these functions that allows sequential inlining.                      *)
(* This is required since in general, there might be recursive "loops", e.g. a local gfun foo() which *)
(* calls itself in its body.                                                                          *)
(* This would result in a loop when inlining, since this would correspond to something like this:     *)
(* comatch _foo ... with                                                                                *)
(* ... comatch _foo ... with                                                                            *)
(*     ... comatch _foo ... with ...                                                                    *)
(*                                                                                                    *)
(* Fortunately, these cases are not in the image of the refunctionalization function, since programs  *)
(* can only contain one call to every local destructor and since local gfun calls are in 1:1-corres-  *)
(* pondence with destructor calls in the original program                                             *)

(* We need two more assumptions for the following theorems:
    sort_gfuns_for_inline_permutes:
        forall p : program,
            Permutation.Permutation (program_gfun_bods_l p) (sort_gfuns_for_inline p (program_gfun_bods_l p))
    i.e. that sorting the gfuns of a program is a permutation of the original

    sort_gfuns_for_inline_ordered_gfun :
        forall p : program,
                local_gfuns_only_used_once p ->
                inline_ordered_gfun (sort_gfuns_for_inline_bods p)
    i.e. that sorting gfuns for inlining will result in an ordering that can be inlined

    Additionally, we need two assumptions which are not directly related to the correctness of the
    theorems below, but concern the preservation of two well-formedness conditions by the inlining
    function:
    match_names_unique_after_inline_comatch :
        forall p : program,
                match_names_unique (program_fun_bods p) (program_cfun_bods_g p ++ program_cfun_bods_l p)
                                   (program_gfun_bods_g p ++ program_gfun_bods_l p) ->
                match_names_unique (new_fun_bods p)
                    (new_cfun_bods_g p ++ new_cfun_bods_l p)
                    (new_gfun_bods_g p ++ new_gfun_bods_l p)
    i.e. that after inlining, the names of all local matches will still be unique

    comatch_names_unique_after_inline_comatch :
        forall p : program,
                comatch_names_unique (program_fun_bods p) (program_cfun_bods_g p ++ program_cfun_bods_l p)
                                     (program_gfun_bods_g p ++ program_gfun_bods_l p) ->
                comatch_names_unique (new_fun_bods p)
                    (new_cfun_bods_g p ++ new_cfun_bods_l p)
                    (new_gfun_bods_g p ++ new_gfun_bods_l p)
    i.e. that after inlining, the names of all local comatches will still be unique
            *)


Theorem sort_gfuns_preserves_local_gfuns : forall (p : program) (tn : TypeName),
    called_local_constructor_names_unique_in_prog p ->
    local_gfuns_only_used_once (sort_gfuns_for_inline_program (refunctionalize_program_with_lift p tn)).
Proof.
  intros.
  apply sort_gfuns_for_inline_preserves_local_gfuns_only_used_once.
  apply refunc_preserves_local_gfuns. auto.
Qed.
Print Assumptions sort_gfuns_preserves_local_gfuns.
(* This theorem has the following assumptions:
   - [sort_gfuns_for_inline_permutes]
   - [Permutations.sort_by_index_list_sorted_like_index]
   - [refunc_preserves_local_cfun]
   These are explained in the prerequisites above
   *)

Theorem refunc_generates_inline_ordered_gfuns : forall (p : program) (tn : TypeName),
    called_local_constructor_names_unique_in_prog p ->
    inline_ordered_gfun (program_gfun_bods_l (sort_gfuns_for_inline_program (refunctionalize_program_with_lift p tn))).
Proof.
  intros p tn H.
  apply sort_gfuns_for_inline_ordered_gfun.
  apply refunc_preserves_local_gfuns; assumption.
Qed.
Print Assumptions refunc_generates_inline_ordered_gfuns.
(* This theorem has the following assumptions:
   - [sort_gfuns_for_inline_ordered_gfun]
   - [refunc_preserves_local_cfun]
   These are explained in the prerequisites above
   *)

(* End Prerequisites *)

(* Complete refunctionalization algorithm *)
Definition refunc_complete (p : program) (tn: TypeName)
    (pr : program_cfun_bods_l p = [])  (pr' : program_gfun_bods_l p = [])
    (Uniq : called_local_constructor_names_unique_in_prog p)
  : program :=
  let x := refunctionalize_program_with_lift p tn in
  let y := sort_gfuns_for_inline_program x in
  inline_gfuns_to_program y (sort_gfuns_preserves_local_gfuns p tn Uniq)
    (refunc_generates_inline_ordered_gfuns p tn Uniq).

Print Assumptions refunc_complete.
(* This theorem has the following assumptions:
   - [sort_gfuns_for_inline_permutes]
   - [sort_gfuns_for_inline_ordered_gfun]
   - [Permutations.sort_by_index_list_sorted_like_index]
   - [new_match_names_unique]
   - [new_comatch_names_unique]
   - [refunc_preserves_local_gfuns]
   These are explained in the prerequisites above
   *)


(**************************************************************************************************)
(* Defunctionalization and refunctionalization are inverse to each other                          *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

(* The core parts of defunctionalization and refunctionalization (i.e., without lift and inline)
   are inverse to each other. This is shown by these Coq proofs:
 *)

Require Import XfuncInverse.

(* note: defunctionalization = constructorization *)
(* note: refunctionalization = destructorization  *)
(* Defunc., then refunc. *)
Print derefunc_preserves_prog.
Print Assumptions derefunc_preserves_prog.
(* Assumptions:
   proof_irrelevance:
        we use proof irrelevance in certain places to show equality between programs or skeletons,
        since we do not care about the content of their well-formedness properties
*)

(* note: defunctionalization = constructorization *)
(* note: refunctionalization = destructorization  *)
(* Refunc., then defunc. *)
Print redefunc_preserves_prog.
Print Assumptions redefunc_preserves_prog.
(* Assumptions:
   proof_irrelevance:
        we use proof irrelevance in certain places to show equality between programs or skeletons,
        since we do not care about the content of their well-formedness properties
*)

(* The properties both have preconditions that require that constructor and destructor
   and consumer/generator function signatures as well as (co)datatype names are ordered
   in a certain way. This reordering does not affect typechecking and semantics.
 *)

(* The complete algorithms for defunctionalization and refunctionalization are made up
   of multiple parts, as explained above. This means that the inverseness statement
   for the complete de- and refunctionalization is:
 *)

(* lift_comatches . defunctionalize_core . sort_cfuns_for_inline_program . inline_local_cfuns .
   lift_matches . refunctionalize_core . sort_gfuns_for_inline_program . inline_local_gfuns
   = id, up to permutation of functions and signatures
 *)
(* We will from now on consider = to mean equality up to such permutation. *)

(* Sortin local consumer functions, then inlining local consumer functions and
   finally lifting these just inlined matches is equality in this sense. Thus we have:
 *)
(* lift_comatches . defunctionalize_core . sort_cfuns_for_inline_program . inline_local_cfuns .
   lift_matches . refunctionalize_core . sort_gfuns_for_inline_program . inline_local_gfuns

 = lift_comatches . defunctionalize_core . refunctionalize_core . 
   sort_gfuns_for_inline_program . inline_local_gfuns
 *)

(* By the Coq proof [derefunc_preserves_prog] given above, core de- and refunctionalization are
   inverse to each other, so we eliminate their composition:
 *)
(*
   lift_comatches . defunctionalize_core . refunctionalize_core
   sort_gfuns_for_inline_program . inline_local_gfuns

 = lift_comatches . sort_gfuns_for_inline_program . inline_local_gfuns
 *)

(* Lifting comatches, sorting and then inlining the thus created generator functions is also equality,
   thus we can finish the proof:
 *)
(*
   lift_comatches . sort_gfuns_for_inline_program . inline_local_gfuns = id, up to permutation
 *)


(* The proof for the other direction (statement shown below) is analogous. *)

(* lift_matches . refunctionalize_core . sort_gfuns_for_inline_program . inline_local_gfuns .
   lift_comatches . defunctionalize_core . sort_cfuns_for_inline_program . inline_local_cfuns
   = id, up to permutation of functions and signatures
 *)


(**************************************************************************************************)
(* Defunctionalization and refunctionalization preserve semantics                                 *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

(*
    Since cases and cocases in our matches and comatches are always exhaustive and non-overlapping,
    changing their order in a match will not change the result of the one_step_eval function.
    Similarly, changing the ordering of any part of the surrounding program, like the list of cfun
    bodies, has no effect on evaluation.
    Hence, we only need to consider the three parts of the full xfunc algorithms in which
    substantial changes are performed:
    - lifting xmatches,
    - core xfunc,
    - inlining xmatches.
    Proofs for these three parts follow below.

    ------------------------------------------------------------------------------------------------

    Lemma R1.1: Given an expression expr, the result of (lift_match expr) will be a value iff expr
        is a value.
    Proof.
        We will perform an induction on the structure of expr.
        Most cases are congruence cases and thus trivial.
        The only interesing case is a match on the type in consideration.
        A match can never be a value and correspondingly, since
        match d on e using bs with
            ...
        with name d, expression e and bindings list bs will be translated into
        e'.d(bs'),
        where e' and bs' are the recursively translated expression e and bindings list bs,
        respectively, the result will also not be a value.
    Qed.

    Lemma D1.1: Given an expression expr, the result of (lift_comatch expr) will be a value iff expr
        is a value.
    Proof.
        We will perform an induction on the structure of expr.
        Most cases are congruence cases and thus trivial.
        The only interesing case is a comatch on the type in consideration.
        A comatch
        comatch C on T using bs with
            ...
        with name C, type T and bindings list bs is a value iff all expressions in bs are values and
        will be translated into
        C(bs')
        where bs' is the recursively translated bindings list bs.
        This result will also only be a value if bs' consists of values and thus we can conclude
        with the induction hypothesis.
    Qed.

    Lemma R1.2: Given an expression expr, the result of (lift_match expr) will be a redex iff expr
        is a redex.
    Proof.
        We will once again use induction over the structure of expr.
        Using progress, we can conclude that non-redexes are preserved, since they are values and
        thus will stay values according to Lemma R1.1.
        A redex is either a destructor call, a match or a cfun call.
        All other cases are immediate congruence cases and thus only require to check that the
        arguments stay values/non-values.
        This can be concluded by using Lemma R1.1.
        Similarly, the case of a destructor call is also a congruence case, since we are lifting
        matches and thus the type parameter of the lifting function is a data type and hence
        different from the type of the destructor in a destructor call.
        Likewise, the case of a cfun call is also not interesting, since cfun calls are not changed
        by the lifting (apart from congruence).
        In the case of a match, we have to differentiate between a match on the type under
        consideration and matches on a different type.
        In the latter case, we can once again apply our congruence rule and finish with the
        induction hypothesis.
        Finally, in the case of a match on the type onder consideration,
        match d on e using bs
            ...
        will once again be translated to
        e'.d(bs'),
        with e' and bs' being the recursively translated expression e and bindings list bs,
        respectively.
        The match will be a redex iff e and all expressions in bs are values.
        Similarly, the cfun call will be a redex iff and only e' and all expressions in bs' are
        values.
        This can easily be confirmed by application of Lemma R1.1, thus concluding the proof.
    Qed.

    Lemma D1.2: Given an expression expr, the result of (lift_comatch expr) will be a redex iff expr
        is a redex.
    Proof.
        We will once again use induction over the structure of expr.
        Using progress, we can conclude that non-redexes are preserved, since they are values and
        thus will stay values according to Lemma D1.1.
        A redex is either a destructor call, a match or a cfun call.
        All other cases are immediate congruence cases and thus only require to check that the
        arguments stay values/non-values.
        This can be concluded by using Lemma R1.1.
        Similarly, the case of a match or cfun call is also a congruence case, since we are lifting
        comatches and thus the type parameter of the lifting function is a codata type and hence
        different from the type of the type being matched on or the type of the cfun being called,
        respectively.
        In the case of a destructor call, we have to differentiate between a destructor call on the
        type under consideration and destructor call on a different type.
        In the latter case, we can once again apply our congruence rule and finish with the
        induction hypothesis.
        Finally, in the case of a destructor call on the type onder consideration,
        e.d(bs)
        will once again be translated to
        e'.d(bs'),
        with e' and bs' being the recursively translated expression e and bindings list bs,
        respectively.
        If e is a gfun call, the result will be the same gfun call with recursively translated
        arguments and it is hence another congruence case.
        If e is a comatch
        comatch C on T using cs with
            ...
        then it will be translated into
        C(cs'),
        with cs' being the recursively translated arguments (with removed type annotations).
        Thus, the result C(cs').d(bs')
        will be a redex iff all expressions in cs' and bs' are values.
        Using Lemma D1.1, this is the case iff cs and bs consist of values, which is precisely iff
        the original expression is a redex.
    Qed.


    Lemma D1.3 Given an expression expr,
        one_step_eval (lift_match expr) = lift_match (one_step_eval expr),
        i.e. lift_match preserves reduction.
    Proof.
        First, fix T to be the type of matches to be lifted.
        We will perform an induction on the structure of expr.
        Since, by Lemmas D1.1 and D1.2, lifting preserves values and redexes, we only need to
        consider the case of redexes which involve a match on a constructor of T where all arguments
        and expressions in the bindings list are already values, since all other cases are once
        again congruences that can immediately be handled by induction.
        In the remaining case, we have
        match d on C(as) using ws:bs returning T' with
            ...
            C(vs) => e
            ...
        with d and C being names for the match and a constructor for T, respectively, as a list of
        values, ws:bs a bindings list (i.e. ws a list of variables and bs the corresponding list of
        values), vs a list of variables and e an expression.
        Reducing this by one step would result in
        e[vs -> as][ws -> bs],
        i.e. substituting the variables vs by the values as and substituting the variables specified
in bs by their corresponding values.
        The result of lifting this expression would be
        C(as').d'(bs'),
        where as and bs are the result of recursively performing lifting in as and bs (and in the
        latter case, removing type annotations), respectively, and d' is the name of the cfun
        corresponding to the match d.
        Additionally, there would be a new cfun in the program, with body
        cfun T : d'(ws) : T' :=
            ...
            C(vs) => e'
            ...
        with e' being the result of performing lifting in e.
        Reducing C(as').d'(bs') would result in
        e'[vs -> as'][ws -> bs'].
        By the substition lemma lift_match_subst, this is also the result of lifting 
        e[vs -> as][ws -> bs].
    Qed.

    Lemma R1.3 Given an expression expr,
        one_step_eval (lift_comatch expr) = lift_comatch (one_step_eval expr),
        i.e. lift_comatch preserves reduction.
    Proof.
        First, fix T to be the type of matches to be lifted.
        We will perform an induction on the structure of expr.
        Since, by Lemmas R1.1 and R1.2, lifting preserves values and redexes, we only need to
        consider the case of redexes which involve a destructor call on a comatch on T where all
        arguments and expressions in the bindings list are already values, since all other cases are
        once again congruences that can immediately be handled by induction.
        In the remaining case, we have
        comatch C on T using ws:bs with
            ...
            d(vs) => e
            ...).d(as).
        with C and d being names for the comatch and a destructor for T, respectively, as a list of
        values, ws:bs a bindings list (i.e. ws a list of variables and bs the corresponding list of
        values), vs a list of variables and e an expression.
        Reducing this by one step would result in
        e[vs -> as][ws -> bs],
        i.e. substituting the variables vs by the values as and substituting the variables specified
        in bs by their corresponding values.
        The result of lifting this expression would be
        C'(as').d(bs'),
        where as and bs are the result of recursively performing lifting in as and bs (and in the
        latter case, removing type annotations), respectively, and C' is the name of the gfun
        corresponding to the comatch C.
        Additionally, there would be a new dfun in the program, with body
        dfun C'(ws) : T :=
            ...
            d(vs) => e'
            ...
        with e' being the result of performing lifting in e.
        Reducing C'(as').d(bs') would result in
        e'[vs -> as'][ws -> bs'].
        By the substition lemma lift_comatch_subst, this is also the result of lifting
        e[vs -> as][ws -> bs].
    Qed.

    ------------------------------------------------------------------------------------------------

    Lemma R2.1: Given an expression expr, the result of (refunctionalize expr) will be a value iff
        expr is a value.
    Proof.
        First, fix T to be the type to be refunctionalized.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some constructor C of type T and a list of expressions as or
        e.d(as)
        for some expression e of type T, a cfun d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction.
        If it is of the first form C(as), then it is a value iff all expressions in as are values.
        The result of refunctionalization of C(as) will be
        C'(as'),
        where C' is the new gfun corresponding to C and as' are the recursively refunctionalized
        arguments.
        This is a value iff all expressions in as' are values, which by induction is true iff all
        expressions in as are values, which is true iff C(as) is a value.
        Similarly, in the second case, e.d(as) is not a value and its refunctionalization is
        e'.d'(as')
        with e' the refunctionalization of e, d' the new destructor corresponding to d and as' the
        recursively refunctionalized list as.
        This is also not a value, thus concluding the proof.
    Qed.

    Lemma D2.1: Given an expression expr, the result of (defunctionalize expr) will be a value iff
        expr is a value.
    Proof.
        First, fix T to be the type to be refunctionalized.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some gfun C of type T and a list of expressions as or
        e.d(as)
        for some expression e of type T, a destructor d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction.
        If it is of the first form C(as), then it is a value iff all expressions in as are values.
        The result of defunctionalization of C(as) will be
        C'(as'),
        where C' is the new constructor corresponding to C and as' are the recursively
        defunctionalized arguments.
        This is a value iff all expressions in as' are values, which by induction is true iff all
        expressions in as are values, which is true iff C(as) is a value.
        Similarly, in the second case, e.d(as) is not a value and its defunctionalization is
        e'.d'(as')
        with e' the defunctionalization of e, d' the new cfun corresponding to d and as' the
        recursively defunctionalized list as.
        This is also not a value, thus concluding the proof.
    Qed.

    Lemma R2.2: Given an expression expr, the result of (refunctionalize expr) will be a redex iff
        expr is a redex.
    Proof.
        First, fix T to be the type to be refunctionalized.
        We start by induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some constructor C of type T and a list of expressions as or
        e.d(as)
        for some expression e of type T, a cfun d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction and
        Lemma R2.1.
        If it is of the first form C(as), then it is not an outermost redex.
        The result of refunctionalization of C(as) will be
        C'(as'),
        where C' is the new gfun corresponding to C and as' are the recursively refunctionalized
        arguments.
        This also can never be a redex.
        Similarly, in the second case, e.d(as) is a redex iff e and all expressions in as are values
        and its refunctionalization is
        e'.d'(as')
        with e' the refunctionalization of e, d' the new destructor corresponding to d and as' the
        recursively refunctionalized list as.
        This is a redex iff e' and all expressions in as' are values, which by Lemma R2.1 is the
        case iff e and all expressions in as are values, which is once again is true iff the
        e.d(as) is a redex.
    Qed.

    Lemma D2.2: Given an expression expr, the result of (defunctionalize expr) will be a redex iff
        expr is a redex.
    Proof.
        First, fix T to be the type to be defunctionalized.
        We start by induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some gfun C of type T and a list of expressions as or
        e.d(as)
        for some expression e of type T, a destructor d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction and
        Lemma D2.1.
        If it is of the first form C(as), then it is not an outermost redex.
        The result of defunctionalization of C(as) will be
        C'(as'),
        where C' is the new constructor corresponding to C and as' are the recursively
        defunctionalized arguments.
        This also can never be a redex.
        Similarly, in the second case, e.d(as) is a redex iff e and all expressions in as are values
        and its defunctionalization is
        e'.d'(as')
        with e' the defunctionalization of e, d' the new cfun corresponding to d and as' the
        recursively defunctionalized list as.
        This is a redex iff e' and all expressions in as' are values, which by Lemma D2.1 is the
        case iff e and all expressions in as are values, which is once again is true iff the
        e.d(as) is a redex.
    Qed.

    Lemma R2.3 Given an expression expr,
        one_step_eval (refunctionalize expr) = refunctionalize (one_step_eval expr),
        i.e. refunctionalize preserves reduction.
    Proof.
        First, fix T to be the type to be refunctionalized.
        We will perform an induction on the structure of expr.
        Since, by Lemmas R2.1 and R2.2, refunctionalization preserves values and redexes, we only
        need to consider the case of redexes which involve a cfun call on a constructor on T where
        all arguments are already values, since all other cases are once again congruences that can
        immediately be handled by induction.
        In the remaining case, we have
        C(as).d(bs),
        where as and bs are lists of values, C and d are names of a constructor and a cfun on T,
        respectively.
        Furthermore, we have a cfun
        cfun T: d(ws) : T' :=
            ...
            C(vs) => e
            ...
        for some expression e.
        Hence, reducing would result in
        e[vs -> as][ws -> bs].
        After refunctionalization, we get
        C'(as').d'(bs'),
        with as' and bs' being the recursively refunctionalized expression list as and bs,
        respectively, and C' and d' being the new corresponding gfun and destructor names,
        respectively.
        Additionally, we replace the cfun d by a new gfun
        gfun C(vs) : T :=
            ...
            d(ws) => e'
            ...
        with variable lists vs and ws as well as the expression e', which is the result of
        refunctionalizing e.
        Reducing the result would yield
        e'[vs -> as'][ws -> bs'],
        which, by the substition lemma refunc_substitution, is the result of refunctionalizing
        e[vs -> as][ws -> bs].
    Qed.

    Lemma D2.3 Given an expression expr,
        one_step_eval (defunctionalize expr) = defunctionalize (one_step_eval expr),
        i.e. defunctionalize preserves reduction.
    Proof.
        First, fix T to be the type to be defunctionalized.
        We will perform an induction on the structure of expr.
        Since, by Lemmas D2.1 and D2.2, defunctionalization preserves values and redexes, we only
        need to consider the case of redexes which involve a destructor call on a gfun on T where
        all arguments are already values, since all other cases are once again congruences that can
        immediately be handled by induction.
        In the remaining case, we have
        C(as).d(bs),
        where as and bs are lists of values, C and d are names of a gfun and a destructor on T,
        respectively.
        Furthermore, we have a gfun
        gfun T: d(ws) : T' :=
            ...
            C(vs) => e
            ...
        for some expression e.
        Hence, reducing would result in
        e[vs -> as][ws -> bs].
        After defunctionalization, we get
        C'(as').d'(bs'),
        with as' and bs' being the recursively defunctionalized expression list as and bs,
        respectively, and C' and d' being the new corresponding constructor and cfun names,
        respectively.
        Additionally, we replace the gfun d by a new cfun
        cfun d(ws) : T :=
            ...
            C(vs) => e'
            ...
        with variable lists vs and ws as well as the expression e', which is the result of
        defunctionalizing e.
        Reducing the result would yield
        e'[vs -> as'][ws -> bs'],
        which, by the substition lemma defunc_substitution, is the result of defunctionalizing
        e[vs -> as][ws -> bs].
    Qed.

    ------------------------------------------------------------------------------------------------

    Lemma R3.0: Given a variable v, expressions expr and expr1 inside a program p where every local
        gfun is called at most once, we have
        inline_comatch expr[v -> expr1] = (inline_comatch expr)[v -> inline_comatch expr1],
        inline_comatch preserves substitution.
        Note: Since local gfuns are called at most once inside p, this means that it cannot both
        occur in expr and expr1.
    Proof.
        First, fix T to be the type of the gfuns to be inlined.
        Since inline_comatch is repeatedly inlining one comatch at a time, it suffices to consider
        one of these steps.
        We will perform an induction on the structure of expr.
        All cases except a local gfun call are once again congruence cases, which can be dealt with
        by induction.
        In the remaining case, we have a gfun call
        C(as)
        for some gfun C of T with body
        gfun C(vs) : T :=
            d_i(ws_i) => e_i
        Since there may at most one local gfun call for C, thus neither the body of C (i.e. all the
        expressions e_i) nor any of the expressions in as may contain a call to C.
        Now consider another expression e, which is also part of the program and thus may not
        contain a call to C.
        - Then substituting e for a variable v in the expression will result in
            C(as)[v -> e] = C(as[v -> e]).
            Performing inlining on this will result in 
            comatch C on T with vs:as'[v -> e'] with
                d_i(ws_i) => e_i',
            where as', e' and the e_i' are the results of inlining in the expression of as, in e
            and in the e_i, respectively (the e_i are also subject to inlining because inlining
            affects the whole program).
            However, since we know that there can be no gfun call to C in as, e or the e_i, this is
            the same as
            comatch C on T with vs:as[v -> e] with
                d_i(ws_i) => e_i.
        - After inlining in the original expression, we get
            comatch C on T with vs:as' with
                d_i(ws_i) => e_i',
            where as' and the e_i' are the results of inlining in the expression of as and in the
            e_i, respectively.
            However, since we know that there can be no gfun call to C in as, e or the e_i, this is
            the same as
            comatch C on T with vs:as with
                d_i(ws_i) => e_i.
            Performing inlining on e will be the identity, since by our prerequisites e may not
            contain a call to C.
            Performing substitution of e in the result of inlining the original expression, we get
            comatch C on T with vs:as[v -> e] with
                d_i(ws_i) => e_i.
            which is the same result as performing substitution and inlining in the reverse order.
    Qed.

    Lemma D3.0: Given a variable v, expressions expr and expr1 inside a program p where every local
        cfun is called at most once, we have
        inline_match expr[v -> expr1] = (inline_match expr)[v -> inline_match expr1],
        inline_match preserves substitution.
        Note: Since local cfuns are called at most once inside p, this means that it cannot both
        occur in expr and expr1.
    Proof.
        First, fix T to be the type of the cfuns to be inlined.
        Since inline_match is repeatedly inlining one match at a time, it suffices to consider one
        of these steps.
        We will perform an induction on the structure of expressions.
        All cases except a local cfun call are once again congruence cases, which can be dealt with
        by induction.
        In the remaining case, we have a gfun call
        ex.d(as)
        for some expression ex and some cfun d of T with body
        cfun T: d(vs) : T' :=
            C_i(ws_i) => e_i
        Since tfere may at most one local cfun call for d, thus neither the body of d (i.e. all the
        expressions e_i) nor ex or any of the expressions in as may contain a call to d.
        Now consider another expression e, which is also part of the program and thus may not
        contain a call to d.
        - Then substituting e for a variable v in the expression will result in
            ex.d(as)[v -> e] = ex[v -> e].d(as[v -> e]).
            Performing inlining on this will result in 
            match d on ex'[v -> e'] with vs:as'[v -> e'] with
                C_i(ws_i) => e_i',
            where as', e', ex' and the e_i' are the results of inlining in the expression of as, in
            e, in ex and in the e_i, respectively (the e_i are also subject to inlining because
            inlining affects the whole program).
            However, since we know that there can be no cfun call to d in as, e, ex or the e_i, this
            is the same as
            match d on ex[v -> e] with vs:as[v -> e] with
                C_i(ws_i) => e_i.
        - After inlining in the original expression, we get
            match d on ex' with vs:as' with
                C_i(ws_i) => e_i',
            where as', ex' and the e_i' are the results of inlining in the expression of as, in ex
            and in the e_i, respectively.
            However, since we know that there can be no cfun call to d in as, e, ex or the e_i, this
            is the same as
            match d on ex with vs:as with
                C_i(ws_i) => e_i.
            Performing inlining on e will be the identity, since by our prerequisites e may not
            contain a call to d.
            Performing substitution of e in the result of inlining the original expression, we get
            match d on ex[v -> e] with vs:as[v -> e] with
                C_i(ws_i) => e_i.
            which is the same result as performing substitution and inlining in the reverse order.
    Qed.

    Lemma R3.1: Given an expression expr, the result of (inline_comatch expr) will be a value iff
        expr is a value.
    Proof.
        First, fix T to be the type of the gfuns to be inlined.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        for some gfun C of type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction.
        In the remaining case, C(as) it is a value iff all expressions in as are values.
        The result of inlining C(as) will be
        comatch C on T using as' with
            ...,
        where as' is the result of recursively inlining in as (with added type annotations from the
        signature of the gfun C).
        This is a value iff all expressions in as' are values, which by induction is true iff all
        expressions in as are values, which is true iff C(as) is a value.
    Qed.

    Lemma D3.1: Given an expression expr, the result of (inline_match expr) will be a value iff
        expr is a value.
    Proof.
        First, fix T to be the type to be inlined.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        e.d(as)
        for some expression e of type T, a cfun d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction.
        In the remaining case, e.d(as) is not a value and the result of inlining is
        match d on e' using as' with
            ...,
        with e' the result of inlining in e and as' the result of recursively inlining in as (with
        added type annotations from the signature of the cfun d).
        This is also not a value, thus concluding the proof.
    Qed.

    Lemma R3.2: Given an expression expr, the result of (inline_comatch expr) will be a redex iff
        expr is a redex.
    Proof.
        First, fix T to be the type of the gfuns to be inlined.
        We will perform an induction on the structure of expr.
        If the input expression is not of the form
        C(as)
        or
        C(as).d(bs)
        for some local gfun C of type T, lists of expressions as and bs, and a destructor d on T,
        then this is a simple congruence case, which can immediately be resolved by induction.
          - In the first remaining case, C(as) is not a redex.
            The result of inlining C(as) will be
            comatch C on T using as' with
                ...,
            where as' is the result of recursively inlining in as (with added type annotations from
            the signature of the gfun C).
            This is also not a redex.
          - In the second remaining case, C(as).d(bs) is a redex.
            The result of inlining will be
            (comatch C on T using as' with
                ...).d(bs'),
            where as' and bs' are the result of recursively inlining in as (with added type
            annotations from the signature of the gfun C) and bs.
            This is also a redex.
    Qed.

    Lemma D3.2: Given an expression expr, the result of (inline_match expr) will be a redex iff
        expr is a redex.
    Proof.
        First, fix T to be the type to be inlined.
        We will perform an induction on the structure of expressions.
        If the input expression is not of the form
        e.d(as)
        for some expression e of type T, a local cfun d for type T and a list of expressions as,
        then this is a simple congruence case, which can immediately be resolved by induction and
        Lemma R3.1.
        In the remaining case, e.d(as) is a redex iff e and all expressions in as are values and the
        result of inlining is
        match d on e' using as' with
            ...,
        with e' the result of inlining in e and as' the result of recursively inlining in as (with
        added type annotations from the signature of the cfun d).
        This is a redex iff e' and all expressions in as' are values, which, by using Lemma R3.1 is
        true iff e and all expressions in as are values, which holds iff e.d(as) is a redex.
    Qed.

    Lemma R3.3 Given an expression expr,
        one_step_eval (inline_comatch expr) = inline_comatch (one_step_eval expr),
        i.e. inline_comatch preserves reduction.
    Proof.
        First, fix T to be the type of comatches to be inlined.
        We will perform an induction on the structure of expressions.
        Since, by Lemmas R3.1 and R3.2, inlining preserves values and redexes, we only
        need to consider the case of redexes which involve a destructor call on a local gfun on T
        where all arguments are already values, since all other cases are once again congruences
        that can immediately be handled by induction.
        In the remaining case, we have
        C(as).d(bs),
        where as and bs are lists of values, C and d are names of a local gfun and a destructor on
        T, respectively.
        Furthermore, we have a gfun
        gfun C(vs) : T :=
            ...
            d(ws) => e'
            ...
        for some expression e.
        Hence, reducing would result in
        e[vs -> as][ws -> bs].
        After inlining, we get
        (comatch C on T using vs:as' with
            ...
            d(ws) => e'
            ...).d(bs')
        with as' and bs' being the results of recursively inlining expression on lists as and bs,
        respectively, ws and vs being variable lists, and e' being the result of recursively
        inlining on e.
        Additionally, we remove the gfun C.
        Reducing the result would yield
        e'[vs -> as'][ws -> bs'],
        which, by the substition lemma R3.0, is the result of performing inlining on
        e[vs -> as][ws -> bs].
    Qed.

    Lemma D3.3 Given an expression expr,
        one_step_eval (inline_match expr) = inline_match (one_step_eval expr),
        i.e. inline_match preserves reduction.
    Proof.
        First, fix T to be the type of matches to be inlined.
        We will perform an induction on the structure of expressions.
        Since, by Lemmas D3.1 and D3.2, inlining preserves values and redexes, we only
        need to consider the case of redexes which involve a local cfun call on a constructor on T
        where all arguments are already values, since all other cases are once again congruences
        that can immediately be handled by induction.
        In the remaining case, we have
        C(as).d(bs),
        where as and bs are lists of values, C and d are names of a constructor and a local cfun on
        T, respectively.
        Furthermore, we have a cfun
        cfun T: d(ws) : T' :=
            ...
            C(vs) => e'
            ...
        for some expression e.
        Hence, reducing would result in
        e[vs -> as][ws -> bs].
        After inlining, we get
        match d on C(as') using vs:bs' with
            ...
            C(vs) => e'
            ...
        with as' and bs' being the results of recursively inlining expression on lists as and bs,
        respectively, ws and vs being variable lists, and e' being the result of recursively
        inlining on e.
        Additionally, we remove the cfun d.
        Reducing the result would yield
        e'[vs -> as'][ws -> bs'],
        which, by the substition lemma D3.0, is the result of performing inlining on
        e[vs -> as][ws -> bs].
    Qed.

*)
