(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: ProgramDef.v                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.

(* Require Import Typechecker.*)
Require Import Names.
Require Import Skeleton.
Require Import AST.
Require Import Unique.
Require Import BodyTypeDefs.
Require Import Typechecker.

(**************************************************************************************************)
(** * Function bodies                                                                             *)
(**************************************************************************************************)

Definition has_all_fun_bods (sigs : fun_sigs) (bodies : fun_bods) :=
  map (fun x => fst (fst x)) sigs = map fst bodies.

(**************************************************************************************************)
(** * Generator function bodies                                                                   *)
(**************************************************************************************************)

Definition has_all_gfun_bods (sigs : gfun_sigs) (bodies : gfun_bods) :=
  map fst sigs = map fst bodies.

(**************************************************************************************************)
(** * Consumer function bodies                                                                    *)
(**************************************************************************************************)

Definition has_all_cfun_bods (sigs : cfun_sigs) (bodies : cfun_bods) :=
  map (fun x => fst (fst x)) sigs = map fst bodies.

Fixpoint collect_comatch_names (e : expr) : list QName :=
  match e with
  | E_Var x => []
  | E_Constr _ x0 => List.concat (List.map collect_comatch_names x0)
  | E_DestrCall _ x0 x1 => List.concat (List.map collect_comatch_names (x0 :: x1))
  | E_FunCall _ x => List.concat (List.map collect_comatch_names x)
  | E_GenFunCall _ x0 => List.concat (List.map collect_comatch_names x0)
  | E_ConsFunCall x x0 x1 => List.concat (List.map collect_comatch_names (x0 :: x1))
  | E_Match _ x0 x2 x3 _ => let bs_names := List.map (fun x => collect_comatch_names ( fst x)) x2 in
                               let case_names := List.map (fun x => collect_comatch_names (snd x)) x3 in
                               (collect_comatch_names x0) ++ List.concat (bs_names ++ case_names)
  | E_CoMatch x  x1 x2 => let bs_names := List.map (fun x => collect_comatch_names (fst x)) x1 in
                           let case_names := List.map (fun x => collect_comatch_names (snd x)) x2 in
                           x :: (List.concat (bs_names ++  case_names))
  | E_Let x x0 => (collect_comatch_names x) ++ (collect_comatch_names x0)
  end.

Fixpoint collect_match_names (e : expr) : list QName :=
  match e with
  | E_Var x => []
  | E_Constr _ x0 => List.concat (List.map collect_match_names x0)
  | E_DestrCall _ x0 x1 => List.concat (List.map collect_match_names (x0 :: x1))
  | E_FunCall _ x => List.concat (List.map collect_match_names x)
  | E_GenFunCall _ x0 => List.concat (List.map collect_match_names x0)
  | E_ConsFunCall _ x0 x1 => List.concat (List.map collect_match_names (x0 :: x1))
  | E_Match x x0  x2 x3 _ => let bs_names := List.map (fun x => collect_match_names ( fst x)) x2 in
                               let case_names := List.map (fun x => collect_match_names (snd x)) x3 in
                               x :: ((collect_match_names x0) ++ List.concat (bs_names ++ case_names))
  | E_CoMatch _  x1 x2 => let bs_names := List.map (fun x => collect_match_names (fst x)) x1 in
                           let case_names := List.map (fun x => collect_match_names (snd x)) x2 in
                           (List.concat (bs_names ++  case_names))
  | E_Let x x0 => (collect_match_names x) ++ (collect_match_names x0)
  end.

Definition comatch_names_unique (fbt : fun_bods) (mfbt : cfun_bods) (cmfbt : gfun_bods) : Prop :=
  let fbodies : list expr := List.map snd fbt in
  let mfbodies : list expr := List.map snd (List.concat (List.map snd mfbt)) in
  let cmfbodies := List.map snd (List.concat (List.map snd cmfbt)) in
  unique (List.concat (List.map collect_comatch_names (fbodies ++ mfbodies ++ cmfbodies))).

Definition match_names_unique (fbt : fun_bods) (mfbt : cfun_bods) (cmfbt : gfun_bods) : Prop :=
  let fbodies : list expr := List.map snd fbt in
  let mfbodies : list expr := List.map snd (List.concat (List.map snd mfbt)) in
  let cmfbodies := List.map snd (List.concat (List.map snd cmfbt)) in
  unique (List.concat (List.map collect_match_names (fbodies ++ mfbodies ++ cmfbodies))).

(**************************************************************************************************)
(** *** Definition of Program                                                                     *)
(**************************************************************************************************)

Record program : Type :=
  mkProgram {
      (* Skeleton *)
      program_skeleton : skeleton;
      (* Ordinary functions *)
      program_fun_bods : fun_bods;
      program_has_all_fun_bods : has_all_fun_bods (skeleton_fun_sigs program_skeleton) program_fun_bods;
      program_fun_bods_typecheck : fun_bods_typecheck program_skeleton program_fun_bods;
      (* Consumer functions *)
      program_cfun_bods_g : cfun_bods;
      program_has_all_cfun_bods_g : has_all_cfun_bods (skeleton_cfun_sigs_g program_skeleton) program_cfun_bods_g;
      program_cfun_bods_typecheck_g : cfun_bods_g_typecheck program_skeleton program_cfun_bods_g;
      program_cfun_bods_l : cfun_bods;
      program_has_all_cfun_bods_l : has_all_cfun_bods (skeleton_cfun_sigs_l program_skeleton) program_cfun_bods_l;
      program_cfun_bods_typecheck_l : cfun_bods_l_typecheck program_skeleton program_cfun_bods_l;
      (* Generator functions *)
      program_gfun_bods_g : gfun_bods;
      program_has_all_gfun_bods_g : has_all_gfun_bods (skeleton_gfun_sigs_g program_skeleton) program_gfun_bods_g;
      program_gfun_bods_typecheck_g : gfun_bods_g_typecheck program_skeleton program_gfun_bods_g;
      program_gfun_bods_l : gfun_bods;
      program_has_all_gfun_bods_l : has_all_gfun_bods (skeleton_gfun_sigs_l program_skeleton) program_gfun_bods_l;
      program_gfun_bods_typecheck_l : gfun_bods_l_typecheck program_skeleton program_gfun_bods_l;
      (* Uniqueness conditions *)
      program_match_names_unique : match_names_unique program_fun_bods
                                                      (program_cfun_bods_g ++ program_cfun_bods_l)
                                                      (program_gfun_bods_g ++ program_gfun_bods_l);
      program_comatch_names_unique : comatch_names_unique program_fun_bods
                                                          (program_cfun_bods_g ++ program_cfun_bods_l)
                                                          (program_gfun_bods_g ++ program_gfun_bods_l);
    }.

(**************************************************************************************************)
(** *** The Empty Program                                                                         *)
(**************************************************************************************************)

Definition no_fun_bods : fun_bods_typecheck emptySkeleton [].
  apply Forall_nil. Qed.
Definition no_cfun_bods_g : cfun_bods_g_typecheck emptySkeleton [].
  apply Forall_nil. Qed.
Definition no_cfun_bods_l : cfun_bods_l_typecheck emptySkeleton [].
  apply Forall_nil. Qed.
Definition no_gfun_bods_g : gfun_bods_g_typecheck emptySkeleton [].
  apply Forall_nil. Qed.
Definition no_gfun_bods_l : gfun_bods_l_typecheck emptySkeleton [].
  apply Forall_nil. Qed.
Definition emptyprog_match_names_unique : match_names_unique [] [] [].
  apply Unique_nil. Qed.
Definition emptyprog_comatch_names_unique : comatch_names_unique [] [] [].
  apply Unique_nil. Qed.
Definition emptyProgram :=
  {|
    program_skeleton := emptySkeleton;
    program_fun_bods := [];
    program_cfun_bods_g := [];
    program_gfun_bods_g := [];
    program_cfun_bods_l := [];
    program_gfun_bods_l := [];
    program_has_all_fun_bods := eq_refl [];
    program_has_all_cfun_bods_g := eq_refl [];
    program_has_all_cfun_bods_l := eq_refl [];
    program_has_all_gfun_bods_g := eq_refl [];
    program_has_all_gfun_bods_l := eq_refl [];
    program_match_names_unique := emptyprog_match_names_unique;
    program_comatch_names_unique := emptyprog_comatch_names_unique;
    program_fun_bods_typecheck := no_fun_bods;
    program_cfun_bods_typecheck_g := no_cfun_bods_g;
    program_cfun_bods_typecheck_l := no_cfun_bods_l;
    program_gfun_bods_typecheck_g := no_gfun_bods_g;
    program_gfun_bods_typecheck_l := no_gfun_bods_l;
  |}.
