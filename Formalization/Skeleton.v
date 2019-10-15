(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: Skeleton.v                                                                               *)
(*                                                                                                *)
(**************************************************************************************************)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Names.
Require Import Unique.

(**************************************************************************************************)
(** ** Program Skeleton                                                                           *)
(**************************************************************************************************)

(**************************************************************************************************)
(** *** Datatypes and Constructors                                                                *)
(**************************************************************************************************)
Definition dts := list TypeName.
Definition ctor : Type := ScopedName * list TypeName.
Definition ctors : Type := list ctor.

(** All Datataypes in CtorTable exist in datatypes.                                               *)
Definition dts_ctors_in_dts (d : dts) (ct : ctors) : Prop :=
  Forall  (fun x => In (fst (unscope (fst x) )) d) ct.

(** Scoped Names of Constructors are globally unique                                              *)
Definition dts_ctor_names_unique (ct : ctors) : Prop := unique (map fst ct).

(**************************************************************************************************)
(** *** Codatatypes and Destructors                                                               *)
(**************************************************************************************************)
Definition cdts := list TypeName.
Definition dtor : Type := ScopedName * list TypeName * TypeName.
Definition dtors := list dtor.

(** All Codatataypes in DtorTable exist in datatypes.                                             *)
Definition cdts_dtors_in_cdts (cd : cdts) (dt : dtors) : Prop :=
  Forall  (fun x => In (fst (unscope (fst (fst  x)))) cd) dt.

(** Scoped Names of Destructors are globally unique                                               *)
Definition cdts_dtor_names_unique (dt : dtors) : Prop := unique (map (fun x => fst (fst x)) dt).

(**************************************************************************************************)
(** *** Relation of data- and codatatypes                                                         *)
(**************************************************************************************************)

Definition dts_cdts_disjoint (d : dts) (cd : cdts) : Prop :=
    forall (t : TypeName), ~ (In t d /\ In t cd).

(**************************************************************************************************)
(** *** Ordinary Function Declarations                                                            *)
(**************************************************************************************************)
Definition fun_sig : Type := Name * list TypeName * TypeName.
Definition fun_sigs : Type := list fun_sig.

Definition fun_sigs_names_unique (fs : fun_sigs) : Prop := unique (map (fun x => fst (fst x)) fs).

(**************************************************************************************************)
(** *** Consumer Function Declarations                                                            *)
(**************************************************************************************************)
Definition cfun_sig : Type := QName * list TypeName * TypeName.
Definition cfun_sigs : Type := list cfun_sig.

Definition cfun_sigs_in_dts (d : dts) (mfs : cfun_sigs) : Prop :=
    Forall (fun x => In (fst (fst (fst x))) d) mfs.

Definition cfun_sigs_names_unique (mfs : cfun_sigs) : Prop := unique (map (fun x => fst (fst x)) mfs).

(**************************************************************************************************)
(** *** Generator Function Declarations                                                           *)
(**************************************************************************************************)
Definition gfun_sig : Type := QName * list TypeName.
Definition gfun_sigs : Type := list gfun_sig.

Definition gfun_sigs_in_cdts (cd : cdts) (cmfs : gfun_sigs) : Prop :=
    Forall (fun x => In (fst (fst x)) cd) cmfs.

Definition gfun_sigs_names_unique (cmfs : gfun_sigs) : Prop := unique (map fst cmfs).

(**************************************************************************************************)
(** *** Definition of Skeleton                                                                    *)
(**************************************************************************************************)

Record skeleton : Type :=
  mkSkeleton {
      (* Datatypes *)
      skeleton_dts : dts;
      skeleton_ctors : ctors;
      skeleton_dts_ctors_in_dts : dts_ctors_in_dts skeleton_dts skeleton_ctors;
      skeleton_dts_ctor_names_unique : dts_ctor_names_unique skeleton_ctors;
      (* Codatatypes *)
      skeleton_cdts : cdts;
      skeleton_dtors :  dtors;
      skeleton_cdts_dtors_in_cdts : cdts_dtors_in_cdts skeleton_cdts skeleton_dtors;
      skeleton_cdts_dtor_names_unique : cdts_dtor_names_unique skeleton_dtors;
      (* Datatypes + Codatatypes *)
      skeleton_dts_cdts_disjoint : dts_cdts_disjoint skeleton_dts skeleton_cdts;
      (* Ordinary Functions *)
      skeleton_fun_sigs : fun_sigs;
      skeleton_fun_sigs_names_unique : fun_sigs_names_unique skeleton_fun_sigs;
      (* Consumer functions *)
      skeleton_cfun_sigs_g : cfun_sigs;
      skeleton_cfun_sigs_in_dts_g : cfun_sigs_in_dts skeleton_dts skeleton_cfun_sigs_g;
      skeleton_cfun_sigs_names_unique_g : cfun_sigs_names_unique skeleton_cfun_sigs_g;
      skeleton_cfun_sigs_l : cfun_sigs;
      skeleton_cfun_sigs_in_dts_l : cfun_sigs_in_dts skeleton_dts skeleton_cfun_sigs_l;
      skeleton_cfun_sigs_names_unique_l : cfun_sigs_names_unique skeleton_cfun_sigs_l;
      (* Generator functions *)
      skeleton_gfun_sigs_g : gfun_sigs;
      skeleton_gfun_sigs_in_cdts_g : gfun_sigs_in_cdts skeleton_cdts skeleton_gfun_sigs_g;
      skeleton_gfun_sigs_names_unique_g : gfun_sigs_names_unique skeleton_gfun_sigs_g;
      skeleton_gfun_sigs_l : gfun_sigs;
      skeleton_gfun_sigs_in_cdts_l : gfun_sigs_in_cdts skeleton_cdts skeleton_gfun_sigs_l;
      skeleton_gfun_sigs_names_unique_l : gfun_sigs_names_unique skeleton_gfun_sigs_l;
    }.

(**************************************************************************************************)
(** *** The Empty ProgramSkeleton                                                                 *)
(**************************************************************************************************)

Definition emptySkeleton : skeleton :=
  {|
    (* Datatypes *)
    skeleton_dts := [];
    skeleton_ctors := [];
    skeleton_dts_ctors_in_dts := Forall_nil (fun x => In (fst (unscope (fst x))) []);
    skeleton_dts_ctor_names_unique := Unique_nil;
    (* Codatatypes *)
    skeleton_cdts := [];
    skeleton_dtors := [];
    skeleton_cdts_dtors_in_cdts := Forall_nil (fun x => In (fst (unscope (fst (fst x)))) []);
    skeleton_cdts_dtor_names_unique := Unique_nil;
    (* Datatypes + Codatatypes *)
    skeleton_dts_cdts_disjoint := fun _ => fun x => proj1 x;
    (* Ordinary functions *)
    skeleton_fun_sigs := [];
    skeleton_fun_sigs_names_unique := Unique_nil;
    (* Consumer functions *)
    skeleton_cfun_sigs_g := [];
    skeleton_cfun_sigs_in_dts_g := Forall_nil (fun x => In (fst (fst (fst x))) []);
    skeleton_cfun_sigs_names_unique_g := Unique_nil;
    skeleton_cfun_sigs_l := [];
    skeleton_cfun_sigs_in_dts_l := Forall_nil (fun x => In (fst (fst (fst x))) []);
    skeleton_cfun_sigs_names_unique_l := Unique_nil;
    (* Generator functions *)
    skeleton_gfun_sigs_g := [];
    skeleton_gfun_sigs_in_cdts_g := Forall_nil (fun x => In (fst (fst x)) []);
    skeleton_gfun_sigs_names_unique_g := Unique_nil;
    skeleton_gfun_sigs_l := [];
    skeleton_gfun_sigs_in_cdts_l := Forall_nil (fun x => In (fst (fst x)) []);
    skeleton_gfun_sigs_names_unique_l := Unique_nil
  |}.

(**************************************************************************************************)
(** *** The property of not having local gfuns and cfuns                                          *)
(**************************************************************************************************)

Definition no_gfun_l (s : skeleton) : Prop := (skeleton_gfun_sigs_l s) = [].

Definition no_cfun_l (s : skeleton) : Prop := (skeleton_cfun_sigs_l s) = [].

Definition no_cfun_gfun_l (s : skeleton) : Prop := no_gfun_l s /\ no_cfun_l s.

