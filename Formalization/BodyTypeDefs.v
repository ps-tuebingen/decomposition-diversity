Require Import AST.
Require Import Names.

(**************************************************************************************************)
(** * Function bodies                                                                             *)
(**************************************************************************************************)

Definition fun_bod : Type := expr.
Definition fun_bod_named : Type := Name * fun_bod.
Definition fun_bods : Type := list fun_bod_named.

(**************************************************************************************************)
(** * Generator function bodies                                                                   *)
(**************************************************************************************************)

Definition gfun_bod : Type := list (ScopedName * expr).
Definition gfun_bod_named : Type := QName * gfun_bod.
Definition gfun_bods : Type := list gfun_bod_named.

(**************************************************************************************************)
(** * Consumer function bodies                                                                    *)
(**************************************************************************************************)

Definition cfun_bod : Type := list (ScopedName * expr).
Definition cfun_bod_named : Type := QName * cfun_bod.
Definition cfun_bods : Type := list cfun_bod_named.

