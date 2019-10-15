(**************************************************************************************************)
(* Total De/Refunctionalization for Local (Co)pattern Matching.                                   *)
(*                                                                                                *)
(* File: Extraction.v                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)

From Coq Require Extraction.
Require Import Ascii.
Require Import String.

Require Import AST.
Require Import ProgramDef.
Require Import UtilsProgram.
Require Import Eval.
Require Import Typechecker.
Require Import TypecheckProgram.
Require Import LiftComatch.
Require Import InlineMatch.
Require Import LiftMatch.
Require Import InlineComatch.
Require Import RefuncIII.
Require Import DefuncIII.


Extraction Language Haskell.

(* Extraction of Inductive Datatypes into Haskell Datatypes *)
(* For more examples, see:
https://github.com/antalsz/hs-to-coq/blob/832e281e98685cd4d2914fb62a475476d1d86fa4/core-semantics-no-values/extraction.v *)

(* Bool and boolean functions *)
Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Constant andb        => "(Prelude.&&)".
Extract Constant orb         => "(Prelude.||)".
Extract Constant xorb        => "(Prelude./=)".
Extract Constant negb => "Prelude.not".

(* Maybe and related functions *)
Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(* natural numbers *)
Extract Inductive nat => "Prelude.Integer" ["(0 :: Prelude.Integer)" "(Prelude.+ 1)"]
"(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Constant pred  => "\x -> Prelude.max (x Prelude.- 1) 0".
Extract Constant plus  => "(Prelude.+)".
Extract Constant minus => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant mult  => "(Prelude.*)".
Extract Constant max   => "Prelude.max".
Extract Constant min => "Prelude.min".

(* Lists *)
Extract Inductive list => "[]" ["[]" "(:)"].
Extract Constant length  => "Data.List.genericLength".
Extract Constant app => "(Prelude.++)".

(* Product Type *)
Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive sigT2 => "(,,)" ["(,,)"].
Extract Constant prod_rect    => "Prelude.uncurry".
Extract Constant prod_uncurry => "Prelude.curry".
Extract Constant sigT_rect    => "Prelude.uncurry".
Extract Constant fst          => "Prelude.fst".
Extract Constant snd          => "Prelude.snd".
Extract Constant projT1       => "Prelude.fst".
Extract Constant projT2 => "Prelude.snd".

(* String Type *)
Extract Inductive ascii => "Prelude.Char"
  [ "(\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr ( (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+ (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+ (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+ (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+ (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+ (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+ (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+ (if b7 then Data.Bits.shiftL 1 7 else 0)))" ]
  "(\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))".
Extract Inlined Constant Ascii.ascii_dec => "(Prelude.==)".
Extract Inductive string => "Prelude.String" ["[]" "(:)"].
Extract Inlined Constant String.string_dec => "(Prelude.==)".



Separate Extraction
         (* Names *)
         Names.unscope
         (* AST *)
         AST.expr
         (* Skeleton *)
         Skeleton.skeleton
         Skeleton.skeleton_dts Skeleton.skeleton_ctors
         Skeleton.skeleton_cdts Skeleton.skeleton_dtors
         Skeleton.skeleton_fun_sigs
         Skeleton.skeleton_cfun_sigs_l Skeleton.skeleton_cfun_sigs_g
         Skeleton.skeleton_gfun_sigs_l Skeleton.skeleton_gfun_sigs_g
         (* Program *)
         ProgramDef.program
         ProgramDef.emptyProgram
         ProgramDef.program_skeleton
         ProgramDef.program_fun_bods
         ProgramDef.program_gfun_bods_g ProgramDef.program_gfun_bods_l
         ProgramDef.program_cfun_bods_g ProgramDef.program_cfun_bods_l
         (* Eval *)
         Eval.value_b Eval.one_step_eval
         (* Typechecker *)
         Typechecker.typecheck
         (* TypecheckProgram *)
         TypecheckProgram.typecheckProgram
         (* LiftComatch *)
         LiftComatch.lift_comatch_to_program
         (* InlineMatch *)
         InlineMatch.inline_cfuns_to_program
         InlineMatch.contains_no_local_cfun_call_b
         (* LiftMatch *)
         LiftMatch.lift_match_to_program
         (* InlineComatch *)
         InlineComatch.inline_gfuns_to_program
         InlineComatch.contains_no_local_gfun_call_b
         (* RefuncIII *)
         RefuncIII.refunctionalize_program
         (* DefuncIII *)
         DefuncIII.defunctionalize_program.

