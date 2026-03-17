(******************************************************************************)
(*                                                                            *)
(*          VST proof: int max(int a, int b)                                 *)
(*                                                                            *)
(*     Full semax_body proof for the max function.                           *)
(*     Generated Clight AST from deepspec/max.c via clightgen.               *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 19, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import max.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================== *)
(* Function specification                                              *)
(* ================================================================== *)

Definition max_spec :=
  DECLARE _max
  WITH a : Z, b : Z
  PRE [ tint, tint ]
    PROP (Int.min_signed <= a <= Int.max_signed;
          Int.min_signed <= b <= Int.max_signed)
    PARAMS (Vint (Int.repr a); Vint (Int.repr b))
    SEP ()
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.max a b)))
    SEP ().

Definition Gprog : funspecs := [max_spec].

(* ================================================================== *)
(* Body proof                                                          *)
(* ================================================================== *)

Lemma body_max : semax_body Vprog Gprog f_max max_spec.
Proof.
  start_function.
  forward_if.
  - (* a >= b branch *)
    forward.
    entailer!.
    f_equal. f_equal.
    rewrite Z.max_l; [reflexivity | lia].
  - (* b > a branch *)
    forward.
    entailer!.
    f_equal. f_equal.
    rewrite Z.max_r; [reflexivity | lia].
Qed.
