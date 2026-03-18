(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Validator Registry                    *)
(*                                                                            *)
(*     ValidatorEntry, ValidatorRegistry, registry_lookup,                   *)
(*     make_certificate.  For FFI bridging after extraction.                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 17, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Types.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Validator registries (for FFI bridging after extraction)              *)
(* ------------------------------------------------------------------ *)

(* A ValidatorEntry maps a tool identifier to a validator function.
   After extraction, the validator is an OCaml (string -> bool) that
   can call real crypto libraries.                                      *)
Record ValidatorEntry : Type := {
  ve_tool      : string;
  ve_validator : string -> bool;
}.

Definition ValidatorRegistry := list ValidatorEntry.

Fixpoint registry_lookup (tool : string) (reg : ValidatorRegistry)
  : option (string -> bool) :=
  match reg with
  | [] => None
  | entry :: rest =>
    if String.eqb entry.(ve_tool) tool
    then Some entry.(ve_validator)
    else registry_lookup tool rest
  end.

(* Build Certificate evidence from a registry lookup.                   *)
Definition make_certificate (tool blob : string) (reg : ValidatorRegistry)
  : option Evidence :=
  match registry_lookup tool reg with
  | Some v => Some (Certificate blob tool v)
  | None => None
  end.
