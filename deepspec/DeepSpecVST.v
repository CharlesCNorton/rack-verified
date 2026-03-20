(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: VST Case Study                       *)
(*                                                                            *)
(*     End-to-end: real VST semax_body proof -> ProofTerm evidence ->        *)
(*     WellFormed -> SupportTree.                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 19, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Core.
From RACK Require Import Main.
From RACK Require Import Reflect.
From RACK Require Import Notation.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import max.
Require Import verif_max.

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Arguments supportedby_children : simpl never.

(* The claim is the actual VST semax_body judgment. *)
Definition vst_max_claim : Prop :=
  semax_body Vprog Gprog f_max max_spec.

(* The proof is the real body_max from verif_max.v. *)
Definition vst_max_proof : vst_max_claim := body_max.

Definition ds_top : Node :=
  mkGoal "DS-top" "max(a,b) is correct: returns Z.max a b for signed ints"
    [("domain", MVString "integer arithmetic")]
    True.

Definition ds_strategy : Node :=
  mkStrategy "DS-strat" "Verified via VST separation logic over CompCert Clight"
    [("tool", MVString "VST");
     ("method", MVString "separation-logic")]
    True.

(* ProofTerm evidence carrying the real VST proof. *)
Definition ds_sol : Node := {|
  node_id         := "DS-vst";
  node_kind       := Solution;
  node_claim_text := "VST semax_body proof: body_max";
  node_evidence   := Some (ProofTerm "body_max"
                      vst_max_claim vst_max_proof
                      (Some (fun _ => true)));
  node_metadata   := [("tool", MVString "VST");
                       ("version", MVString "2.16");
                       ("method", MVString "separation-logic");
                       ("source", MVString "deepspec/max.c");
                       ("proof_file", MVString "deepspec/verif_max.vo");
                       ("timestamp", MVTimestamp "2026-03-19")];
  node_claim      := vst_max_claim;
|}.

Definition ds_ctx : Node :=
  mkContext "DS-ctx" "Target: CompCert 3.16 Clight, x86-64, signed 32-bit integers".

Definition ds_asm : Node :=
  mkAssumption "DS-asm" "CompCert compilation preserves verified properties".

Definition deepspec_vst_case : AssuranceCase :=
  mkCase "DS-top"
    [ds_top; ds_strategy; ds_sol; ds_ctx; ds_asm]
    [supports "DS-top" "DS-strat";
     supports "DS-strat" "DS-vst";
     in_context_of "DS-top" "DS-ctx";
     in_context_of "DS-strat" "DS-asm"].

Example deepspec_vst_structural :
  structural_checks deepspec_vst_case = true := eq_refl.

Definition deepspec_vst_wf : WellFormed deepspec_vst_case.
Proof. prove_well_formed_full. Qed.

Theorem deepspec_vst_supported : SupportTree deepspec_vst_case "DS-top".
Proof. exact (assurance_case_supported deepspec_vst_case deepspec_vst_wf). Qed.
