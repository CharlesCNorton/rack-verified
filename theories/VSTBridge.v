(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: VST / CompCert Bridge                *)
(*                                                                            *)
(*     Embeds Verified Software Toolchain Hoare triples as RACK evidence.    *)
(*     Requires coq-compcert >= 3.15 and coq-vst >= 2.16.                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 19, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Core.
From RACK Require Import Notation.

From compcert Require Import Clightdefs.
From compcert Require Import Ctypes.
From compcert Require Import Cop.
From compcert Require Import Clight.
From compcert Require Import AST.

From VST Require Import floyd.proofauto.
From VST Require Import floyd.library.

Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* VST claim embedding                                                 *)
(* ================================================================== *)

(** A [VSTSpec] packages a VST function specification in a form
    that RACK can consume.  The [vs_claim] field holds the
    [semax] judgment.  VST's [compspecs] and [OracleKind] are
    provided as section variables by the caller. *)
Record VSTSpec : Type := {
  vs_name   : string;            (* human-readable function name *)
  vs_claim  : Prop;              (* typically semax Delta Pre body Post *)
}.

Section VSTConstruction.

Context {CS : compspecs} {Espec : OracleKind}.

(** Build a [VSTSpec] from a [semax] judgment.  The caller must
    supply the compspecs and OracleKind (typically via Section
    variables or Instance declarations). *)
Definition mk_vst_spec (name : string)
    (Delta : tycontext) (Pre : environ -> mpred)
    (Post : ret_assert) (body : statement)
    (_ : @semax CS Espec Delta Pre body Post) : VSTSpec := {|
  vs_name  := name;
  vs_claim := @semax CS Espec Delta Pre body Post;
|}.

End VSTConstruction.

(* ================================================================== *)
(* RACK node construction from VST specs                               *)
(* ================================================================== *)

(** Build a RACK [Node] (Solution kind) whose [node_claim] is the
    VST [semax] judgment and whose evidence is a [ProofTerm] carrying
    the VST proof.  After extraction, the proof is erased; the label
    and claim text survive for audit. *)
Definition vst_solution (id : Id) (spec : VSTSpec)
    (pf : spec.(vs_claim)) : Node := {|
  node_id         := id;
  node_kind       := Solution;
  node_claim_text := "VST: " ++ spec.(vs_name);
  node_evidence   := Some (ProofTerm
                      ("vst:" ++ spec.(vs_name))
                      spec.(vs_claim) pf None);
  node_metadata   := [("tool", MVString "VST");
                       ("method", MVString "separation-logic")];
  node_claim      := spec.(vs_claim);
|}.

(** Build a RACK [Node] (Goal kind) whose claim is a VST [semax]
    judgment.  Used for top-level goals that are discharged by
    VST-verified children. *)
Definition vst_goal (id : Id) (text : string)
    (claim : Prop) : Node :=
  mkGoal id text [("tool", MVString "VST")] claim.

(* ================================================================== *)
(* CompCert compilation correctness                                    *)
(* ================================================================== *)

(** A [CompCertSpec] packages a CompCert compilation correctness
    claim: the compiled program preserves the semantics of the
    source program. *)
Record CompCertSpec : Type := {
  cc_name   : string;
  cc_source : Clight.program;
  cc_claim  : Prop;   (* typically: forward simulation / behavior refinement *)
}.

(** Build a RACK [Node] (Solution kind) whose evidence is a CompCert
    compilation correctness proof. *)
Definition compcert_solution (id : Id) (spec : CompCertSpec)
    (pf : spec.(cc_claim)) : Node := {|
  node_id         := id;
  node_kind       := Solution;
  node_claim_text := "CompCert: " ++ spec.(cc_name);
  node_evidence   := Some (ProofTerm
                      ("compcert:" ++ spec.(cc_name))
                      spec.(cc_claim) pf None);
  node_metadata   := [("tool", MVString "CompCert");
                       ("method", MVString "verified-compilation")];
  node_claim      := spec.(cc_claim);
|}.

(* ================================================================== *)
(* Evidence validity                                                   *)
(* ================================================================== *)

(** VST evidence is always valid: the [ProofTerm] carries a proof
    whose type IS the node's claim, so [evidence_valid] reduces to
    [P = P] which is [eq_refl]. *)
Lemma vst_evidence_valid : forall id spec pf,
    let n := vst_solution id spec pf in
    match n.(node_evidence) with
    | Some e => evidence_valid n e
    | None => False
    end.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma compcert_evidence_valid : forall id spec pf,
    let n := compcert_solution id spec pf in
    match n.(node_evidence) with
    | Some e => evidence_valid n e
    | None => False
    end.
Proof.
  intros. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Assurance case assembly helpers                                     *)
(* ================================================================== *)

(** Build a minimal assurance case: one goal supported by one
    VST-verified solution. *)
Definition vst_simple_case (goal_id sol_id : Id) (text : string)
    (spec : VSTSpec) (pf : spec.(vs_claim)) : AssuranceCase :=
  mkCase goal_id
    [vst_goal goal_id text spec.(vs_claim);
     vst_solution sol_id spec pf]
    [supports goal_id sol_id].
