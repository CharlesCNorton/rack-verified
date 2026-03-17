(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: CONOPS with ITree Claims             *)
(*                                                                            *)
(*     Extends the CONOPS compiler to produce behavioral claims as           *)
(*     ITree trace predicates instead of node_claim := True.                 *)
(*                                                                            *)
(*     The compiler is parameterized by a claim interpreter that maps        *)
(*     requirement text to ITree behavioral specifications.                  *)
(*                                                                            *)
(*     Build: make deepspec                                                   *)
(*     Requires: coq-itree >= 5.1                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 19, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Core.
From RACK Require Import Trace.
From RACK Require Import Notation.
From RACK Require Import Conops.
From RACK Require Import ITreeBridge.

From ITree Require Import ITree.
From ITree Require Import ITreeFacts.
From ITree Require Import Eq.Eqit.

Import ITreeNotations.
Open Scope itree_scope.

Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* Claim interpreter                                                   *)
(*                                                                     *)
(* A claim interpreter maps requirement IDs to behavioral claims.     *)
(* The domain engineer provides this; the CONOPS compiler uses it.    *)
(* ================================================================== *)

(** A [ClaimInterp] maps requirement IDs to propositions.
    Requirements not in the interpreter get [True] (unspecified). *)
Definition ClaimInterp := string -> Prop.

Definition default_interp : ClaimInterp := fun _ => True.

(** Look up a claim, defaulting to [True]. *)
Definition interp_claim (interp : ClaimInterp) (req_id : string) : Prop :=
  interp req_id.

(* ================================================================== *)
(* Parameterized CONOPS compiler                                       *)
(* ================================================================== *)

(** Compile a requirement to a Goal node with a real claim
    from the interpreter, instead of [True]. *)
Definition compile_requirement_interp (interp : ClaimInterp)
    (cr : ConopsRequirement) : Node :=
  mkGoal cr.(cr_id) cr.(cr_text)
    [md_string "rationale" cr.(cr_rationale);
     md_string "priority" cr.(cr_priority);
     md_string "source" "CONOPS"]
    (interp_claim interp cr.(cr_id)).

Definition compile_section_interp (interp : ClaimInterp)
    (sec : ConopsSection) : list Node :=
  map (compile_requirement_interp interp) sec.(csec_requirements) ++
  map compile_assumption sec.(csec_assumptions) ++
  map compile_constraint sec.(csec_constraints).

Definition compile_document_nodes_interp (interp : ClaimInterp)
    (doc : ConopsDocument) : list Node :=
  flat_map (compile_section_interp interp) doc.(cd_sections).

(** Full CONOPS compiler with interpreted claims. *)
Definition compile_conops_interp (interp : ClaimInterp)
    (doc : ConopsDocument) (top_id : Id)
    : AssuranceCase * list TraceLink :=
  let top_claim := fold_right and True
    (map (fun sec =>
      fold_right and True
        (map (fun cr => interp_claim interp cr.(cr_id))
             sec.(csec_requirements)))
      doc.(cd_sections)) in
  let top := mkGoal top_id doc.(cd_title)
    [md_string "source" "CONOPS"] top_claim in
  let section_nodes := compile_document_nodes_interp interp doc in
  let req_ids := flat_map (fun sec =>
    map cr_id sec.(csec_requirements)) doc.(cd_sections) in
  let asm_ids := flat_map (fun sec =>
    map ca_id sec.(csec_assumptions)) doc.(cd_sections) in
  let support_links := map (supports top_id) req_ids in
  let context_links := map (in_context_of top_id) asm_ids in
  let ac := mkCase top_id
    (top :: section_nodes)
    (support_links ++ context_links) in
  let traces := compile_document_traces doc in
  (ac, traces).

(* ================================================================== *)
(* Preservation lemmas                                                 *)
(* ================================================================== *)

Lemma compile_requirement_interp_is_goal : forall interp cr,
    (compile_requirement_interp interp cr).(node_kind) = Goal.
Proof. reflexivity. Qed.

Lemma compile_requirement_interp_id : forall interp cr,
    (compile_requirement_interp interp cr).(node_id) = cr.(cr_id).
Proof. reflexivity. Qed.

Lemma compile_requirement_interp_claim : forall interp cr,
    (compile_requirement_interp interp cr).(node_claim) =
    interp_claim interp cr.(cr_id).
Proof. reflexivity. Qed.

Lemma compiled_interp_reqs_in_nodes : forall interp doc top_id cr sec,
    In sec doc.(cd_sections) ->
    In cr sec.(csec_requirements) ->
    In (compile_requirement_interp interp cr)
       (fst (compile_conops_interp interp doc top_id)).(ac_nodes).
Proof.
  intros interp doc top_id cr sec Hsec Hcr.
  unfold compile_conops_interp. simpl.
  right. unfold compile_document_nodes_interp.
  apply in_flat_map. exists sec. split; [exact Hsec |].
  unfold compile_section_interp. apply in_or_app. left.
  apply in_map. exact Hcr.
Qed.

(* ================================================================== *)
(* ITree-specific claim interpreter                                    *)
(* ================================================================== *)

Section ITreeInterp.

Context {E : Type -> Type} {R : Type}.

(** Build a [ClaimInterp] from a list of (req_id, behavioral_spec)
    pairs.  Requirements not in the list get [True]. *)
Fixpoint itree_interp_from_list
    (specs : list (string * BehavioralSpec E R))
    (req_id : string) : Prop :=
  match specs with
  | [] => True
  | (id, spec) :: rest =>
    if String.eqb id req_id then spec.(bs_claim)
    else itree_interp_from_list rest req_id
  end.

(** Convenience: build a claim interpreter and compile in one step. *)
Definition compile_conops_itree
    (specs : list (string * BehavioralSpec E R))
    (doc : ConopsDocument) (top_id : Id)
    : AssuranceCase * list TraceLink :=
  compile_conops_interp (itree_interp_from_list specs) doc top_id.

End ITreeInterp.

(* ================================================================== *)
(* Example: CONOPS with behavioral claims                              *)
(* ================================================================== *)

Inductive sysE : Type -> Type :=
  | Operate : sysE unit
  | CheckSafe : sysE bool.

Definition safety_spec : itree sysE bool :=
  trigger Operate;; trigger CheckSafe.

Definition safety_impl : itree sysE bool :=
  trigger Operate;; trigger CheckSafe.

Definition safety_refines : eutt eq safety_spec safety_impl.
Proof. reflexivity. Qed.

Definition safety_bspec : BehavioralSpec sysE bool :=
  mk_behavioral_eutt "safety_refines" safety_spec safety_impl.

Definition example_req : ConopsRequirement := {|
  cr_id := "REQ-SAFE-01";
  cr_text := "The system shall not cause harm to operators";
  cr_rationale := "Operator safety is the primary design constraint";
  cr_priority := "critical";
|}.

Definition example_section : ConopsSection := {|
  csec_title := "Safety";
  csec_requirements := [example_req];
  csec_assumptions := [];
  csec_constraints := [];
|}.

Definition example_doc : ConopsDocument := {|
  cd_title := "System safety";
  cd_version := "1.0";
  cd_sections := [example_section];
  cd_scenarios := [];
|}.

Definition example_specs : list (string * BehavioralSpec sysE bool) :=
  [("REQ-SAFE-01", safety_bspec)].

Definition example_compiled :=
  fst (compile_conops_itree example_specs example_doc "TOP").

(** The compiled requirement node carries the ITree behavioral
    claim, not [True]. *)
Lemma example_req_claim :
  exists n, In n example_compiled.(ac_nodes) /\
    n.(node_id) = "REQ-SAFE-01" /\
    n.(node_claim) = eutt eq safety_spec safety_impl.
Proof.
  eexists. split; [| split].
  - right. left. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
