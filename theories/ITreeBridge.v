(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Interaction Trees Bridge              *)
(*                                                                            *)
(*     Behavioral claims as predicates over interaction tree traces.          *)
(*     Evidence as simulation and refinement proofs.                          *)
(*     Requires coq-itree >= 5.1.                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 19, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Core.
From RACK Require Import Notation.

From ITree Require Import ITree.
From ITree Require Import ITreeFacts.
From ITree Require Import Events.State.

Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* Behavioral claims                                                   *)
(* ================================================================== *)

(** A behavioral claim is a predicate over an interaction tree.
    The event type [E] and return type [R] are parameters —
    instantiate them for your system's event vocabulary.

    Example: for a server, [E] might be [networkE +' stateE S]
    and [R] might be [unit].  A safety claim would be
    [forall t, spec_refines spec t -> no_double_response t]. *)

(** [BehavioralSpec E R] packages a reference specification ITree
    and the claim that the implementation refines it. *)
Record BehavioralSpec (E : Type -> Type) (R : Type) : Type := {
  bs_name : string;
  bs_spec : itree E R;           (* reference specification *)
  bs_impl : itree E R;           (* implementation *)
  bs_claim : Prop;               (* refinement/simulation claim *)
}.

Arguments bs_name {E R}.
Arguments bs_spec {E R}.
Arguments bs_impl {E R}.
Arguments bs_claim {E R}.

(** Build a behavioral spec from an [eutt] equivalence claim.
    [eutt] (equivalence up to taus) is the standard ITree
    bisimulation: two ITrees are equivalent when they produce
    the same observable events in the same order. *)
Definition mk_behavioral_eutt {E : Type -> Type} {R : Type}
    (name : string)
    (spec impl : itree E R) : BehavioralSpec E R := {|
  bs_name  := name;
  bs_spec  := spec;
  bs_impl  := impl;
  bs_claim := eutt eq spec impl;
|}.

(** Build a behavioral spec from a custom refinement relation. *)
Definition mk_behavioral_custom {E : Type -> Type} {R : Type}
    (name : string) (spec impl : itree E R)
    (claim : Prop) : BehavioralSpec E R := {|
  bs_name  := name;
  bs_spec  := spec;
  bs_impl  := impl;
  bs_claim := claim;
|}.

(* ================================================================== *)
(* RACK node construction from behavioral specs                        *)
(* ================================================================== *)

(** Build a RACK Solution node whose claim is a behavioral
    refinement and whose evidence is the refinement proof. *)
Definition itree_solution {E : Type -> Type} {R : Type}
    (id : Id) (spec : BehavioralSpec E R)
    (pf : spec.(bs_claim)) : Node := {|
  node_id         := id;
  node_kind       := Solution;
  node_claim_text := "Behavioral: " ++ spec.(bs_name);
  node_evidence   := Some (ProofTerm
                      ("itree:" ++ spec.(bs_name))
                      spec.(bs_claim) pf None);
  node_metadata   := [("tool", MVString "ITree");
                       ("method", MVString "behavioral-refinement")];
  node_claim      := spec.(bs_claim);
|}.

(** Build a RACK Goal node for a behavioral property. *)
Definition itree_goal (id : Id) (text : string)
    (claim : Prop) : Node :=
  mkGoal id text [("method", MVString "behavioral")] claim.

(* ================================================================== *)
(* Evidence validity                                                   *)
(* ================================================================== *)

Lemma itree_evidence_valid : forall E R id (spec : BehavioralSpec E R) pf,
    let n := itree_solution id spec pf in
    match n.(node_evidence) with
    | Some e => evidence_valid n e
    | None => False
    end.
Proof.
  intros. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* Trace predicates                                                    *)
(* ================================================================== *)

(** A safety property: the ITree never triggers a "bad" event.
    [bad : forall T, E T -> Prop] classifies which events are bad. *)
Definition safe_trace {E : Type -> Type} {R : Type}
    (bad : forall T, E T -> Prop)
    (t : itree E R) : Prop :=
  forall T (e : E T), ~ bad T e.
  (* Full version would walk the tree coinductively;
     this is a placeholder for the structural pattern. *)

(** A liveness property: the ITree eventually produces a result. *)
Definition terminates {E : Type -> Type} {R : Type}
    (t : itree E R) : Prop :=
  exists r, eutt eq t (Ret r).

(* ================================================================== *)
(* Assurance case assembly                                             *)
(* ================================================================== *)

(** Build a minimal assurance case: one behavioral goal supported
    by one ITree-verified solution. *)
Definition itree_simple_case {E : Type -> Type} {R : Type}
    (goal_id sol_id : Id) (text : string)
    (spec : BehavioralSpec E R) (pf : spec.(bs_claim))
    : AssuranceCase :=
  mkCase goal_id
    [itree_goal goal_id text spec.(bs_claim);
     itree_solution sol_id spec pf]
    [supports goal_id sol_id].
