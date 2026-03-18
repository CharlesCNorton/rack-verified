(* ------------------------------------------------------------------ *)
(* Ergonomic notations and scope for assurance-case construction       *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* Node builders                                                       *)
(* ------------------------------------------------------------------ *)

(** Smart constructors for concise case definitions.  Each builder
    takes the minimal required fields; optional fields default to
    [None] / [nil].  For [Solution] the caller must supply evidence;
    for [Goal] and [Strategy] the claim is mandatory.  The [node_claim]
    field defaults to [True]; override it when you need entailment
    proofs over non-trivial propositions. *)

Definition mkGoal (id : Id) (text : string)
    (md : list (string * MetadataValue)) (claim : Prop) : Node := {|
  node_id         := id;
  node_kind       := Goal;
  node_claim_text := text;
  node_evidence   := None;
  node_metadata   := md;
  node_claim      := claim;
|}.

Definition mkStrategy (id : Id) (text : string)
    (md : list (string * MetadataValue)) (claim : Prop) : Node := {|
  node_id         := id;
  node_kind       := Strategy;
  node_claim_text := text;
  node_evidence   := None;
  node_metadata   := md;
  node_claim      := claim;
|}.

Definition mkSolution (id : Id) (text : string)
    (ev : Evidence)
    (md : list (string * MetadataValue)) (claim : Prop) : Node := {|
  node_id         := id;
  node_kind       := Solution;
  node_claim_text := text;
  node_evidence   := Some ev;
  node_metadata   := md;
  node_claim      := claim;
|}.

Definition mkContext (id : Id) (text : string) : Node := {|
  node_id         := id;
  node_kind       := Context;
  node_claim_text := text;
  node_evidence   := None;
  node_metadata   := nil;
  node_claim      := True;
|}.

Definition mkAssumption (id : Id) (text : string) : Node := {|
  node_id         := id;
  node_kind       := Assumption;
  node_claim_text := text;
  node_evidence   := None;
  node_metadata   := nil;
  node_claim      := True;
|}.

Definition mkJustification (id : Id) (text : string) : Node := {|
  node_id         := id;
  node_kind       := Justification;
  node_claim_text := text;
  node_evidence   := None;
  node_metadata   := nil;
  node_claim      := True;
|}.

(* ------------------------------------------------------------------ *)
(* Link builders                                                       *)
(* ------------------------------------------------------------------ *)

Definition supports (from to_ : Id) : Link := {|
  link_kind := SupportedBy;
  link_from := from;
  link_to   := to_;
|}.

Definition in_context_of (from to_ : Id) : Link := {|
  link_kind := InContextOf;
  link_from := from;
  link_to   := to_;
|}.

(* ------------------------------------------------------------------ *)
(* Evidence builders                                                   *)
(* ------------------------------------------------------------------ *)

(** Build a [ProofTerm] evidence from a label and proof.
    The runtime re-checker defaults to [None]. *)
Definition proof_evidence (label : string) (P : Prop) (pf : P) : Evidence :=
  ProofTerm label P pf None.

(** Build a [ProofTerm] with a runtime re-checker thunk. *)
Definition proof_evidence_rt (label : string) (P : Prop) (pf : P)
    (check : unit -> bool) : Evidence :=
  ProofTerm label P pf (Some check).

(** Build a [Certificate] evidence from blob, tool, and validator. *)
Definition cert_evidence (blob tool : string)
    (validator : string -> bool) : Evidence :=
  Certificate blob tool validator.

(* ------------------------------------------------------------------ *)
(* AssuranceCase builder                                                *)
(* ------------------------------------------------------------------ *)

Definition mkCase (top : Id) (nodes : list Node)
    (links : list Link) : AssuranceCase := {|
  ac_nodes := nodes;
  ac_links := links;
  ac_top   := top;
|}.

(* ------------------------------------------------------------------ *)
(* Metadata builders                                                   *)
(* ------------------------------------------------------------------ *)

Definition md_string (k v : string) : string * MetadataValue :=
  (k, MVString v).

Definition md_nat (k : string) (v : nat) : string * MetadataValue :=
  (k, MVNat v).

Definition md_bool (k : string) (v : bool) : string * MetadataValue :=
  (k, MVBool v).

Definition md_timestamp (k v : string) : string * MetadataValue :=
  (k, MVTimestamp v).
