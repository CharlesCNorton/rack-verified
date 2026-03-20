(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Graph Operations                      *)
(*                                                                            *)
(*     find_node, supportedby_children, build_node_index,                    *)
(*     find_node_indexed, Reaches, Acyclic, evidence helpers,                *)
(*     metadata helpers, undeveloped/assumption lifecycle.                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 17, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Types.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* Graph operations                                                     *)
(* ------------------------------------------------------------------ *)

(* O(n) linear scan.  For repeated lookups on large graphs, see
   build_node_index / find_node_indexed below.                        *)
Definition find_node (ac : AssuranceCase) (id : Id) : option Node :=
  find (fun n => String.eqb n.(node_id) id) ac.(ac_nodes).

Definition supportedby_children (ac : AssuranceCase) (id : Id) : list Id :=
  map link_to
    (filter (fun l => andb
               (String.eqb l.(link_from) id)
               (match l.(link_kind) with SupportedBy => true | _ => false end))
            ac.(ac_links)).

(* ------------------------------------------------------------------ *)
(* Indexed node lookup                                                  *)
(* ------------------------------------------------------------------ *)

(* Precomputed association-list index.  Build once, then use
   find_node_indexed for lookups.  Still O(n) worst case per
   lookup but avoids the predicate overhead of find.
   For O(log n), plug in a balanced map type.                          *)
Definition build_node_index (ac : AssuranceCase) : list (Id * Node) :=
  map (fun n => (n.(node_id), n)) ac.(ac_nodes).

Fixpoint assoc_find (id : Id) (idx : list (Id * Node)) : option Node :=
  match idx with
  | [] => None
  | (k, v) :: rest =>
    if String.eqb k id then Some v
    else assoc_find id rest
  end.

Definition find_node_indexed (idx : list (Id * Node))
    (id : Id) : option Node :=
  assoc_find id idx.

Lemma find_node_indexed_correct : forall ac id,
    find_node_indexed (build_node_index ac) id = find_node ac id.
Proof.
  intros ac id. unfold find_node_indexed, build_node_index, find_node.
  induction ac.(ac_nodes) as [|n ns IH]; simpl.
  - reflexivity.
  - destruct (String.eqb n.(node_id) id); [reflexivity | exact IH].
Qed.

(* ------------------------------------------------------------------ *)
(* Reachability and acyclicity                                          *)
(* ------------------------------------------------------------------ *)

Inductive Reaches (ac : AssuranceCase) : Id -> Id -> Prop :=
  | R_Step  : forall u v,
      In v (supportedby_children ac u) -> Reaches ac u v
  | R_Trans : forall u w v,
      Reaches ac u w -> Reaches ac w v -> Reaches ac u v.

Definition Acyclic (ac : AssuranceCase) : Prop :=
  forall id, ~ Reaches ac id id.

(* ------------------------------------------------------------------ *)
(* Evidence validity                                                    *)
(* ------------------------------------------------------------------ *)

Definition evidence_valid (n : Node) (e : Evidence) : Prop :=
  match e with
  | ProofTerm _ P _ _ => P = n.(node_claim)
  | Certificate b _ v => v b = true
  end.

(* After extraction, ProofTerm's Prop and proof witness are erased;
   only this label survives to identify which theorem was proved.
   Certificate evidence returns the raw blob payload.
   Use this for audit trails and inspectable witness trees.            *)
Definition evidence_label (e : Evidence) : string :=
  match e with
  | ProofTerm lbl _ _ _ => lbl
  | Certificate blob _ _ => blob
  end.

(* Runtime re-check: call the optional re-checker if present.
   For ProofTerm, [claim_text] is the node's claim text — the re-checker
   verifies that the evidence is still bound to the correct node.
   Returns true for ProofTerm without a runtime checker (trust the type
   system), true for Certificate if the validator passes, false otherwise.
   Survives extraction — use this in CI gates and audit tooling.           *)
Definition evidence_runtime_check (claim_text : string) (e : Evidence) : bool :=
  match e with
  | ProofTerm _ _ _ (Some f) => f claim_text
  | ProofTerm _ _ _ None     => true
  | Certificate b _ v        => v b
  end.

(* Tool identifier for external evidence.
   Returns EmptyString for ProofTerm (Rocq itself is the "tool").        *)
Definition evidence_tool (e : Evidence) : string :=
  match e with
  | ProofTerm _ _ _ _  => EmptyString
  | Certificate _ t _  => t
  end.

(* ------------------------------------------------------------------ *)
(* Metadata helpers                                                      *)
(* ------------------------------------------------------------------ *)

Fixpoint find_metadata (key : string) (md : list (string * MetadataValue))
  : option MetadataValue :=
  match md with
  | [] => None
  | (k, v) :: rest =>
    if String.eqb k key then Some v
    else find_metadata key rest
  end.

Definition has_metadata_key (key : string) (md : list (string * MetadataValue))
  : bool :=
  match find_metadata key md with Some _ => true | None => false end.

(** Convenience accessors — extract string content, accepting
    both [MVTimestamp] and [MVString] for timestamp fields, etc. *)
Definition node_timestamp (n : Node) : option string :=
  match find_metadata "timestamp" n.(node_metadata) with
  | Some (MVTimestamp s) => Some s
  | Some (MVString s)    => Some s
  | _                    => None
  end.

Definition node_confidence (n : Node) : option string :=
  match find_metadata "confidence" n.(node_metadata) with
  | Some (MVString s) => Some s
  | _                 => None
  end.

Definition node_weight (n : Node) : option string :=
  match find_metadata "weight" n.(node_metadata) with
  | Some (MVString s) => Some s
  | _                 => None
  end.

(* ------------------------------------------------------------------ *)
(* Undeveloped nodes                                                    *)
(* ------------------------------------------------------------------ *)

(** A node is undeveloped when its metadata contains [("undeveloped", MVBool true)].
    Undeveloped nodes are skipped by discharged checks, allowing
    partial cases to validate without false positives. *)
Definition node_undeveloped (n : Node) : bool :=
  match find_metadata "undeveloped" n.(node_metadata) with
  | Some (MVBool true) => true
  | _ => false
  end.

Definition all_developed (ac : AssuranceCase) : bool :=
  forallb (fun n => negb (node_undeveloped n)) ac.(ac_nodes).

(* ------------------------------------------------------------------ *)
(* Assumption lifecycle                                                 *)
(* ------------------------------------------------------------------ *)

(** Assumption lifecycle status, tracked via metadata.
    [("assumption_status", MVString "invalidated")] marks an
    Assumption node as invalidated; the support tree is blocked
    for any path through an invalidated assumption. *)
Definition assumption_invalidated (n : Node) : bool :=
  match n.(node_kind) with
  | Assumption =>
    match find_metadata "assumption_status" n.(node_metadata) with
    | Some (MVString s) => String.eqb s "invalidated"
    | _ => false
    end
  | _ => false
  end.

Definition check_no_invalidated_assumptions (ac : AssuranceCase) : bool :=
  forallb (fun n => negb (assumption_invalidated n)) ac.(ac_nodes).

Definition solution_discharged (n : Node) : Prop :=
  n.(node_kind) = Solution ->
  exists e,
    n.(node_evidence) = Some e /\
    evidence_valid n e.

(* ------------------------------------------------------------------ *)
(* Evidence validity decidability                                      *)
(* ------------------------------------------------------------------ *)

(** Decidability of [evidence_valid] for [Certificate] evidence.
    ProofTerm validity ([P = node_claim]) is propositional equality
    and not generally decidable; Certificate validity is a boolean
    computation and always decidable. *)
Lemma evidence_valid_certificate_dec : forall n b tool v,
    {evidence_valid n (Certificate b tool v)} +
    {~ evidence_valid n (Certificate b tool v)}.
Proof.
  intros n b tool v. unfold evidence_valid.
  destruct (v b) eqn:E.
  - left. reflexivity.
  - right. intro H. rewrite H in E. discriminate.
Defined.

(** Boolean evidence validity check agrees with [evidence_valid]
    for [Certificate] evidence. *)
Lemma evidence_runtime_check_certificate : forall claim_text n b tool v,
    evidence_runtime_check claim_text (Certificate b tool v) = true <->
    evidence_valid n (Certificate b tool v).
Proof.
  intros. unfold evidence_runtime_check, evidence_valid. split; exact (fun H => H).
Qed.
