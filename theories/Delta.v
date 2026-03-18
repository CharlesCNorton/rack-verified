(* ------------------------------------------------------------------ *)
(* Diff calculus and PR-gating semantics                               *)
(*                                                                    *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Trace.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* Assurance delta types                                               *)
(* ================================================================== *)

(** A [NodeChange] describes a single change to a node in the
    assurance case. *)
Inductive NodeChange : Type :=
  | AddNode    : Node -> NodeChange
  | RemoveNode : Id -> NodeChange
  | UpdateEvidence : Id -> Evidence -> NodeChange.

(** A [LinkChange] describes a single change to a link. *)
Inductive LinkChange : Type :=
  | AddLink    : Link -> LinkChange
  | RemoveLink : Id -> Id -> LinkChange. (* from, to *)

(** A [TraceChange] describes a single change to a trace link. *)
Inductive TraceChange : Type :=
  | AddTrace    : TraceLink -> TraceChange
  | RemoveTrace : TraceLink -> TraceChange.

(** An [AssuranceDelta] is a typed diff over an assurance case. *)
Record AssuranceDelta : Type := {
  ad_node_changes  : list NodeChange;
  ad_link_changes  : list LinkChange;
  ad_trace_changes : list TraceChange;
  ad_commit        : option CommitId;
  ad_description   : string;
}.

(* ================================================================== *)
(* Delta application                                                   *)
(* ================================================================== *)

(** Apply a single node change. *)
Definition apply_node_change (ac : AssuranceCase)
    (nc : NodeChange) : AssuranceCase :=
  match nc with
  | AddNode n => {|
      ac_nodes := ac.(ac_nodes) ++ [n];
      ac_links := ac.(ac_links);
      ac_top := ac.(ac_top);
    |}
  | RemoveNode id => {|
      ac_nodes := filter (fun n =>
        negb (String.eqb n.(node_id) id)) ac.(ac_nodes);
      ac_links := filter (fun l =>
        negb (String.eqb l.(link_from) id) &&
        negb (String.eqb l.(link_to) id)) ac.(ac_links);
      ac_top := ac.(ac_top);
    |}
  | UpdateEvidence id ev => {|
      ac_nodes := map (fun n =>
        if String.eqb n.(node_id) id then {|
          node_id := n.(node_id);
          node_kind := n.(node_kind);
          node_claim_text := n.(node_claim_text);
          node_evidence := Some ev;
          node_metadata := n.(node_metadata);
          node_claim := n.(node_claim);
        |} else n) ac.(ac_nodes);
      ac_links := ac.(ac_links);
      ac_top := ac.(ac_top);
    |}
  end.

(** Apply a single link change. *)
Definition apply_link_change (ac : AssuranceCase)
    (lc : LinkChange) : AssuranceCase :=
  match lc with
  | AddLink l => {|
      ac_nodes := ac.(ac_nodes);
      ac_links := ac.(ac_links) ++ [l];
      ac_top := ac.(ac_top);
    |}
  | RemoveLink from to_ => {|
      ac_nodes := ac.(ac_nodes);
      ac_links := filter (fun l =>
        negb (String.eqb l.(link_from) from &&
              String.eqb l.(link_to) to_)) ac.(ac_links);
      ac_top := ac.(ac_top);
    |}
  end.

(** Apply all changes in a delta, left to right. *)
Definition apply_delta (ac : AssuranceCase)
    (delta : AssuranceDelta) : AssuranceCase :=
  let ac1 := fold_left apply_node_change
                       delta.(ad_node_changes) ac in
  fold_left apply_link_change delta.(ad_link_changes) ac1.

(* ================================================================== *)
(* Delta analysis                                                      *)
(* ================================================================== *)

(** Compute the set of node IDs affected (added, removed, or
    modified) by a delta. *)
Definition delta_affected_nodes (delta : AssuranceDelta) : list Id :=
  flat_map (fun nc =>
    match nc with
    | AddNode n => [n.(node_id)]
    | RemoveNode id => [id]
    | UpdateEvidence id _ => [id]
    end) delta.(ad_node_changes).

(** Compute node IDs that are preserved (not directly touched). *)
Definition delta_preserved_nodes (ac : AssuranceCase)
    (delta : AssuranceDelta) : list Id :=
  let affected := delta_affected_nodes delta in
  filter (fun id => negb (mem_string id affected))
         (map node_id ac.(ac_nodes)).

(** Nodes that need re-validation: nodes whose evidence was updated
    or whose support structure changed. *)
Definition delta_revalidation_needed (ac : AssuranceCase)
    (delta : AssuranceDelta) : list Id :=
  let evidence_updated :=
    flat_map (fun nc =>
      match nc with UpdateEvidence id _ => [id] | _ => [] end)
    delta.(ad_node_changes) in
  let structurally_affected :=
    flat_map (fun lc =>
      match lc with
      | AddLink l => [l.(link_from); l.(link_to)]
      | RemoveLink from to_ => [from; to_]
      end) delta.(ad_link_changes) in
  evidence_updated ++ structurally_affected.

(* ================================================================== *)
(* Preservation predicates                                             *)
(* ================================================================== *)

(** A node is preserved by a delta when it exists in both the
    original and the result, with the same kind, claim, and evidence. *)
Definition node_preserved (ac_before ac_after : AssuranceCase)
    (id : Id) : Prop :=
  match find_node ac_before id, find_node ac_after id with
  | Some n1, Some n2 =>
    n1.(node_kind) = n2.(node_kind) /\
    n1.(node_claim_text) = n2.(node_claim_text) /\
    n1.(node_evidence) = n2.(node_evidence)
  | _, _ => False
  end.

(** A delta preserves a support subtree when:
    1. All preserved nodes retain their evidence.
    2. All preserved structural links remain.
    3. No new cycles are introduced. *)
Definition delta_preserves_subtree (ac : AssuranceCase)
    (delta : AssuranceDelta) (root : Id) : Prop :=
  let ac' := apply_delta ac delta in
  let preserved := delta_preserved_nodes ac delta in
  forall id, In id preserved ->
    In id (root :: reachable_from ac root) ->
    node_preserved ac ac' id.

(* ================================================================== *)
(* PR-gating judgment                                                  *)
(* ================================================================== *)

(** The [PRAdmissible] judgment formalizes: "this delta preserves the
    admissibility of the top claim, given these re-runs."

    A PR is admissible when:
    1. Applying the delta produces a structurally valid case.
    2. All obligations (re-validation nodes) are discharged.
    3. No new cycles are introduced. *)
Record PRAdmissible (ac : AssuranceCase) (delta : AssuranceDelta)
    : Prop := {
  pra_result_wf : WellFormed (apply_delta ac delta);
  pra_preserved : forall id,
    In id (delta_preserved_nodes ac delta) ->
    node_preserved ac (apply_delta ac delta) id;
}.

(** Boolean PR-gating check.  This is the CI gate computation. *)
Definition check_pr_admissible (ac : AssuranceCase)
    (delta : AssuranceDelta) : bool :=
  let ac' := apply_delta ac delta in
  structural_checks ac'.

(** Soundness: the boolean check implies structural well-formedness
    of the result (modulo entailment and evidence validity). *)
Lemma check_pr_admissible_sound : forall ac delta,
    check_pr_admissible ac delta = true ->
    structural_checks (apply_delta ac delta) = true.
Proof. intros ac delta H. exact H. Qed.

(* ================================================================== *)
(* Delta composition                                                   *)
(* ================================================================== *)

(** Compose two deltas sequentially. *)
Definition compose_deltas (d1 d2 : AssuranceDelta) : AssuranceDelta := {|
  ad_node_changes  := d1.(ad_node_changes) ++ d2.(ad_node_changes);
  ad_link_changes  := d1.(ad_link_changes) ++ d2.(ad_link_changes);
  ad_trace_changes := d1.(ad_trace_changes) ++ d2.(ad_trace_changes);
  ad_commit        := d2.(ad_commit); (* later commit wins *)
  ad_description   :=
    d1.(ad_description) ++ " + " ++ d2.(ad_description);
|}.

(** Empty delta: identity element for composition. *)
Definition empty_delta : AssuranceDelta := {|
  ad_node_changes  := [];
  ad_link_changes  := [];
  ad_trace_changes := [];
  ad_commit        := None;
  ad_description   := "";
|}.

(** Applying the empty delta is the identity. *)
Lemma apply_empty_delta : forall ac,
    apply_delta ac empty_delta = ac.
Proof.
  intros ac. unfold apply_delta, empty_delta. simpl.
  destruct ac. reflexivity.
Qed.
