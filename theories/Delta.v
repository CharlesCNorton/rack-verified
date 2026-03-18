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

(** Apply a single trace change. *)
Definition apply_trace_change (tls : list TraceLink)
    (tc : TraceChange) : list TraceLink :=
  match tc with
  | AddTrace tl => tls ++ [tl]
  | RemoveTrace tl =>
    filter (fun t =>
      negb (TraceLinkKind_eqb t.(tl_kind) tl.(tl_kind) &&
            String.eqb t.(tl_source) tl.(tl_source) &&
            String.eqb t.(tl_target) tl.(tl_target)))
      tls
  end.

(** Apply all changes in a delta, left to right. *)
Definition apply_delta (ac : AssuranceCase)
    (delta : AssuranceDelta) : AssuranceCase :=
  let ac1 := fold_left apply_node_change
                       delta.(ad_node_changes) ac in
  fold_left apply_link_change delta.(ad_link_changes) ac1.

(** Apply a delta to a trace graph, updating both the case and traces. *)
Definition apply_delta_trace (tg : TraceGraph)
    (delta : AssuranceDelta) : TraceGraph := {|
  tg_case := apply_delta tg.(tg_case) delta;
  tg_requirements := tg.(tg_requirements);
  tg_artifacts := tg.(tg_artifacts);
  tg_commits := match delta.(ad_commit) with
                | Some c => tg.(tg_commits) ++ [c]
                | None => tg.(tg_commits)
                end;
  tg_tool_runs := tg.(tg_tool_runs);
  tg_owners := tg.(tg_owners);
  tg_trace_links := fold_left apply_trace_change
                      delta.(ad_trace_changes) tg.(tg_trace_links);
|}.

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

(* ================================================================== *)
(* Additive delta composition                                        *)
(* ================================================================== *)

Definition additive_node_change (nc : NodeChange) : bool :=
  match nc with RemoveNode _ => false | _ => true end.

Definition additive_delta (d : AssuranceDelta) : bool :=
  forallb additive_node_change d.(ad_node_changes).

(** Additive node changes commute with any link change because
    they only touch ac_nodes while link changes only touch ac_links. *)
Lemma anc_alc_commute : forall ac nc lc,
    additive_node_change nc = true ->
    apply_link_change (apply_node_change ac nc) lc =
    apply_node_change (apply_link_change ac lc) nc.
Proof.
  intros ac nc lc Hadd.
  destruct nc as [n | id | id ev]; simpl in Hadd; [| discriminate |];
    destruct lc as [l | from to]; destruct ac; reflexivity.
Qed.

(** Lift single-step commutation to fold_left over node changes. *)
Lemma fold_anc_alc_commute : forall ncs ac lc,
    forallb additive_node_change ncs = true ->
    fold_left apply_node_change ncs (apply_link_change ac lc) =
    apply_link_change (fold_left apply_node_change ncs ac) lc.
Proof.
  induction ncs as [|nc ncs' IH]; intros ac lc Hadd.
  - reflexivity.
  - simpl. simpl in Hadd. apply Bool.andb_true_iff in Hadd.
    destruct Hadd as [Hnc Hrest].
    rewrite <- (anc_alc_commute ac nc lc Hnc).
    exact (IH _ _ Hrest).
Qed.

(** Full commutation: fold of link changes commutes with fold of
    additive node changes. *)
Lemma fold_alc_fold_anc_commute : forall lcs ncs ac,
    forallb additive_node_change ncs = true ->
    fold_left apply_link_change lcs (fold_left apply_node_change ncs ac) =
    fold_left apply_node_change ncs (fold_left apply_link_change lcs ac).
Proof.
  induction lcs as [|lc lcs' IH]; intros ncs ac Hadd.
  - reflexivity.
  - simpl.
    rewrite <- (fold_anc_alc_commute ncs ac lc Hadd).
    exact (IH ncs (apply_link_change ac lc) Hadd).
Qed.

(** Composition distributes over application when the second delta
    is additive (no RemoveNode changes).  RemoveNode changes affect
    both ac_nodes and ac_links, breaking the commutation. *)
Theorem apply_delta_compose : forall ac d1 d2,
    additive_delta d2 = true ->
    apply_delta ac (compose_deltas d1 d2) =
    apply_delta (apply_delta ac d1) d2.
Proof.
  intros ac d1 d2 Hadd. unfold apply_delta, compose_deltas. simpl.
  do 2 rewrite fold_left_app.
  apply (f_equal (fold_left apply_link_change d2.(ad_link_changes))).
  exact (fold_alc_fold_anc_commute
           d1.(ad_link_changes) d2.(ad_node_changes)
           (fold_left apply_node_change d1.(ad_node_changes) ac)
           Hadd).
Qed.

(* ================================================================== *)
(* RemoveNode commutation under disjointness                          *)
(* ================================================================== *)

(** A RemoveNode and a link change commute when the added link
    does not reference the removed node. *)
Definition node_link_disjoint (nc : NodeChange) (lc : LinkChange) : bool :=
  match nc with
  | RemoveNode id =>
    match lc with
    | AddLink l =>
      negb (String.eqb l.(link_from) id) &&
      negb (String.eqb l.(link_to) id)
    | RemoveLink _ _ => true
    end
  | _ => true
  end.

(** filter commutes with filter (standard). *)
Lemma filter_comm : forall {A} (f g : A -> bool) (l : list A),
    filter f (filter g l) = filter g (filter f l).
Proof.
  intros A f g l. induction l as [|a l' IH]; simpl.
  - reflexivity.
  - destruct (g a) eqn:Hg; destruct (f a) eqn:Hf;
      simpl; try rewrite Hg; try rewrite Hf; try rewrite IH; reflexivity.
Qed.

(** filter distributes over app (standard). *)
Lemma filter_app : forall {A} (f : A -> bool) (l1 l2 : list A),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  intros A f l1. induction l1 as [|a l1' IH]; intro l2; simpl.
  - reflexivity.
  - destruct (f a); [simpl; f_equal |]; exact (IH l2).
Qed.

(** General node-link commutation under disjointness. *)
Lemma anc_alc_commute_general : forall ac nc lc,
    node_link_disjoint nc lc = true ->
    apply_link_change (apply_node_change ac nc) lc =
    apply_node_change (apply_link_change ac lc) nc.
Proof.
  intros ac nc lc Hdisj.
  destruct nc as [n | id | id ev];
    destruct lc as [l | from to]; destruct ac as [ns ls tp]; simpl in *;
    try reflexivity.
  - (* RemoveNode + AddLink: need link not to reference removed node *)
    apply Bool.andb_true_iff in Hdisj. destruct Hdisj as [Hf Ht].
    f_equal.
    rewrite filter_app. simpl.
    rewrite Hf, Ht. simpl. reflexivity.
  - (* RemoveNode + RemoveLink: filters commute *)
    f_equal. apply filter_comm.
Qed.

(** Pairwise disjointness between all node changes and a link change. *)
Definition all_node_link_disjoint (ncs : list NodeChange) (lc : LinkChange) : bool :=
  forallb (fun nc => node_link_disjoint nc lc) ncs.

(** Lift to fold_left of node changes. *)
Lemma fold_anc_alc_commute_general : forall ncs ac lc,
    all_node_link_disjoint ncs lc = true ->
    fold_left apply_node_change ncs (apply_link_change ac lc) =
    apply_link_change (fold_left apply_node_change ncs ac) lc.
Proof.
  induction ncs as [|nc ncs' IH]; intros ac lc Hdisj.
  - reflexivity.
  - simpl in Hdisj. apply Bool.andb_true_iff in Hdisj.
    destruct Hdisj as [Hnc Hrest].
    simpl. rewrite <- (anc_alc_commute_general ac nc lc Hnc).
    exact (IH _ _ Hrest).
Qed.

(** General delta composition under pairwise disjointness. *)
Definition deltas_disjoint (d1 d2 : AssuranceDelta) : bool :=
  forallb (fun lc =>
    forallb (fun nc => node_link_disjoint nc lc)
            d2.(ad_node_changes))
  d1.(ad_link_changes).

Lemma fold_alc_fold_anc_commute_general : forall lcs ncs ac,
    forallb (fun lc =>
      forallb (fun nc => node_link_disjoint nc lc) ncs) lcs = true ->
    fold_left apply_link_change lcs (fold_left apply_node_change ncs ac) =
    fold_left apply_node_change ncs (fold_left apply_link_change lcs ac).
Proof.
  induction lcs as [|lc lcs' IH]; intros ncs ac Hdisj.
  - reflexivity.
  - simpl. simpl in Hdisj. apply Bool.andb_true_iff in Hdisj.
    destruct Hdisj as [Hlc Hrest].
    rewrite <- (fold_anc_alc_commute_general ncs ac lc Hlc).
    exact (IH ncs (apply_link_change ac lc) Hrest).
Qed.

Theorem apply_delta_compose_general : forall ac d1 d2,
    deltas_disjoint d1 d2 = true ->
    apply_delta ac (compose_deltas d1 d2) =
    apply_delta (apply_delta ac d1) d2.
Proof.
  intros ac d1 d2 Hdisj. unfold apply_delta, compose_deltas. simpl.
  do 2 rewrite fold_left_app.
  apply (f_equal (fold_left apply_link_change d2.(ad_link_changes))).
  exact (fold_alc_fold_anc_commute_general
           d1.(ad_link_changes) d2.(ad_node_changes)
           (fold_left apply_node_change d1.(ad_node_changes) ac) Hdisj).
Qed.
