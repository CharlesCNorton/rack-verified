(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Diagnostics                           *)
(*                                                                            *)
(*     Identity entailment, ID disjointness, metadata validation,            *)
(*     compose_cases, SupportWitness, check_support_tree, defeater           *)
(*     support, check_wf_extended, CheckError, diagnose_* functions.         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 17, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Types.
From RACK Require Import Graph.
From RACK Require Import WellFormedness.
From RACK Require Import TopoSort.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* Identity entailment checker (partial decision procedure)             *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Identity entailment via claim fingerprints                           *)
(* ------------------------------------------------------------------ *)

(** A [ClaimFingerprintMap] assigns an opaque fingerprint string to
    each node ID.  Two nodes have the same underlying [node_claim]
    iff their fingerprints match.  The map is constructed by the user
    at case-definition time (before extraction erases Props). *)
Definition ClaimFingerprintMap := list (Id * string).

Fixpoint fingerprint_lookup (id : Id) (fp : ClaimFingerprintMap)
    : option string :=
  match fp with
  | [] => None
  | (k, v) :: rest =>
    if String.eqb k id then Some v
    else fingerprint_lookup id rest
  end.

(** Sound identity entailment check: returns [true] only when every
    child's claim fingerprint equals the parent's.  Unlike
    [check_identity_entailment_node], this cannot false-positive
    (assuming the fingerprint map is faithful to [node_claim]). *)
Definition check_identity_entailment_fp_node (ac : AssuranceCase)
    (fp : ClaimFingerprintMap) (n : Node) : bool :=
  match n.(node_kind) with
  | Goal | Strategy =>
    match fingerprint_lookup n.(node_id) fp with
    | None => false
    | Some pfp =>
      let kids := supportedby_children ac n.(node_id) in
      forallb (fun kid =>
        match fingerprint_lookup kid fp with
        | Some kfp => String.eqb kfp pfp
        | None => false
        end) kids
    end
  | _ => true
  end.

Definition check_identity_entailment_fp (ac : AssuranceCase)
    (fp : ClaimFingerprintMap) : bool :=
  forallb (check_identity_entailment_fp_node ac fp) ac.(ac_nodes).

(** A fingerprint map is consistent when nodes with equal
    fingerprints have identical [node_claim] Props. *)
Definition fingerprint_consistent (ac : AssuranceCase)
    (fp : ClaimFingerprintMap) : Prop :=
  forall id1 id2 n1 n2 f,
    find_node ac id1 = Some n1 ->
    find_node ac id2 = Some n2 ->
    fingerprint_lookup id1 fp = Some f ->
    fingerprint_lookup id2 fp = Some f ->
    n1.(node_claim) = n2.(node_claim).

(* ------------------------------------------------------------------ *)
(* ID-disjointness check for compositional assembly                     *)
(* ------------------------------------------------------------------ *)

(** Boolean check that two assurance cases have disjoint node IDs. *)
Definition check_id_disjoint (ac1 ac2 : AssuranceCase) : bool :=
  let ids2 := map node_id ac2.(ac_nodes) in
  forallb (fun n => negb (mem_string n.(node_id) ids2)) ac1.(ac_nodes).

(* ------------------------------------------------------------------ *)
(* Metadata validation                                                  *)
(* ------------------------------------------------------------------ *)

(** Convert an ASCII character to a natural number (0-255). *)
Definition nat_of_ascii_core (c : ascii) : nat :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    (if b0 then 1 else 0) + (if b1 then 2 else 0) +
    (if b2 then 4 else 0) + (if b3 then 8 else 0) +
    (if b4 then 16 else 0) + (if b5 then 32 else 0) +
    (if b6 then 64 else 0) + (if b7 then 128 else 0)
  end.

(** Lexicographic string comparison for ISO 8601 timestamps.
    Returns true if [a] is strictly before [b].  Rejects
    comparisons between strings of different lengths (returns
    false) to prevent misorderings on non-normalized dates. *)
Fixpoint string_ltb_go (a b : string) : bool :=
  match a, b with
  | EmptyString, String _ _ => true
  | _, EmptyString => false
  | String ca ra, String cb rb =>
    let na := nat_of_ascii_core ca in
    let nb := nat_of_ascii_core cb in
    if Nat.ltb na nb then true
    else if Nat.ltb nb na then false
    else string_ltb_go ra rb
  end.

Fixpoint string_len (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ r => S (string_len r)
  end.

Definition string_ltb (a b : string) : bool :=
  if Nat.eqb (string_len a) (string_len b) then string_ltb_go a b
  else false.

(** Basic ISO 8601 date format check: exactly 10 characters,
    digits at positions 0-3, 5-6, 8-9, hyphens at 4, 7. *)
Definition is_digit_ascii (c : ascii) : bool :=
  let n := nat_of_ascii_core c in
  Nat.leb 48 n && Nat.leb n 57.

Definition is_hyphen_ascii (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii_core c) 45.

(** Maximum day for a given month (1-12).  February allows 29
    (permissive — accepts leap years without year validation). *)
Definition max_day_for_month (month : nat) : nat :=
  match month with
  | 2 => 29
  | 4 | 6 | 9 | 11 => 30
  | _ => 31
  end.

Definition check_date_format (s : string) : bool :=
  match s with
  | String c0 (String c1 (String c2 (String c3
    (String c4 (String c5 (String c6
    (String c7 (String c8 (String c9 EmptyString))))))))) =>
    is_digit_ascii c0 && is_digit_ascii c1 &&
    is_digit_ascii c2 && is_digit_ascii c3 &&
    is_hyphen_ascii c4 &&
    is_digit_ascii c5 && is_digit_ascii c6 &&
    is_hyphen_ascii c7 &&
    is_digit_ascii c8 && is_digit_ascii c9 &&
    let month := (nat_of_ascii_core c5 - 48) * 10 +
                 (nat_of_ascii_core c6 - 48) in
    let day   := (nat_of_ascii_core c8 - 48) * 10 +
                 (nat_of_ascii_core c9 - 48) in
    Nat.leb 1 month && Nat.leb month 12 &&
    Nat.leb 1 day && Nat.leb day (max_day_for_month month)
  | _ => false
  end.

(* ------------------------------------------------------------------ *)
(* Compositional assembly                                               *)
(* ------------------------------------------------------------------ *)

(* Merge two assurance cases by concatenating their nodes and links,
   adding a SupportedBy bridge from parent_goal to subcase_top.         *)
Definition compose_cases (parent subcase : AssuranceCase)
    (parent_goal : Id) : AssuranceCase := {|
  ac_nodes := parent.(ac_nodes) ++ subcase.(ac_nodes);
  ac_links := parent.(ac_links) ++ subcase.(ac_links) ++
              [{| link_kind := SupportedBy;
                  link_from := parent_goal;
                  link_to   := subcase.(ac_top) |}];
  ac_top   := parent.(ac_top);
|}.

(** Guarded composition: checks ID disjointness and avoids adding a
    duplicate bridge link.  Returns [None] when node IDs overlap. *)
Definition compose_cases_guarded (parent subcase : AssuranceCase)
    (parent_goal : Id) : option AssuranceCase :=
  if check_id_disjoint parent subcase then
    let bridge_exists :=
      existsb (fun l =>
        match l.(link_kind) with
        | SupportedBy =>
          String.eqb l.(link_from) parent_goal &&
          String.eqb l.(link_to) subcase.(ac_top)
        | _ => false
        end) parent.(ac_links) in
    let bridge := if bridge_exists then []
                  else [{| link_kind := SupportedBy;
                           link_from := parent_goal;
                           link_to   := subcase.(ac_top) |}] in
    Some {| ac_nodes := parent.(ac_nodes) ++ subcase.(ac_nodes);
            ac_links := parent.(ac_links) ++ subcase.(ac_links) ++ bridge;
            ac_top   := parent.(ac_top) |}
  else None.

(* ------------------------------------------------------------------ *)
(* Computable support-tree checker and witness                         *)
(* ------------------------------------------------------------------ *)

(* Inspectable witness of a support tree, suitable for extraction.
   Unlike the propositional SupportTree, this carries concrete data
   (node IDs, evidence labels) that can be examined at runtime.        *)
Inductive SupportWitness : Type :=
  | SW_Leaf : Id -> string -> SupportWitness
  | SW_Internal : Id -> list SupportWitness -> SupportWitness
  | SW_Annotation : Id -> SupportWitness.

(* Boolean support-tree check.  Verifies all decidable aspects:
   - Solutions have passing evidence
   - Goals/Strategies have non-empty children with passing subtrees
   - Context/Assumption/Justification nodes always pass
   Does NOT check entailment (undecidable) or ProofTerm type
   matching (guaranteed by Rocq's type checker, erased at extraction). *)
Fixpoint check_support_tree_go (ac : AssuranceCase) (fuel : nat)
    (id : Id) : bool :=
  match fuel with
  | 0 => false
  | S f =>
    match find_node ac id with
    | None => false
    | Some n =>
      match n.(node_kind) with
      | Solution =>
        match n.(node_evidence) with
        | Some (ProofTerm _ _ _ (Some f)) => f n.(node_claim_text)
        | Some (ProofTerm _ _ _ None) => false
        | Some (Certificate b _ v) => v b
        | None => false
        end
      | Context | Assumption | Justification => true
      | Goal | Strategy =>
        let kids := supportedby_children ac id in
        match kids with
        | [] => false
        | _ => forallb (check_support_tree_go ac f) kids
        end
      end
    end
  end.

Definition check_support_tree (ac : AssuranceCase) (id : Id) : bool :=
  check_support_tree_go ac (length ac.(ac_nodes)) id.

(* ------------------------------------------------------------------ *)
(* Defeater support                                                     *)
(* ------------------------------------------------------------------ *)

Definition defeater_sources (ac : AssuranceCase) (id : Id) : list Id :=
  map link_from
    (filter (fun l => andb
               (String.eqb l.(link_to) id)
               (match l.(link_kind) with Defeater => true | _ => false end))
            ac.(ac_links)).

Definition defeater_resolved (ac : AssuranceCase) (def_id : Id) : bool :=
  match supportedby_children ac def_id with
  | [] => false
  | kids => existsb (check_support_tree_go ac (length ac.(ac_nodes))) kids
  end.

Definition check_defeaters (ac : AssuranceCase) : bool :=
  forallb (fun l =>
    match l.(link_kind) with
    | Defeater => defeater_resolved ac l.(link_from)
    | _ => true
    end) ac.(ac_links).

(** [check_wf_extended] extends [structural_checks] with defeater
    resolution.  All soundness proofs go through [structural_checks];
    defeater checking is an additional CI-time validation. *)
Definition check_wf_extended (ac : AssuranceCase) : bool :=
  structural_checks ac && check_defeaters ac.

(** [check_wf_extended] implies [structural_checks]. *)
Lemma check_wf_extended_structural : forall ac,
    check_wf_extended ac = true -> structural_checks ac = true.
Proof.
  intros ac H. unfold check_wf_extended in H.
  apply Bool.andb_true_iff in H. exact (proj1 H).
Qed.

(** [structural_checks] + [check_defeaters] = [check_wf_extended]. *)
Lemma structural_defeaters_well_formed : forall ac,
    structural_checks ac = true ->
    check_defeaters ac = true ->
    check_wf_extended ac = true.
Proof.
  intros ac Hs Hd. unfold check_wf_extended.
  rewrite Hs, Hd. reflexivity.
Qed.

(** [well_typed_defeater_links] follows from [check_context_links]. *)
Lemma check_context_links_defeaters : forall ac,
    check_context_links ac = true ->
    well_typed_defeater_links ac.
Proof.
  intros ac H l Hin Hkind.
  unfold check_context_links in H.
  apply forallb_forall with (x := l) in H; [| exact Hin].
  rewrite Hkind in H.
  destruct (find_node ac l.(link_to)) as [nt|]; [| discriminate].
  exists nt. split; [reflexivity |].
  destruct nt.(node_kind); try discriminate;
    [left | right]; reflexivity.
Qed.

(** [check_defeaters] soundness: if it passes, every defeater link
    has a resolved counter-argument. *)
Definition defeaters_resolved (ac : AssuranceCase) : Prop :=
  forall l, In l ac.(ac_links) ->
    l.(link_kind) = Defeater ->
    exists kid, In kid (supportedby_children ac l.(link_from)) /\
      check_support_tree_go ac (length ac.(ac_nodes)) kid = true.

Lemma check_defeaters_sound : forall ac,
    check_defeaters ac = true -> defeaters_resolved ac.
Proof.
  intros ac H l Hin Hkind. unfold check_defeaters in H.
  apply forallb_forall with (x := l) in H; [| exact Hin].
  rewrite Hkind in H. unfold defeater_resolved in H.
  destruct (supportedby_children ac l.(link_from)) as [|k ks] eqn:Hkids;
    [discriminate |].
  apply existsb_exists in H. destruct H as [kid [Hkin Hcheck]].
  exists kid. split; [exact Hkin | exact Hcheck].
Qed.

(* Compute an inspectable witness (if one exists). *)
Fixpoint compute_support_witness_go (ac : AssuranceCase) (fuel : nat)
    (id : Id) : option SupportWitness :=
  match fuel with
  | 0 => None
  | S f =>
    match find_node ac id with
    | None => None
    | Some n =>
      match n.(node_kind) with
      | Solution =>
        match n.(node_evidence) with
        | Some e =>
          let valid := match e with
            | ProofTerm _ _ _ (Some f) => f n.(node_claim_text)
            | ProofTerm _ _ _ None => false
            | Certificate b _ v => v b
            end in
          if valid then Some (SW_Leaf id (evidence_label e)) else None
        | None => None
        end
      | Context | Assumption | Justification =>
        Some (SW_Annotation id)
      | Goal | Strategy =>
        let kids := supportedby_children ac id in
        match kids with
        | [] => None
        | _ =>
          let child_results :=
            map (compute_support_witness_go ac f) kids in
          if forallb (fun o =>
            match o with Some _ => true | None => false end)
            child_results
          then Some (SW_Internal id
            (flat_map (fun o =>
              match o with Some w => [w] | None => [] end)
              child_results))
          else None
        end
      end
    end
  end.

Definition compute_support_witness (ac : AssuranceCase)
    (id : Id) : option SupportWitness :=
  compute_support_witness_go ac (length ac.(ac_nodes)) id.

(* ------------------------------------------------------------------ *)
(* Diagnostic error reporting                                           *)
(* ------------------------------------------------------------------ *)

(* Structured errors identifying the failing node or link.              *)
Inductive CheckError : Type :=
  | ErrTopNotGoal       : Id -> CheckError
  | ErrDanglingFrom     : Id -> Id -> CheckError
  | ErrDanglingTo       : Id -> Id -> CheckError
  | ErrDuplicateId      : Id -> CheckError
  | ErrUnsupported      : Id -> CheckError   (* Goal/Strategy with no children *)
  | ErrMissingEvidence  : Id -> CheckError   (* Solution with no evidence *)
  | ErrInvalidEvidence  : Id -> CheckError   (* Certificate validator fails *)
  | ErrBadContextSource : Id -> Id -> CheckError   (* InContextOf from wrong kind *)
  | ErrBadContextTarget : Id -> Id -> CheckError   (* InContextOf to wrong kind *)
  | ErrCycle            : Id -> CheckError
  | ErrExpiredEvidence  : Id -> string -> CheckError  (* node id, expiry date *)
  | ErrMissingRequiredKey : Id -> string -> CheckError (* node id, key name *)
  | ErrMalformedTimestamp : Id -> string -> CheckError (* node id, bad value *)
  | ErrUnresolvedDefeater : Id -> Id -> CheckError (* defeater node, target node *)
  | ErrUndeveloped : Id -> CheckError
  | ErrInvalidatedAssumption : Id -> CheckError.

Definition diagnose_top (ac : AssuranceCase) : list CheckError :=
  match find_node ac ac.(ac_top) with
  | Some n => match n.(node_kind) with Goal => [] | _ => [ErrTopNotGoal ac.(ac_top)] end
  | None => [ErrTopNotGoal ac.(ac_top)]
  end.

Definition diagnose_dangling (ac : AssuranceCase) : list CheckError :=
  flat_map (fun l =>
    (match find_node ac l.(link_from) with
     | Some _ => []
     | None => [ErrDanglingFrom l.(link_from) l.(link_to)]
     end) ++
    (match find_node ac l.(link_to) with
     | Some _ => []
     | None => [ErrDanglingTo l.(link_from) l.(link_to)]
     end))
    ac.(ac_links).

Definition diagnose_unique_ids (ac : AssuranceCase) : list CheckError :=
  let fix go (seen : list Id) (nodes : list Node) : list CheckError :=
    match nodes with
    | [] => []
    | n :: rest =>
      if mem_string n.(node_id) seen
      then ErrDuplicateId n.(node_id) :: go seen rest
      else go (n.(node_id) :: seen) rest
    end
  in go [] ac.(ac_nodes).

Definition diagnose_discharged (ac : AssuranceCase) : list CheckError :=
  flat_map (fun n =>
    match n.(node_kind) with
    | Goal | Strategy =>
      match supportedby_children ac n.(node_id) with
      | [] => [ErrUnsupported n.(node_id)]
      | _ => []
      end
    | Solution =>
      match n.(node_evidence) with
      | None => [ErrMissingEvidence n.(node_id)]
      | Some (ProofTerm _ _ _ (Some f)) =>
        if f n.(node_claim_text) then [] else [ErrInvalidEvidence n.(node_id)]
      | Some (ProofTerm _ _ _ None) =>
        [ErrInvalidEvidence n.(node_id)]
      | Some (Certificate b _ v) =>
        if v b then [] else [ErrInvalidEvidence n.(node_id)]
      end
    | _ => []
    end) ac.(ac_nodes).

Definition diagnose_context_links (ac : AssuranceCase) : list CheckError :=
  flat_map (fun l =>
    match l.(link_kind) with
    | SupportedBy => []
    | InContextOf =>
      let src_err :=
        match find_node ac l.(link_from) with
        | Some nf =>
          match nf.(node_kind) with
          | Goal | Strategy => []
          | _ => [ErrBadContextSource l.(link_from) l.(link_to)]
          end
        | None => []
        end in
      let tgt_err :=
        match find_node ac l.(link_to) with
        | Some nt =>
          match nt.(node_kind) with
          | Context | Assumption | Justification => []
          | _ => [ErrBadContextTarget l.(link_from) l.(link_to)]
          end
        | None => []
        end in
      src_err ++ tgt_err
    | Defeater =>
      match find_node ac l.(link_to) with
      | Some nt =>
        match nt.(node_kind) with
        | Goal | Strategy => []
        | _ => [ErrBadContextTarget l.(link_from) l.(link_to)]
        end
      | None => []
      end
    end) ac.(ac_links).

(** Diagnose acyclicity using the topo-order verifier (matches
    [structural_checks], enabling the completeness proof in Reflect.v).
    Falls back to the BFS checker for cycle localization. *)
Definition diagnose_acyclic (ac : AssuranceCase) : list CheckError :=
  if verify_topo_order ac (topo_sort ac) then []
  else
    (* Topo order failed: use BFS to locate specific cycles. *)
    flat_map (fun n =>
      if mem_string n.(node_id) (reachable_from ac n.(node_id))
      then [ErrCycle n.(node_id)]
      else []) ac.(ac_nodes).

(** Unified acyclicity decision.  Returns [(true, [])] when the
    graph is acyclic (via [verify_topo_order], which has a complete
    soundness proof to [Acyclic] in Reflect.v).  Returns
    [(false, errors)] with per-node cycle diagnostics when it is
    not.  This is the single recommended entry point; prefer it
    over calling [check_acyclic] or [verify_topo_order] directly.

    Soundness chain:
      [fst (decide_acyclic ac) = true]
      -> [verify_topo_order ac (topo_sort ac) = true]   (by definition)
      -> [Acyclic ac]                                    (verify_topo_order_acyclic)

    Cycle localization:
      [snd (decide_acyclic ac)] lists [ErrCycle id] for every
      node [id] that [check_acyclic] detects in a cycle (BFS).  *)
Definition decide_acyclic (ac : AssuranceCase) : bool * list CheckError :=
  if verify_topo_order ac (topo_sort ac) then (true, [])
  else
    let errs := flat_map (fun n =>
      if mem_string n.(node_id) (reachable_from ac n.(node_id))
      then [ErrCycle n.(node_id)]
      else []) ac.(ac_nodes) in
    (false, errs).

Definition diagnose_defeaters (ac : AssuranceCase) : list CheckError :=
  flat_map (fun l =>
    match l.(link_kind) with
    | Defeater =>
      if defeater_resolved ac l.(link_from) then []
      else [ErrUnresolvedDefeater l.(link_from) l.(link_to)]
    | _ => []
    end) ac.(ac_links).

Definition diagnose_all (ac : AssuranceCase) : list CheckError :=
  diagnose_top ac ++
  diagnose_dangling ac ++
  diagnose_unique_ids ac ++
  diagnose_discharged ac ++
  diagnose_context_links ac ++
  diagnose_acyclic ac ++
  diagnose_defeaters ac.

Definition diagnose_undeveloped (ac : AssuranceCase) : list CheckError :=
  flat_map (fun n =>
    if node_undeveloped n then [ErrUndeveloped n.(node_id)]
    else []) ac.(ac_nodes).

Definition diagnose_invalidated_assumptions (ac : AssuranceCase)
    : list CheckError :=
  flat_map (fun n =>
    if assumption_invalidated n
    then [ErrInvalidatedAssumption n.(node_id)]
    else []) ac.(ac_nodes).

(** Diagnostic function that mirrors [structural_checks] exactly.
    Uses [check_all_discharged] (all-nodes) rather than
    [check_all_discharged] (all-nodes), and the topo-order
    acyclicity verifier.  The completeness proof in Reflect.v
    establishes: [diagnose_structural ac = []] ->
    [structural_checks ac = true]. *)
Definition diagnose_structural (ac : AssuranceCase) : list CheckError :=
  diagnose_top ac ++
  diagnose_unique_ids ac ++
  diagnose_dangling ac ++
  diagnose_acyclic ac ++
  (flat_map (fun n =>
    match n.(node_kind) with
    | Goal | Strategy =>
      match supportedby_children ac n.(node_id) with
      | [] => [ErrUnsupported n.(node_id)]
      | _ => []
      end
    | Solution =>
      match n.(node_evidence) with
      | None => [ErrMissingEvidence n.(node_id)]
      | Some (ProofTerm _ _ _ (Some f)) =>
        if f n.(node_claim_text) then [] else [ErrInvalidEvidence n.(node_id)]
      | Some (ProofTerm _ _ _ None) =>
        [ErrInvalidEvidence n.(node_id)]
      | Some (Certificate b _ v) =>
        if v b then [] else [ErrInvalidEvidence n.(node_id)]
      end
    | _ => []
    end) ac.(ac_nodes)) ++
  diagnose_context_links ac ++
  diagnose_defeaters ac.

(* ------------------------------------------------------------------ *)
(* Metadata validation diagnostics                                      *)
(* ------------------------------------------------------------------ *)

(** Diagnose expired evidence: nodes whose [valid_until] timestamp
    is lexicographically before the given [cutoff].
    Only accepts [MVTimestamp] values — [MVString] is not a valid
    timestamp encoding and is silently skipped.  Use
    [diagnose_malformed_timestamps] to catch [MVString] misuse. *)
Definition diagnose_metadata_expiry (ac : AssuranceCase)
    (cutoff : string) : list CheckError :=
  flat_map (fun n =>
    match find_metadata "valid_until" n.(node_metadata) with
    | Some (MVTimestamp expiry) =>
      if string_ltb expiry cutoff then [ErrExpiredEvidence n.(node_id) expiry]
      else []
    | _ => []
    end) ac.(ac_nodes).

(** Diagnose missing required metadata keys.
    [required] maps each [NodeKind] to a list of mandatory key names. *)
Definition diagnose_required_keys (ac : AssuranceCase)
    (required : list (NodeKind * string)) : list CheckError :=
  flat_map (fun n =>
    flat_map (fun req =>
      if NodeKind_eqb n.(node_kind) (fst req) then
        if has_metadata_key (snd req) n.(node_metadata) then []
        else [ErrMissingRequiredKey n.(node_id) (snd req)]
      else []) required) ac.(ac_nodes).

(** Known timestamp metadata keys.  [MVString] values under these
    keys are flagged as malformed — callers should use [MVTimestamp]. *)
Definition is_timestamp_key (k : string) : bool :=
  String.eqb k "timestamp" || String.eqb k "valid_from" ||
  String.eqb k "valid_until".

(** Diagnose malformed timestamps: [MVTimestamp] values that fail
    the basic YYYY-MM-DD format check, and [MVString] values
    under known timestamp keys (should be [MVTimestamp]). *)
Definition diagnose_malformed_timestamps (ac : AssuranceCase)
    : list CheckError :=
  flat_map (fun n =>
    flat_map (fun kv =>
      match snd kv with
      | MVTimestamp s =>
        if check_date_format s then []
        else [ErrMalformedTimestamp n.(node_id) s]
      | MVString s =>
        if is_timestamp_key (fst kv) then
          [ErrMalformedTimestamp n.(node_id) s]
        else []
      | _ => []
      end) n.(node_metadata)) ac.(ac_nodes).

(* ------------------------------------------------------------------ *)
(* Incremental / single-element checkers                                *)
(* ------------------------------------------------------------------ *)

(* Check a single node in isolation: kind-specific structural rules.    *)
Definition check_node (ac : AssuranceCase) (id : Id) : bool :=
  match find_node ac id with
  | None => false
  | Some n =>
    match n.(node_kind) with
    | Solution =>
      match n.(node_evidence) with
      | Some (ProofTerm _ _ _ (Some f)) => f n.(node_claim_text)
      | Some (ProofTerm _ _ _ None) => false
      | Some (Certificate b _ v) => v b
      | None => false
      end
    | Goal | Strategy =>
      negb (match supportedby_children ac id with [] => true | _ => false end)
    | _ => true
    end
  end.

(* Check a single link: both endpoints exist, context-link typing.      *)
Definition check_link (ac : AssuranceCase) (l : Link) : bool :=
  match find_node ac l.(link_from), find_node ac l.(link_to) with
  | Some nf, Some nt =>
    match l.(link_kind) with
    | SupportedBy => true
    | InContextOf =>
      (match nf.(node_kind) with Goal | Strategy => true | _ => false end) &&
      (match nt.(node_kind) with
       | Context | Assumption | Justification => true | _ => false end)
    | Defeater =>
      match nt.(node_kind) with Goal | Strategy => true | _ => false end
    end
  | _, _ => false
  end.

(* Diagnose a single node — returns a list (possibly empty) of errors. *)
Definition diagnose_node (ac : AssuranceCase) (id : Id)
  : list CheckError :=
  match find_node ac id with
  | None => [ErrDanglingFrom id id]
  | Some n =>
    match n.(node_kind) with
    | Solution =>
      match n.(node_evidence) with
      | None => [ErrMissingEvidence id]
      | Some (ProofTerm _ _ _ (Some f)) =>
        if f n.(node_claim_text) then [] else [ErrInvalidEvidence id]
      | Some (ProofTerm _ _ _ None) =>
        [ErrInvalidEvidence id]
      | Some (Certificate b _ v) =>
        if v b then [] else [ErrInvalidEvidence id]
      end
    | Goal | Strategy =>
      match supportedby_children ac id with
      | [] => [ErrUnsupported id]
      | _ => []
      end
    | _ => []
    end
  end.
