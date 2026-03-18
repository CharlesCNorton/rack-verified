(* ------------------------------------------------------------------ *)
(* Incremental checking with indexed data structures                   *)
(*                                                                    *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* Indexed assurance case                                              *)
(* ================================================================== *)

(** An [IndexedAC] wraps an [AssuranceCase] with precomputed indices
    for O(n) worst-case amortized lookup (vs O(n) per lookup without).
    For O(log n), substitute a balanced map; the refinement proofs
    below show the indexed version agrees with the naive version. *)
Record IndexedAC : Type := {
  iac_case       : AssuranceCase;
  iac_node_index : list (Id * Node);
  iac_child_index : list (Id * list Id);
}.

(** Build an indexed case from a plain case. *)
Definition build_indexed (ac : AssuranceCase) : IndexedAC := {|
  iac_case := ac;
  iac_node_index := build_node_index ac;
  iac_child_index := map (fun n =>
    (n.(node_id), supportedby_children ac n.(node_id)))
    ac.(ac_nodes);
|}.

(** Indexed node lookup. *)
Definition iac_find_node (iac : IndexedAC) (id : Id)
  : option Node :=
  find_node_indexed iac.(iac_node_index) id.

(** Indexed children lookup. *)
Fixpoint iac_assoc_find (id : Id) (idx : list (Id * list Id))
  : option (list Id) :=
  match idx with
  | [] => None
  | (k, v) :: rest =>
    if String.eqb k id then Some v
    else iac_assoc_find id rest
  end.

Definition iac_children (iac : IndexedAC) (id : Id)
  : list Id :=
  match iac_assoc_find id iac.(iac_child_index) with
  | Some kids => kids
  | None => []
  end.

(* ================================================================== *)
(* Refinement proofs                                                   *)
(* ================================================================== *)

(** The indexed node lookup agrees with the naive lookup. *)
Theorem iac_find_node_correct : forall ac id,
    iac_find_node (build_indexed ac) id = find_node ac id.
Proof.
  intros ac id. unfold iac_find_node, build_indexed. simpl.
  exact (find_node_indexed_correct ac id).
Qed.

(** The indexed children lookup agrees with the naive lookup. *)
Lemma iac_children_correct_go : forall ac nodes id,
    (forall n, In n nodes -> In n ac.(ac_nodes)) ->
    NoDup (map node_id nodes) ->
    In id (map node_id nodes) ->
    iac_assoc_find id
      (map (fun n => (n.(node_id), supportedby_children ac n.(node_id))) nodes) =
    Some (supportedby_children ac id).
Proof.
  intros ac nodes id Hsub Hnd Hin.
  induction nodes as [|n ns IH]; simpl.
  - destruct Hin.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    destruct (String.eqb n.(node_id) id) eqn:Heq.
    + apply String.eqb_eq in Heq. rewrite Heq. reflexivity.
    + apply IH.
      * intros n0 Hn0. apply Hsub. right. exact Hn0.
      * exact Hnd'.
      * destruct Hin as [Hin | Hin].
        -- rewrite Hin in Heq. rewrite String.eqb_refl in Heq.
           discriminate.
        -- exact Hin.
Qed.

(* ================================================================== *)
(* Incremental single-node check                                       *)
(* ================================================================== *)

(** Check a single node after it's been added or updated.
    Uses the indexed case for efficient node lookups.
    Children are computed from the case's links (the index
    optimizes node lookup, not child enumeration). *)
Definition iac_check_node (iac : IndexedAC) (id : Id) : bool :=
  match iac_find_node iac id with
  | None => false
  | Some n =>
    match n.(node_kind) with
    | Solution =>
      match n.(node_evidence) with
      | Some (ProofTerm _ _ _ _) => true
      | Some (Certificate b _ v) => v b
      | None => false
      end
    | Goal | Strategy =>
      negb (match supportedby_children iac.(iac_case) id with
            | [] => true | _ => false end)
    | _ => true
    end
  end.

(** The incremental check agrees with the full check. *)
Theorem iac_check_node_correct : forall ac id,
    iac_check_node (build_indexed ac) id = check_node ac id.
Proof.
  intros ac id. unfold iac_check_node, check_node.
  rewrite iac_find_node_correct. reflexivity.
Qed.

(** Check a single link after it's been added. *)
Definition iac_check_link (iac : IndexedAC) (l : Link) : bool :=
  match iac_find_node iac l.(link_from),
        iac_find_node iac l.(link_to) with
  | Some nf, Some nt =>
    match l.(link_kind) with
    | SupportedBy => true
    | InContextOf =>
      (match nf.(node_kind) with Goal | Strategy => true | _ => false end) &&
      (match nt.(node_kind) with
       | Context | Assumption | Justification => true | _ => false end)
    end
  | _, _ => false
  end.

(** The incremental link check agrees with the full check. *)
Theorem iac_check_link_correct : forall ac l,
    iac_check_link (build_indexed ac) l = check_link ac l.
Proof.
  intros ac l. unfold iac_check_link, check_link.
  repeat rewrite iac_find_node_correct. reflexivity.
Qed.

(* ================================================================== *)
(* Batch incremental checking                                          *)
(* ================================================================== *)

(** Check a batch of nodes (e.g., after a delta is applied). *)
Definition iac_check_nodes (iac : IndexedAC) (ids : list Id) : bool :=
  forallb (iac_check_node iac) ids.

(** Check a batch of links. *)
Definition iac_check_links (iac : IndexedAC) (links : list Link) : bool :=
  forallb (iac_check_link iac) links.
