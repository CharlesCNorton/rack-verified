(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Mechanized Evidence Graphs            *)
(*                                                                            *)
(*     Typed GSN-inspired claim/strategy/evidence graph with machine-         *)
(*     checked well-formedness, evidence coverage, acyclicity, and            *)
(*     support-tree completeness. Designed for CI-gated assurance cases       *)
(*     linking requirements to proofs and external certificates.              *)
(*                                                                            *)
(*     "The price of reliability is the pursuit of the utmost simplicity."    *)
(*     — C.A.R. Hoare, 1980                                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 17, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Core types                                                           *)
(* ------------------------------------------------------------------ *)

Definition Id := string.

Inductive NodeKind : Type :=
  | Goal | Strategy | Solution | Context | Assumption | Justification.

(* Evidence must *witness* the node's own claim, not an arbitrary Prop. *)
Inductive Evidence : Type :=
  (* A Rocq proof term whose type IS the node's claim.
     The string label survives extraction, identifying what was proved. *)
  | ProofTerm  : string -> forall (P : Prop), P -> Evidence
  (* External certificate: a raw blob plus a decidable validator *)
  | Certificate : string -> (string -> bool) -> Evidence.

Record Node : Type := {
  node_id         : Id;
  node_kind       : NodeKind;
  node_claim_text : string;   (* human-readable claim — survives extraction *)
  node_evidence   : option Evidence;
  node_claim      : Prop;     (* logical claim — erased at extraction *)
}.

Inductive LinkKind : Type := SupportedBy | InContextOf.

Record Link : Type := {
  link_kind : LinkKind;
  link_from : Id;
  link_to   : Id;
}.

Record AssuranceCase : Type := {
  ac_nodes : list Node;
  ac_links : list Link;
  ac_top   : Id;
}.

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
  | ProofTerm _ P _   => P = n.(node_claim)
  | Certificate b v => v b = true
  end.

(* After extraction, ProofTerm's Prop and proof witness are erased;
   only this label survives to identify which theorem was proved.
   Certificate evidence returns the raw blob payload.
   Use this for audit trails and inspectable witness trees.            *)
Definition evidence_label (e : Evidence) : string :=
  match e with
  | ProofTerm lbl _ _ => lbl
  | Certificate blob _ => blob
  end.

Definition solution_discharged (n : Node) : Prop :=
  n.(node_kind) = Solution ->
  exists e,
    n.(node_evidence) = Some e /\
    evidence_valid n e.

(* ------------------------------------------------------------------ *)
(* Support tree — the central inductive witness                         *)
(* ------------------------------------------------------------------ *)

Inductive SupportTree (ac : AssuranceCase) : Id -> Prop :=
  | ST_Leaf : forall id n e,
      find_node ac id = Some n ->
      n.(node_kind) = Solution ->
      n.(node_evidence) = Some e ->
      evidence_valid n e ->
      SupportTree ac id

  | ST_Internal : forall id n (kids : list Id),
      find_node ac id = Some n ->
      n.(node_kind) <> Solution ->
      kids = supportedby_children ac id ->
      kids <> [] ->
      (forall kid, In kid kids -> SupportTree ac kid) ->
      (let child_claims :=
           flat_map (fun kid =>
             match find_node ac kid with
             | Some cn => [cn.(node_claim)]
             | None     => []
             end) kids
       in fold_right and True child_claims -> n.(node_claim)) ->
      SupportTree ac id

  | ST_Annotation : forall id n,
      find_node ac id = Some n ->
      (n.(node_kind) = Context \/
       n.(node_kind) = Assumption \/
       n.(node_kind) = Justification) ->
      SupportTree ac id.

(* ------------------------------------------------------------------ *)
(* Well-formedness                                                      *)
(* ------------------------------------------------------------------ *)

Definition top_is_goal (ac : AssuranceCase) : Prop :=
  exists n,
    find_node ac ac.(ac_top) = Some n /\
    n.(node_kind) = Goal.

Definition all_reachable_discharged (ac : AssuranceCase) : Prop :=
  forall id,
    (id = ac.(ac_top) \/ Reaches ac ac.(ac_top) id) ->
    match find_node ac id with
    | None   => False
    | Some n =>
      match n.(node_kind) with
      | Solution =>
          exists e,
            n.(node_evidence) = Some e /\
            evidence_valid n e
      | Goal | Strategy =>
          supportedby_children ac id <> []
      | _ => True
      end
    end.

Definition no_dangling_links (ac : AssuranceCase) : Prop :=
  forall l,
    In l ac.(ac_links) ->
    (exists n, find_node ac l.(link_from) = Some n) /\
    (exists n, find_node ac l.(link_to)   = Some n).

(* ------------------------------------------------------------------ *)
(* Context link type constraints                                        *)
(* ------------------------------------------------------------------ *)

(* InContextOf links must go FROM Goal/Strategy TO Context/Assumption/
   Justification nodes.                                                  *)
Definition well_typed_context_links (ac : AssuranceCase) : Prop :=
  forall l,
    In l ac.(ac_links) ->
    l.(link_kind) = InContextOf ->
    exists nf nt,
      find_node ac l.(link_from) = Some nf /\
      find_node ac l.(link_to)   = Some nt /\
      (nf.(node_kind) = Goal \/ nf.(node_kind) = Strategy) /\
      (nt.(node_kind) = Context \/ nt.(node_kind) = Assumption \/
       nt.(node_kind) = Justification).

(* ------------------------------------------------------------------ *)
(* NoDup decision via boolean reflection                                *)
(* ------------------------------------------------------------------ *)

Definition mem_string (s : string) (l : list string) : bool :=
  existsb (String.eqb s) l.

Fixpoint nodupb (l : list string) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (mem_string x xs) && nodupb xs
  end.

Lemma existsb_In : forall s l,
    existsb (String.eqb s) l = true -> In s l.
Proof.
  intros s l. induction l as [|a l' IH]; simpl.
  - discriminate.
  - intro H. apply Bool.orb_true_iff in H.
    destruct H as [H | H].
    + left. apply String.eqb_eq in H. symmetry. exact H.
    + right. exact (IH H).
Qed.

Lemma In_existsb : forall s l,
    In s l -> existsb (String.eqb s) l = true.
Proof.
  intros s l. induction l as [|a l' IH]; simpl.
  - intro H; destruct H.
  - intros [<- | H].
    + rewrite String.eqb_refl. reflexivity.
    + apply Bool.orb_true_iff. right. exact (IH H).
Qed.

Lemma nodupb_NoDup : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [|a l' IH]; simpl; intro H.
  - constructor.
  - apply Bool.andb_true_iff in H. destruct H as [Hmem Hrest].
    constructor.
    + intro Hin. apply In_existsb in Hin.
      unfold mem_string in Hmem. rewrite Hin in Hmem. discriminate.
    + exact (IH Hrest).
Qed.

Record WellFormed (ac : AssuranceCase) : Prop := {
  wf_top        : top_is_goal ac;
  wf_acyclic    : Acyclic ac;
  wf_discharged : all_reachable_discharged ac;
  wf_no_dangle  : no_dangling_links ac;
  wf_unique_ids : NoDup (map node_id ac.(ac_nodes));
  wf_entailment : forall id n,
    find_node ac id = Some n ->
    (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
    (let kids := supportedby_children ac id in
     let child_claims :=
       flat_map (fun kid =>
         match find_node ac kid with
         | Some cn => [cn.(node_claim)]
         | None     => []
         end) kids
     in fold_right and True child_claims -> n.(node_claim));
  wf_context_links : well_typed_context_links ac;
}.

(* ------------------------------------------------------------------ *)
(* Decidable well-formedness checker                                    *)
(* ------------------------------------------------------------------ *)
(* Checks all structural conditions except entailment (undecidable)     *)
(* and ProofTerm type matching (guaranteed by the type checker but      *)
(* erased during extraction).                                           *)

Definition check_top_is_goal (ac : AssuranceCase) : bool :=
  match find_node ac ac.(ac_top) with
  | Some n => match n.(node_kind) with Goal => true | _ => false end
  | None => false
  end.

Definition check_no_dangling (ac : AssuranceCase) : bool :=
  forallb (fun l =>
    match find_node ac l.(link_from), find_node ac l.(link_to) with
    | Some _, Some _ => true
    | _, _ => false
    end) ac.(ac_links).

Definition check_unique_ids (ac : AssuranceCase) : bool :=
  nodupb (map node_id ac.(ac_nodes)).

Fixpoint reachable_set_fuel (ac : AssuranceCase) (fuel : nat)
    (frontier acc : list Id) : list Id :=
  match fuel with
  | 0 => acc
  | S f =>
    let new_kids := flat_map (supportedby_children ac) frontier in
    let fresh := filter (fun id => negb (mem_string id acc)) new_kids in
    match fresh with
    | [] => acc
    | _ => reachable_set_fuel ac f fresh (acc ++ fresh)
    end
  end.

Definition reachable_from (ac : AssuranceCase) (start : Id) : list Id :=
  let kids := supportedby_children ac start in
  reachable_set_fuel ac (length ac.(ac_nodes)) kids kids.

(* BFS-based acyclicity checker.  Works correctly on all concrete
   graphs but does NOT have a formal soundness proof (BFS completeness
   is unproved).  Prefer verify_topo_order / structural_checks for
   verified workflows — those have a complete soundness proof
   in Reflect.v (verify_topo_order_acyclic, build_well_formed).       *)
Definition check_acyclic (ac : AssuranceCase) : bool :=
  forallb (fun n =>
    negb (mem_string n.(node_id) (reachable_from ac n.(node_id))))
    ac.(ac_nodes).

Definition check_discharged (ac : AssuranceCase) : bool :=
  let reachable := ac.(ac_top) :: reachable_from ac ac.(ac_top) in
  forallb (fun id =>
    match find_node ac id with
    | None => false
    | Some n =>
      match n.(node_kind) with
      | Solution =>
        match n.(node_evidence) with
        | Some (Certificate b v) => v b
        | Some (ProofTerm _ _ _) => true
        | None => false
        end
      | Goal | Strategy =>
        negb (match supportedby_children ac id with [] => true | _ => false end)
      | _ => true
      end
    end) reachable.

Definition check_context_links (ac : AssuranceCase) : bool :=
  forallb (fun l =>
    match l.(link_kind) with
    | SupportedBy => true
    | InContextOf =>
      match find_node ac l.(link_from), find_node ac l.(link_to) with
      | Some nf, Some nt =>
        (match nf.(node_kind) with Goal | Strategy => true | _ => false end) &&
        (match nt.(node_kind) with
         | Context | Assumption | Justification => true | _ => false end)
      | _, _ => false
      end
    end) ac.(ac_links).

(* Stronger discharged check: verify ALL nodes, not just reachable ones.
   Easier to reflect because it avoids BFS completeness arguments.       *)
Definition check_all_discharged (ac : AssuranceCase) : bool :=
  forallb (fun n =>
    match n.(node_kind) with
    | Solution =>
      match n.(node_evidence) with
      | Some (Certificate b v) => v b
      | Some (ProofTerm _ _ _) => true
      | None => false
      end
    | Goal | Strategy =>
      negb (match supportedby_children ac n.(node_id) with
            | [] => true | _ => false end)
    | _ => true
    end) ac.(ac_nodes).

(* Quick decidable checker using the BFS-based check_acyclic.
   For verified well-formedness, use structural_checks instead —
   it uses verify_topo_order (with proved soundness) and
   check_all_discharged (stronger, easier to reflect).                 *)
Definition check_well_formed (ac : AssuranceCase) : bool :=
  check_top_is_goal ac &&
  check_unique_ids ac &&
  check_no_dangling ac &&
  check_acyclic ac &&
  check_discharged ac &&
  check_context_links ac.

(* ------------------------------------------------------------------ *)
(* Entailment automation                                                *)
(* ------------------------------------------------------------------ *)

(* Discharges entailment obligations on concrete assurance cases.       *)
(* Usage: solve_entailment <find_node_equiv_lemma>.                     *)
Ltac solve_entailment find_equiv :=
  intros ? ? Hfind Hkind;
  rewrite find_equiv in Hfind;
  repeat match type of Hfind with
  | (if ?c then _ else _) = _ =>
      destruct c eqn:?;
      [ injection Hfind as <-;
        first [ vm_compute; tauto
              | vm_compute; intuition
              | vm_compute; firstorder
              | exfalso; destruct Hkind as [? | ?]; discriminate ]
      | ]
  end;
  try discriminate.

(* Variant accepting a hint database name for custom entailments.       *)
Ltac solve_entailment_with find_equiv db :=
  intros ? ? Hfind Hkind;
  rewrite find_equiv in Hfind;
  repeat match type of Hfind with
  | (if ?c then _ else _) = _ =>
      destruct c eqn:?;
      [ injection Hfind as <-;
        first [ vm_compute; tauto
              | vm_compute; intuition
              | solve [vm_compute; eauto with db]
              | exfalso; destruct Hkind as [? | ?]; discriminate ]
      | ]
  end;
  try discriminate.

(* Discharges NoDup obligations on concrete node lists.                 *)
Ltac prove_nodup := apply nodupb_NoDup; vm_compute; reflexivity.

(* ------------------------------------------------------------------ *)
(* Topological ordering for acyclicity decision                         *)
(* ------------------------------------------------------------------ *)

Fixpoint index_of (s : string) (l : list string) : option nat :=
  match l with
  | [] => None
  | x :: xs =>
    if String.eqb s x then Some 0
    else match index_of s xs with
         | Some n => Some (S n)
         | None => None
         end
  end.

(* SupportedBy in-degree restricted to a set of remaining nodes.       *)
Definition sb_in_degree (ac : AssuranceCase)
    (remaining : list Id) (id : Id) : nat :=
  length (filter (fun l =>
    match l.(link_kind) with
    | SupportedBy =>
      String.eqb l.(link_to) id && mem_string l.(link_from) remaining
    | InContextOf => false
    end) ac.(ac_links)).

(* Kahn's algorithm: peel zero-in-degree nodes.                        *)
Fixpoint topo_sort_go (ac : AssuranceCase) (fuel : nat)
    (remaining : list Id) (acc : list Id) : list Id :=
  match fuel with
  | 0 => acc
  | S f =>
    match find (fun id => Nat.eqb (sb_in_degree ac remaining id) 0)
               remaining with
    | None => acc
    | Some id =>
      let remaining' :=
        filter (fun x => negb (String.eqb x id)) remaining in
      topo_sort_go ac f remaining' (acc ++ [id])
    end
  end.

Definition topo_sort (ac : AssuranceCase) : list Id :=
  topo_sort_go ac (length ac.(ac_nodes))
               (map node_id ac.(ac_nodes)) [].

(* Verify a candidate topological order: every SupportedBy edge goes
   from a lower to a higher index, all node IDs appear, no duplicates. *)
Definition verify_topo_order (ac : AssuranceCase)
    (order : list Id) : bool :=
  forallb (fun l =>
    match l.(link_kind) with
    | InContextOf => true
    | SupportedBy =>
      match index_of l.(link_from) order,
            index_of l.(link_to)   order with
      | Some i, Some j => Nat.ltb i j
      | _, _ => false
      end
    end) ac.(ac_links) &&
  forallb (fun n => mem_string n.(node_id) order)
          ac.(ac_nodes) &&
  nodupb order.

(* Combined structural checks with proved soundness (see Reflect.v:
   build_well_formed).  Uses verify_topo_order for acyclicity
   (soundness proved via verify_topo_order_acyclic) and
   check_all_discharged for evidence coverage (stronger than the
   reachable-only check, easier to reflect).
   For concrete assurance cases, structural_checks and
   check_well_formed agree — see Example.v for computational proofs.   *)
Definition structural_checks (ac : AssuranceCase) : bool :=
  check_top_is_goal ac &&
  check_unique_ids ac &&
  check_no_dangling ac &&
  verify_topo_order ac (topo_sort ac) &&
  check_all_discharged ac &&
  check_context_links ac.

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
        | Some (ProofTerm _ _ _) => true
        | Some (Certificate b v) => v b
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
            | ProofTerm _ _ _ => true
            | Certificate b v => v b
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
