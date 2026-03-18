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
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* Core types                                                           *)
(* ------------------------------------------------------------------ *)

Definition Id := string.

(** * Node kinds
    The six GSN node kinds.  [Goal] and [Strategy] are internal
    (must have children); [Solution] is a leaf (must carry evidence);
    [Context], [Assumption], and [Justification] are annotations. *)
Inductive NodeKind : Type :=
  | Goal | Strategy | Solution | Context | Assumption | Justification.

(** Decidable equality on [NodeKind]. *)
Definition NodeKind_eqb (a b : NodeKind) : bool :=
  match a, b with
  | Goal, Goal | Strategy, Strategy | Solution, Solution
  | Context, Context | Assumption, Assumption
  | Justification, Justification => true
  | _, _ => false
  end.

Lemma NodeKind_eqb_refl : forall k, NodeKind_eqb k k = true.
Proof. destruct k; reflexivity. Qed.

Lemma NodeKind_eqb_eq : forall a b, NodeKind_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; intro; try reflexivity; try discriminate. Qed.

(* Evidence must *witness* the node's own claim, not an arbitrary Prop. *)
Inductive Evidence : Type :=
  (* A Rocq proof term whose type IS the node's claim.
     The string label survives extraction, identifying what was proved.
     The optional (unit -> bool) is a runtime re-checker that survives
     extraction — call it to re-verify validity without the erased proof. *)
  | ProofTerm  : string -> forall (P : Prop), P -> option (unit -> bool) -> Evidence
  (* External certificate: raw blob, tool identifier, decidable validator.
     tool_id names the originating tool (e.g. "SAW", "CBMC", "fuzz")
     so the extracted code can dispatch to the right FFI validator.       *)
  | Certificate : string -> string -> (string -> bool) -> Evidence.

(** * Typed metadata values
    Structured representation replacing raw string pairs.
    [MVString] is the catch-all; [MVNat], [MVBool], and [MVTimestamp]
    carry semantic intent that survives extraction and enables
    validated accessors and policy checks. *)
Inductive MetadataValue : Type :=
  | MVString    : string -> MetadataValue
  | MVNat       : nat -> MetadataValue
  | MVBool      : bool -> MetadataValue
  | MVTimestamp : string -> MetadataValue.

Definition MetadataValue_eqb (a b : MetadataValue) : bool :=
  match a, b with
  | MVString s1, MVString s2 => String.eqb s1 s2
  | MVNat n1, MVNat n2 => Nat.eqb n1 n2
  | MVBool b1, MVBool b2 => Bool.eqb b1 b2
  | MVTimestamp s1, MVTimestamp s2 => String.eqb s1 s2
  | _, _ => false
  end.

(** Extract the string content from any [MetadataValue]. *)
Definition mv_as_string (v : MetadataValue) : string :=
  match v with
  | MVString s    => s
  | MVTimestamp s => s
  | MVNat _       => ""
  | MVBool true   => "true"
  | MVBool false  => "false"
  end.

(** * Nodes *)
Record Node : Type := {
  node_id         : Id;
  node_kind       : NodeKind;
  node_claim_text : string;   (* human-readable claim — survives extraction *)
  node_evidence   : option Evidence;
  node_metadata   : list (string * MetadataValue);
  node_claim      : Prop;     (* logical claim — erased at extraction *)
}.

Inductive LinkKind : Type := SupportedBy | InContextOf.

(** Decidable equality on [LinkKind]. *)
Definition LinkKind_eqb (a b : LinkKind) : bool :=
  match a, b with
  | SupportedBy, SupportedBy | InContextOf, InContextOf => true
  | _, _ => false
  end.

Lemma LinkKind_eqb_eq : forall a b, LinkKind_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; intro; try reflexivity; try discriminate. Qed.

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

(* Runtime re-check: call the optional thunk if present.
   Returns true for ProofTerm without a runtime checker (trust the type
   system), true for Certificate if the validator passes, false otherwise.
   Survives extraction — use this in CI gates and audit tooling.           *)
Definition evidence_runtime_check (e : Evidence) : bool :=
  match e with
  | ProofTerm _ _ _ (Some f) => f tt
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
        | Some (Certificate b _ v) => v b
        | Some (ProofTerm _ _ _ _) => true
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
      | Some (Certificate b _ v) => v b
      | Some (ProofTerm _ _ _ _) => true
      | None => false
      end
    | Goal | Strategy =>
      negb (match supportedby_children ac n.(node_id) with
            | [] => true | _ => false end)
    | _ => true
    end) ac.(ac_nodes).

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

(** [check_well_formed] is now a synonym for [structural_checks].
    The former BFS-based acyclicity checker ([check_acyclic]) is
    retained as a utility but no longer on the main verification path.
    All soundness proofs go through [verify_topo_order]. *)
Definition check_well_formed (ac : AssuranceCase) : bool :=
  structural_checks ac.

(* ------------------------------------------------------------------ *)
(* Identity entailment checker (partial decision procedure)             *)
(* ------------------------------------------------------------------ *)

(** Check whether every child claim of a Goal/Strategy node is
    propositionally identical to the parent claim.  When true, the
    entailment obligation is trivially dischargeable.  Returns false
    conservatively — a false result does NOT mean entailment fails. *)
Definition check_identity_entailment_node (ac : AssuranceCase)
    (n : Node) : bool :=
  match n.(node_kind) with
  | Goal | Strategy =>
    let kids := supportedby_children ac n.(node_id) in
    forallb (fun kid =>
      match find_node ac kid with
      | Some cn =>
        (* We can only compare claim_text since node_claim is a Prop *)
        String.eqb cn.(node_claim_text) n.(node_claim_text)
      | None => false
      end) kids
  | _ => true
  end.

Definition check_identity_entailment (ac : AssuranceCase) : bool :=
  forallb (check_identity_entailment_node ac) ac.(ac_nodes).

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
    Returns true if [a] is strictly before [b].  Only valid for
    same-length date strings in YYYY-MM-DD or ISO 8601 format. *)
Fixpoint string_ltb (a b : string) : bool :=
  match a, b with
  | EmptyString, String _ _ => true
  | _, EmptyString => false
  | String ca ra, String cb rb =>
    let na := nat_of_ascii_core ca in
    let nb := nat_of_ascii_core cb in
    if Nat.ltb na nb then true
    else if Nat.ltb nb na then false
    else string_ltb ra rb
  end.

(** Basic ISO 8601 date format check: exactly 10 characters,
    digits at positions 0-3, 5-6, 8-9, hyphens at 4, 7. *)
Definition is_digit_ascii (c : ascii) : bool :=
  let n := nat_of_ascii_core c in
  Nat.leb 48 n && Nat.leb n 57.

Definition is_hyphen_ascii (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii_core c) 45.

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
    is_digit_ascii c8 && is_digit_ascii c9
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
        | Some (ProofTerm _ _ _ _) => true
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
            | ProofTerm _ _ _ _ => true
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
  | ErrMalformedTimestamp : Id -> string -> CheckError. (* node id, bad value *)

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
      | Some (ProofTerm _ _ _ _) => []
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

Definition diagnose_all (ac : AssuranceCase) : list CheckError :=
  diagnose_top ac ++
  diagnose_dangling ac ++
  diagnose_unique_ids ac ++
  diagnose_discharged ac ++
  diagnose_context_links ac ++
  diagnose_acyclic ac.

(** Diagnostic function that mirrors [structural_checks] exactly.
    Uses [check_all_discharged] (all-nodes) rather than
    [check_discharged] (reachable-only), and the topo-order
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
      | Some (ProofTerm _ _ _ _) => []
      | Some (Certificate b _ v) =>
        if v b then [] else [ErrInvalidEvidence n.(node_id)]
      end
    | _ => []
    end) ac.(ac_nodes)) ++
  diagnose_context_links ac.

(* ------------------------------------------------------------------ *)
(* Metadata validation diagnostics                                      *)
(* ------------------------------------------------------------------ *)

(** Diagnose expired evidence: nodes whose [valid_until] timestamp
    is lexicographically before the given [cutoff]. *)
Definition diagnose_metadata_expiry (ac : AssuranceCase)
    (cutoff : string) : list CheckError :=
  flat_map (fun n =>
    match find_metadata "valid_until" n.(node_metadata) with
    | Some (MVTimestamp expiry) =>
      if string_ltb expiry cutoff then [ErrExpiredEvidence n.(node_id) expiry]
      else []
    | Some (MVString expiry) =>
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

(** Diagnose malformed timestamps: [MVTimestamp] values that fail
    the basic YYYY-MM-DD format check. *)
Definition diagnose_malformed_timestamps (ac : AssuranceCase)
    : list CheckError :=
  flat_map (fun n =>
    flat_map (fun kv =>
      match snd kv with
      | MVTimestamp s =>
        if check_date_format s then []
        else [ErrMalformedTimestamp n.(node_id) s]
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
      | Some (ProofTerm _ _ _ _) => true
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
      | Some (ProofTerm _ _ _ _) => []
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

(* ------------------------------------------------------------------ *)
(* Validator registries (for FFI bridging after extraction)              *)
(* ------------------------------------------------------------------ *)

(* A ValidatorEntry maps a tool identifier to a validator function.
   After extraction, the validator is an OCaml (string -> bool) that
   can call real crypto libraries.                                      *)
Record ValidatorEntry : Type := {
  ve_tool      : string;
  ve_validator : string -> bool;
}.

Definition ValidatorRegistry := list ValidatorEntry.

Fixpoint registry_lookup (tool : string) (reg : ValidatorRegistry)
  : option (string -> bool) :=
  match reg with
  | [] => None
  | entry :: rest =>
    if String.eqb entry.(ve_tool) tool
    then Some entry.(ve_validator)
    else registry_lookup tool rest
  end.

(* Build Certificate evidence from a registry lookup.                   *)
Definition make_certificate (tool blob : string) (reg : ValidatorRegistry)
  : option Evidence :=
  match registry_lookup tool reg with
  | Some v => Some (Certificate blob tool v)
  | None => None
  end.
