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
(* 1. Core types                                                        *)
(* ------------------------------------------------------------------ *)

Definition Id := string.

Inductive NodeKind : Type :=
  | Goal | Strategy | Solution | Context | Assumption | Justification.

(* Evidence must *witness* the node's own claim, not an arbitrary Prop. *)
Inductive Evidence : Type :=
  (* A Rocq proof term whose type IS the node's claim — no cheating *)
  | ProofTerm  : forall (P : Prop), P -> Evidence
  (* External certificate: a raw blob plus a decidable validator              *)
  (* (e.g., a SAW/Kani result with a signature check)                        *)
  | Certificate : string -> (string -> bool) -> Evidence.

Record Node : Type := {
  node_id       : Id;
  node_kind     : NodeKind;
  node_claim    : Prop;
  node_evidence : option Evidence;
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
(* 2. Graph operations                                                  *)
(* ------------------------------------------------------------------ *)

Definition find_node (ac : AssuranceCase) (id : Id) : option Node :=
  find (fun n => String.eqb n.(node_id) id) ac.(ac_nodes).

Definition supportedby_children (ac : AssuranceCase) (id : Id) : list Id :=
  map link_to
    (filter (fun l => andb
               (String.eqb l.(link_from) id)
               (match l.(link_kind) with SupportedBy => true | _ => false end))
            ac.(ac_links)).

(* ------------------------------------------------------------------ *)
(* 3. Reachability and acyclicity                                       *)
(* ------------------------------------------------------------------ *)

Inductive Reaches (ac : AssuranceCase) : Id -> Id -> Prop :=
  | R_Step  : forall u v,
      In v (supportedby_children ac u) -> Reaches ac u v
  | R_Trans : forall u w v,
      Reaches ac u w -> Reaches ac w v -> Reaches ac u v.

Definition Acyclic (ac : AssuranceCase) : Prop :=
  forall id, ~ Reaches ac id id.

(* ------------------------------------------------------------------ *)
(* 4. Evidence validity                                                 *)
(* ------------------------------------------------------------------ *)

(* Evidence is valid for a node only if it discharges THAT node's claim. *)
Definition evidence_valid (n : Node) (e : Evidence) : Prop :=
  match e with
  | ProofTerm P _   => P = n.(node_claim)   (* proof type must match claim *)
  | Certificate b v => v b = true            (* validator accepts the blob  *)
  end.

(* A Solution is discharged iff it carries valid evidence. *)
Definition solution_discharged (n : Node) : Prop :=
  n.(node_kind) = Solution ->
  exists e,
    n.(node_evidence) = Some e /\
    evidence_valid n e.

(* ------------------------------------------------------------------ *)
(* 5. Support tree — the central inductive witness                      *)
(* ------------------------------------------------------------------ *)

(* A SupportTree for node [id] is a proof-relevant object:             *)
(*  - Leaf case: the node is a Solution with valid evidence.            *)
(*  - Internal case: the node has ≥1 SupportedBy child, and EVERY      *)
(*    child has its own SupportTree (all branches must close).          *)
(*    We also require that children's claims ENTAIL the parent's claim  *)
(*    (captured by the [entailment] hypothesis), so the tree is not     *)
(*    merely structurally complete but logically sound.                  *)

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
      (* Every child closes *)
      (forall kid, In kid kids -> SupportTree ac kid) ->
      (* Children's claims jointly entail the parent's claim            *)
      (* (For ProofTerm leaves this is checkable; for mixed trees it is *)
      (*  an explicit logical obligation left to the case author.)       *)
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
(* 6. Well-formedness                                                   *)
(* ------------------------------------------------------------------ *)

Definition top_is_goal (ac : AssuranceCase) : Prop :=
  exists n,
    find_node ac ac.(ac_top) = Some n /\
    n.(node_kind) = Goal.

(* Every node reachable from the top goal is either                    *)
(*  (a) a Solution with valid evidence, or                             *)
(*  (b) a Goal/Strategy with at least one SupportedBy child.           *)
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
      | _ => True  (* Context, Assumption, Justification carry no obligation *)
      end
    end.

(* No dangling links: every link endpoint names a real node. *)
Definition no_dangling_links (ac : AssuranceCase) : Prop :=
  forall l,
    In l ac.(ac_links) ->
    (exists n, find_node ac l.(link_from) = Some n) /\
    (exists n, find_node ac l.(link_to)   = Some n).

Record WellFormed (ac : AssuranceCase) : Prop := {
  wf_top        : top_is_goal ac;
  wf_acyclic    : Acyclic ac;
  wf_discharged : all_reachable_discharged ac;
  wf_no_dangle  : no_dangling_links ac;
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
}.
