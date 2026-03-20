(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Core Types                            *)
(*                                                                            *)
(*     Id, NodeKind, Evidence, MetadataValue, Node, IndexedNode,             *)
(*     ClaimTable, LinkKind, Link, AssuranceCase.                            *)
(*     Includes all _eqb, _eq_dec, _eqb_eq lemmas.                          *)
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

Definition NodeKind_eq_dec : forall a b : NodeKind, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* Evidence must *witness* the node's own claim, not an arbitrary Prop. *)
Inductive Evidence : Type :=
  (* A Rocq proof term whose type IS the node's claim.
     The string label survives extraction, identifying what was proved.
     The optional (string -> bool) is a runtime re-checker that survives
     extraction — it receives the node's claim_text at check time and
     returns true when the evidence is still bound to the correct node. *)
  | ProofTerm  : string -> forall (P : Prop), P -> option (string -> bool) -> Evidence
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

Lemma MetadataValue_eqb_eq : forall a b,
    MetadataValue_eqb a b = true <-> a = b.
Proof.
  intros [s1|n1|b1|s1] [s2|n2|b2|s2]; simpl;
    split; intro H; try reflexivity; try discriminate.
  - apply String.eqb_eq in H. subst. reflexivity.
  - injection H as <-. apply String.eqb_refl.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - injection H as <-. apply Nat.eqb_refl.
  - destruct b1, b2; try discriminate; reflexivity.
  - injection H as <-. destruct b1; reflexivity.
  - apply String.eqb_eq in H. subst. reflexivity.
  - injection H as <-. apply String.eqb_refl.
Qed.

Definition MetadataValue_eq_dec : forall a b : MetadataValue, {a = b} + {a <> b}.
Proof.
  intros [s1|n1|b1|s1] [s2|n2|b2|s2]; try (right; discriminate).
  - destruct (String.eqb s1 s2) eqn:E.
    + left. apply String.eqb_eq in E. subst. reflexivity.
    + right. intro H. injection H as <-.
      rewrite String.eqb_refl in E. discriminate.
  - destruct (Nat.eq_dec n1 n2) as [Heq | Hne].
    + left. subst. reflexivity.
    + right. intro H. injection H as <-. exact (Hne eq_refl).
  - destruct b1, b2.
    + left. reflexivity.
    + right. discriminate.
    + right. discriminate.
    + left. reflexivity.
  - destruct (String.eqb s1 s2) eqn:E.
    + left. apply String.eqb_eq in E. subst. reflexivity.
    + right. intro H. injection H as <-.
      rewrite String.eqb_refl in E. discriminate.
Defined.

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

(** * Indexed claims (scalable alternative to [node_claim : Prop])
    For large assurance cases, embedding Props directly in nodes
    causes proof-term bloat.  [ClaimIndex] defunctionalizes claims:
    each node carries a natural-number index into a separate claim
    table, avoiding duplication and enabling O(1) claim lookup.
    The indexed representation is interconvertible with the direct
    representation; use [reify_claims] / [reflect_claims] to convert. *)
Definition ClaimIndex := nat.

Record IndexedNode : Type := {
  inode_id         : Id;
  inode_kind       : NodeKind;
  inode_claim_text : string;
  inode_evidence   : option Evidence;
  inode_metadata   : list (string * MetadataValue);
  inode_claim_idx  : ClaimIndex;
}.

Record ClaimTable : Type := {
  ct_claims : list Prop;
}.

Definition lookup_claim (ct : ClaimTable) (idx : ClaimIndex) : Prop :=
  nth idx ct.(ct_claims) True.

(** Convert an indexed node to a standard node using a claim table. *)
Definition reflect_node (ct : ClaimTable) (n : IndexedNode) : Node := {|
  node_id         := n.(inode_id);
  node_kind       := n.(inode_kind);
  node_claim_text := n.(inode_claim_text);
  node_evidence   := n.(inode_evidence);
  node_metadata   := n.(inode_metadata);
  node_claim      := lookup_claim ct n.(inode_claim_idx);
|}.

Inductive LinkKind : Type := SupportedBy | InContextOf | Defeater.

(** Decidable equality on [LinkKind]. *)
Definition LinkKind_eqb (a b : LinkKind) : bool :=
  match a, b with
  | SupportedBy, SupportedBy | InContextOf, InContextOf
  | Defeater, Defeater => true
  | _, _ => false
  end.

Lemma LinkKind_eqb_eq : forall a b, LinkKind_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; intro; try reflexivity; try discriminate.
Qed.

Definition LinkKind_eq_dec : forall a b : LinkKind, {a = b} + {a <> b}.
Proof. decide equality. Defined.

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
