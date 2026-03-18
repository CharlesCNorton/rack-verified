(* ------------------------------------------------------------------ *)
(* Typeclass-based entailment automation and metadata extensions       *)
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
(* Typeclass-based entailment                                          *)
(* ================================================================== *)

(** [Entails children_claims parent_claim] witnesses that the
    conjunction of [children_claims] implies [parent_claim].
    Instances automate common patterns; the user can add more. *)
Class Entails (children : list Prop) (parent : Prop) : Prop :=
  entails_proof : fold_right and True children -> parent.

(** Identity: a single child with the same claim. *)
Global Instance entails_identity (P : Prop) : Entails [P] P.
Proof. intro H. destruct H as [HP _]. exact HP. Defined.

(** Conjunction splitting: parent is P /\ Q, children are [P; Q]. *)
Global Instance entails_conj (P Q : Prop) : Entails [P; Q] (P /\ Q).
Proof.
  intro H. destruct H as [HP [HQ _]]. exact (conj HP HQ).
Defined.

(** Conjunction splitting (3-way). *)
Global Instance entails_conj3 (P Q R : Prop)
  : Entails [P; Q; R] (P /\ Q /\ R).
Proof.
  intro H. destruct H as [HP [HQ [HR _]]].
  exact (conj HP (conj HQ HR)).
Defined.

(** True is trivially entailed by anything. *)
Global Instance entails_true (cs : list Prop) : Entails cs True.
Proof. intro. exact I. Defined.

(** Single-child forwarding: one child entails parent
    when the child implies the parent. *)
Global Instance entails_impl (P Q : Prop) `{P -> Q}
  : Entails [P] Q.
Proof. intro Hcs. destruct Hcs as [HP _]. exact (H HP). Defined.

(** Two-child disjunction: children are [P; Q], parent is P \/ Q. *)
Global Instance entails_disj_l (P Q : Prop) : Entails [P; Q] (P \/ Q).
Proof.
  intro H. destruct H as [HP [HQ _]]. left. exact HP.
Defined.

(* ================================================================== *)
(* Automation tactics using Entails                                    *)
(* ================================================================== *)

(** Solve entailment using typeclass resolution.  For concrete cases
    where the child claims and parent claim are syntactically known,
    this resolves automatically.  Falls back to [vm_compute; tauto]
    for cases that don't match a typeclass instance. *)
Ltac solve_entailment_tc :=
  match goal with
  | |- fold_right and True ?children -> ?parent =>
    first [ exact (entails_proof (children := children) (parent := parent))
          | vm_compute; tauto
          | vm_compute; intuition ]
  end.

(** Full entailment solver for [wf_entailment] obligations.
    Handles the [find_node] dispatch, then uses [solve_entailment_tc]
    for each concrete case. *)
Ltac solve_all_entailments :=
  intros ? ? Hfind Hkind;
  vm_compute in Hfind;
  repeat match type of Hfind with
  | (if ?c then _ else _) = _ =>
      destruct c eqn:?;
      [ injection Hfind as <-;
        first [ solve_entailment_tc
              | vm_compute; tauto
              | vm_compute; intuition
              | vm_compute; firstorder
              | exfalso; destruct Hkind as [? | ?]; discriminate ]
      | ]
  end;
  try discriminate.

(* ================================================================== *)
(* Extended metadata values                                            *)
(* ================================================================== *)

(** Extended metadata supporting nested structures.
    This extends [MetadataValue] without changing it, so existing
    proofs remain intact. *)
Inductive MetadataValueExt : Type :=
  | MVXBase    : MetadataValue -> MetadataValueExt
  | MVXList    : list MetadataValueExt -> MetadataValueExt
  | MVXObj     : list (string * MetadataValueExt) -> MetadataValueExt.

(** Inject base metadata into extended. *)
Definition mvx_string (s : string) : MetadataValueExt :=
  MVXBase (MVString s).
Definition mvx_nat (n : nat) : MetadataValueExt :=
  MVXBase (MVNat n).
Definition mvx_bool (b : bool) : MetadataValueExt :=
  MVXBase (MVBool b).
Definition mvx_timestamp (s : string) : MetadataValueExt :=
  MVXBase (MVTimestamp s).

(** Flatten extended metadata to base (lossy: nested structures
    become empty strings). *)
Fixpoint flatten_mvx (v : MetadataValueExt) : MetadataValue :=
  match v with
  | MVXBase mv => mv
  | MVXList _ => MVString ""
  | MVXObj _ => MVString ""
  end.

(** Extended metadata key lookup. *)
Fixpoint find_metadata_ext (key : string)
    (md : list (string * MetadataValueExt))
  : option MetadataValueExt :=
  match md with
  | [] => None
  | (k, v) :: rest =>
    if String.eqb k key then Some v
    else find_metadata_ext key rest
  end.

(* ================================================================== *)
(* Entailment pattern library                                          *)
(* ================================================================== *)

(** Common entailment patterns as reusable lemmas. *)

(** Weakening: if P entails Q and [P] is among the children,
    then the children entail Q. *)
Lemma entails_weaken : forall (cs : list Prop) (P Q : Prop),
    In P cs ->
    (P -> Q) ->
    fold_right and True cs -> Q.
Proof.
  intros cs P Q Hin Himpl Hcs.
  apply Himpl.
  induction cs as [|c cs' IH].
  - destruct Hin.
  - destruct Hin as [<- | Hin'].
    + exact (proj1 Hcs).
    + exact (IH Hin' (proj2 Hcs)).
Qed.

(** All children are True -> parent is True. *)
Lemma entails_all_true : forall cs,
    fold_right and True cs -> True.
Proof. intros _ _. exact I. Qed.

(** Single child: equivalent to implication. *)
Lemma entails_single : forall P Q,
    (P -> Q) -> fold_right and True [P] -> Q.
Proof. intros P Q H [HP _]. exact (H HP). Qed.

(** Two children: conjunction of both. *)
Lemma entails_pair : forall P Q R,
    (P -> Q -> R) -> fold_right and True [P; Q] -> R.
Proof. intros P Q R H [HP [HQ _]]. exact (H HP HQ). Qed.

(* ================================================================== *)
(* N-ary conjunction Entails instance                                 *)
(* ================================================================== *)

(** Right-nested conjunction without trailing True.
    [conj_all [P; Q; R]] = [P /\ Q /\ R]. *)
Fixpoint conj_all (ps : list Prop) : Prop :=
  match ps with
  | [] => True
  | [P] => P
  | P :: rest => P /\ conj_all rest
  end.

Lemma fold_and_to_conj_all : forall ps,
    fold_right and True ps -> conj_all ps.
Proof.
  induction ps as [|P rest IH].
  - intros; exact I.
  - destruct rest as [|Q rest'].
    + intro H. exact (proj1 H).
    + intro H. split.
      * exact (proj1 H).
      * exact (IH (proj2 H)).
Qed.

Lemma conj_all_to_fold_and : forall ps,
    conj_all ps -> fold_right and True ps.
Proof.
  induction ps as [|P rest IH].
  - intros; exact I.
  - destruct rest as [|Q rest'].
    + intro HP. exact (conj HP I).
    + intros [HP Hrest]. exact (conj HP (IH Hrest)).
Qed.

(** General n-ary conjunction instance.  Fires when the goal
    is [conj_all cs] and the children are [cs]. *)
Global Instance entails_conj_all (ps : list Prop)
  : Entails ps (conj_all ps).
Proof. intro H. exact (fold_and_to_conj_all ps H). Defined.

(** 4-way conjunction. *)
Global Instance entails_conj4 (P Q R S : Prop)
  : Entails [P; Q; R; S] (P /\ Q /\ R /\ S).
Proof.
  intro H. destruct H as [HP [HQ [HR [HS _]]]].
  exact (conj HP (conj HQ (conj HR HS))).
Defined.

(** 5-way conjunction. *)
Global Instance entails_conj5 (P Q R S T : Prop)
  : Entails [P; Q; R; S; T] (P /\ Q /\ R /\ S /\ T).
Proof.
  intro H. destruct H as [HP [HQ [HR [HS [HT _]]]]].
  exact (conj HP (conj HQ (conj HR (conj HS HT)))).
Defined.

(* ================================================================== *)
(* Hint Extern for broader Entails resolution                         *)
(* ================================================================== *)

(** When no typeclass instance fires, fall back to [vm_compute; tauto]. *)
Global Hint Extern 10 (Entails _ _) =>
  intro; vm_compute; tauto : typeclass_instances.

(* ================================================================== *)
(* Hint database for domain-specific entailments                      *)
(* ================================================================== *)

(** [rack_entail] is a dedicated hint database for entailment lemmas.
    Users register domain-specific entailment facts here so the
    automation picks them up without modifying the core tactics.

    Usage:
      Hint Resolve my_domain_lemma : rack_entail.
      (* Then solve_entailment_db fires automatically. *)
*)
Create HintDb rack_entail.

(** Solver using the hint database. *)
Ltac solve_entailment_db :=
  match goal with
  | |- fold_right and True ?children -> ?parent =>
    first [ exact (entails_proof (children := children) (parent := parent))
          | intro; eauto with rack_entail
          | vm_compute; tauto
          | vm_compute; intuition
          | vm_compute; firstorder ]
  end.

(** Full wf_entailment solver with hint database support. *)
Ltac solve_all_entailments_db :=
  intros ? ? Hfind Hkind;
  vm_compute in Hfind;
  repeat match type of Hfind with
  | (if ?c then _ else _) = _ =>
      destruct c eqn:?;
      [ injection Hfind as <-;
        first [ solve_entailment_db
              | vm_compute; tauto
              | vm_compute; intuition
              | vm_compute; firstorder
              | exfalso; destruct Hkind as [? | ?]; discriminate ]
      | ]
  end;
  try discriminate.

(** Register standard entailment patterns in the hint database. *)
Global Hint Resolve entails_identity : rack_entail.
Global Hint Resolve entails_conj : rack_entail.
Global Hint Resolve entails_conj3 : rack_entail.
Global Hint Resolve entails_conj4 : rack_entail.
Global Hint Resolve entails_conj5 : rack_entail.
Global Hint Resolve entails_true : rack_entail.
Global Hint Resolve entails_conj_all : rack_entail.

(* ================================================================== *)
(* Reflection-based partial decision procedure                        *)
(* ================================================================== *)

(** For entailments where all children are propositionally equal to
    the parent, decide by syntactic identity.  This handles the
    common case of pass-through claims without vm_compute. *)
Ltac solve_entailment_reflect :=
  match goal with
  | |- fold_right and True ?children -> ?parent =>
    let rec try_children cs :=
      match cs with
      | ?P :: ?rest =>
        first [ unify P parent; exact (entails_identity parent)
              | try_children rest ]
      | _ => fail
      end
    in
    first [ try_children children
          | solve_entailment_db ]
  end.
