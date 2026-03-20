(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Well-Formedness                       *)
(*                                                                            *)
(*     SupportTree, WellFormed record, decidable checkers,                   *)
(*     entailment Ltacs.                                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 17, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Types.
From RACK Require Import Graph.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

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

Definition well_typed_defeater_links (ac : AssuranceCase) : Prop :=
  forall l,
    In l ac.(ac_links) ->
    l.(link_kind) = Defeater ->
    exists nt,
      find_node ac l.(link_to) = Some nt /\
      (nt.(node_kind) = Goal \/ nt.(node_kind) = Strategy).

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
  wf_defeater_links : well_typed_defeater_links ac;
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
    | Defeater =>
      match find_node ac l.(link_to) with
      | Some nt =>
        match nt.(node_kind) with Goal | Strategy => true | _ => false end
      | None => false
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
      | Some (ProofTerm _ _ _ (Some f)) => f n.(node_claim_text)
      | Some (ProofTerm _ _ _ None) => false
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
