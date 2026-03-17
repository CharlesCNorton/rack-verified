(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: ITree Case Study                     *)
(*                                                                            *)
(*     RACK assurance case with ITree behavioral refinement as evidence.     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 19, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Core.
From RACK Require Import Main.
From RACK Require Import Reflect.
From RACK Require Import Notation.

From ITree Require Import ITree.
From ITree Require Import Eq.Eqit.

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Arguments supportedby_children : simpl never.

Inductive maxE : Type -> Type :=
  | AskMax : Z -> Z -> maxE Z.

Definition max_spec_itree (a b : Z) : itree maxE Z :=
  Ret (Z.max a b).

Definition max_impl_itree (a b : Z) : itree maxE Z :=
  Ret (Z.max a b).

Lemma max_refines : forall a b,
    eutt eq (max_spec_itree a b) (max_impl_itree a b).
Proof. intros. reflexivity. Qed.

Definition ds_behavioral_claim : Prop :=
  forall a b, eutt eq (max_spec_itree a b) (max_impl_itree a b).

Definition ds_behavioral_proof : ds_behavioral_claim := max_refines.

Definition ds_sol_itree : Node := {|
  node_id         := "DS-itree";
  node_kind       := Solution;
  node_claim_text := "ITree: max behavior refines spec";
  node_evidence   := Some (ProofTerm "max_refines"
                      ds_behavioral_claim ds_behavioral_proof (Some (fun _ => true)));
  node_metadata   := [("tool", MVString "ITree");
                       ("method", MVString "behavioral-refinement")];
  node_claim      := ds_behavioral_claim;
|}.

Definition ds_itree_top : Node :=
  mkGoal "DS-itree-top" "max behavior refines specification"
    [] True.

Definition deepspec_itree_case : AssuranceCase :=
  mkCase "DS-itree-top"
    [ds_itree_top; ds_sol_itree]
    [supports "DS-itree-top" "DS-itree"].

Example deepspec_itree_structural :
  structural_checks deepspec_itree_case = true := eq_refl.

Definition deepspec_itree_wf : WellFormed deepspec_itree_case.
Proof.
  apply build_well_formed; [vm_compute; reflexivity | |].
  - intros id n Hfind Hkind.
    cbv [find_node deepspec_itree_case ac_nodes find
         node_id ds_itree_top ds_sol_itree mkGoal mkCase] in Hfind.
    destruct (String.eqb "DS-itree-top" id) eqn:E1;
      [injection Hfind as <-; exact (fun _ => I) |].
    destruct (String.eqb "DS-itree" id) eqn:E2;
      [injection Hfind as <-; destruct Hkind as [H|H]; discriminate
      | discriminate].
  - intros n e Hin Hkind He.
    destruct Hin as [<- | [<- | []]]; [discriminate |].
    cbv [node_evidence ds_sol_itree] in He.
    injection He as <-. simpl. reflexivity.
Qed.

Theorem deepspec_itree_supported : SupportTree deepspec_itree_case "DS-itree-top".
Proof. exact (assurance_case_supported deepspec_itree_case deepspec_itree_wf). Qed.
