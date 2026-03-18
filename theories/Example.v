(* ------------------------------------------------------------------ *)
(* 11. Example: requirement -> theorem -> evidence                      *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Main.
From RACK Require Import Export.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Arguments supportedby_children : simpl never.

(* Claim: 2 + 2 = 4, witnessed by a Rocq proof term. *)
Definition ex_claim : Prop := 2 + 2 = 4.
Definition ex_proof : ex_claim := eq_refl.

Definition ex_goal : Node := {|
  node_id := "G1";
  node_kind := Goal;
  node_claim := ex_claim;
  node_evidence := None;
|}.

Definition ex_solution : Node := {|
  node_id := "E1";
  node_kind := Solution;
  node_claim := ex_claim;
  node_evidence := Some (ProofTerm ex_claim ex_proof);
|}.

Definition ex_link : Link := {|
  link_kind := SupportedBy;
  link_from := "G1";
  link_to := "E1";
|}.

Definition ex_ac : AssuranceCase := {|
  ac_nodes := [ex_goal; ex_solution];
  ac_links := [ex_link];
  ac_top := "G1";
|}.

(* — Helpers for the concrete example — *)

Lemma ex_children_equiv : forall u,
    supportedby_children ex_ac u =
    if String.eqb "G1" u then ["E1"] else [].
Proof.
  intro u. unfold supportedby_children, ex_ac, ex_link.
  cbn -[String.eqb]. destruct (String.eqb "G1" u); reflexivity.
Qed.

Lemma ex_find_node_equiv : forall id,
    find_node ex_ac id =
    if String.eqb "G1" id then Some ex_goal
    else if String.eqb "E1" id then Some ex_solution
    else None.
Proof.
  intro id. unfold find_node, ex_ac.
  cbn -[String.eqb]. destruct (String.eqb "G1" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E1" id); reflexivity.
Qed.

Definition ex_rank (id : Id) : nat :=
  if String.eqb "G1" id then 1 else 0.

Lemma ex_rank_decreases : forall u v,
    Reaches ex_ac u v -> ex_rank v < ex_rank u.
Proof.
  intros u v H. induction H as [u v Hstep | u w v H1 IH1 H2 IH2].
  - rewrite ex_children_equiv in Hstep. unfold ex_rank.
    destruct (String.eqb "G1" u) eqn:Heq.
    + destruct Hstep as [<- | []]. simpl. apply Nat.lt_0_succ.
    + destruct Hstep.
  - exact (Nat.lt_trans _ _ _ IH2 IH1).
Qed.

Lemma ex_acyclic : Acyclic ex_ac.
Proof.
  intros id H.
  exact (Nat.lt_irrefl _ (ex_rank_decreases id id H)).
Qed.

Lemma ex_no_reach_from_E1 : forall v, ~ Reaches ex_ac "E1" v.
Proof.
  intros v H.
  exact (Nat.nlt_0_r _ (ex_rank_decreases _ _ H)).
Qed.

Lemma ex_reaches_from_G1 : forall u v,
    Reaches ex_ac u v -> u = "G1" -> v = "E1".
Proof.
  intros u v H. induction H as [u v Hstep | u w v H1 IH1 H2 IH2]; intro Heq; subst.
  - rewrite ex_children_equiv in Hstep. simpl in Hstep.
    destruct Hstep as [<- | []]. reflexivity.
  - assert (w = "E1") by exact (IH1 eq_refl). subst w.
    exfalso. exact (ex_no_reach_from_E1 v H2).
Qed.

(* — Well-formedness proof — *)

Lemma ex_top_is_goal : top_is_goal ex_ac.
Proof. exists ex_goal. split; reflexivity. Qed.

Lemma ex_no_dangle : no_dangling_links ex_ac.
Proof.
  intros l Hin. destruct Hin as [<- | []].
  split; [exists ex_goal | exists ex_solution]; reflexivity.
Qed.

Lemma ex_discharged : all_reachable_discharged ex_ac.
Proof.
  intros id Hreach.
  assert (Hid: id = "G1" \/ id = "E1").
  { destruct Hreach as [-> | H].
    - left; reflexivity.
    - right; exact (ex_reaches_from_G1 _ _ H eq_refl). }
  destruct Hid as [-> | ->]; vm_compute.
  - discriminate.
  - eexists; split; reflexivity.
Qed.

Lemma ex_entailment : forall id n,
    find_node ex_ac id = Some n ->
    (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
    (let kids := supportedby_children ex_ac id in
     let child_claims :=
       flat_map (fun kid =>
         match find_node ex_ac kid with
         | Some cn => [cn.(node_claim)]
         | None     => []
         end) kids
     in fold_right and True child_claims -> n.(node_claim)).
Proof.
  intros id n Hfind Hkind.
  rewrite ex_find_node_equiv in Hfind.
  destruct (String.eqb "G1" id) eqn:Heq1.
  - injection Hfind as <-. vm_compute. tauto.
  - destruct (String.eqb "E1" id) eqn:Heq2.
    + injection Hfind as <-. destruct Hkind as [H | H]; discriminate.
    + discriminate.
Qed.

Definition ex_wf : WellFormed ex_ac :=
  {| wf_top := ex_top_is_goal;
     wf_acyclic := ex_acyclic;
     wf_discharged := ex_discharged;
     wf_no_dangle := ex_no_dangle;
     wf_entailment := ex_entailment |}.

Theorem ex_supported : SupportTree ex_ac "G1".
Proof. exact (assurance_case_supported ex_ac ex_wf). Qed.

(* The example renders to JSON and DOT: *)
(* Eval vm_compute in render_assurance_case ex_ac. *)
(* Eval vm_compute in render_dot ex_ac.             *)

(* ------------------------------------------------------------------ *)
(* 12. Multi-level example: Goal -> Strategy -> 2 Solutions + Context   *)
(* ------------------------------------------------------------------ *)

Definition ml_security_claim : Prop := True.
Definition ml_unit_claim : Prop := 1 = 1.
Definition ml_fuzz_claim : Prop := True.

Definition ml_goal : Node := {|
  node_id := "G-sec";
  node_kind := Goal;
  node_claim := ml_security_claim;
  node_evidence := None;
|}.

Definition ml_strategy : Node := {|
  node_id := "S-test";
  node_kind := Strategy;
  node_claim := ml_security_claim;
  node_evidence := None;
|}.

Definition ml_context : Node := {|
  node_id := "C-scope";
  node_kind := Context;
  node_claim := True;
  node_evidence := None;
|}.

Definition ml_sol_unit : Node := {|
  node_id := "E-unit";
  node_kind := Solution;
  node_claim := ml_unit_claim;
  node_evidence := Some (ProofTerm ml_unit_claim eq_refl);
|}.

Definition ml_sol_fuzz : Node := {|
  node_id := "E-fuzz";
  node_kind := Solution;
  node_claim := ml_fuzz_claim;
  node_evidence := Some (Certificate "PASS:fuzz:2026-03-18" (fun s => String.eqb s "PASS:fuzz:2026-03-18"));
|}.

Definition ml_ac : AssuranceCase := {|
  ac_nodes := [ml_goal; ml_strategy; ml_context; ml_sol_unit; ml_sol_fuzz];
  ac_links := [{| link_kind := SupportedBy; link_from := "G-sec"; link_to := "S-test" |};
               {| link_kind := InContextOf; link_from := "G-sec"; link_to := "C-scope" |};
               {| link_kind := SupportedBy; link_from := "S-test"; link_to := "E-unit" |};
               {| link_kind := SupportedBy; link_from := "S-test"; link_to := "E-fuzz" |}];
  ac_top := "G-sec";
|}.

(* — Helpers for the multi-level example — *)

Lemma ml_children_equiv : forall u,
    supportedby_children ml_ac u =
    if String.eqb "G-sec" u then ["S-test"]
    else if String.eqb "S-test" u then ["E-unit"; "E-fuzz"]
    else [].
Proof.
  intro u. unfold supportedby_children, ml_ac.
  cbn -[String.eqb].
  destruct (String.eqb "G-sec" u) eqn:HG.
  - apply String.eqb_eq in HG. subst u. reflexivity.
  - cbn -[String.eqb].
    destruct (String.eqb "S-test" u) eqn:HS.
    + apply String.eqb_eq in HS. subst u. reflexivity.
    + reflexivity.
Qed.

Lemma ml_find_node_equiv : forall id,
    find_node ml_ac id =
    if String.eqb "G-sec" id then Some ml_goal
    else if String.eqb "S-test" id then Some ml_strategy
    else if String.eqb "C-scope" id then Some ml_context
    else if String.eqb "E-unit" id then Some ml_sol_unit
    else if String.eqb "E-fuzz" id then Some ml_sol_fuzz
    else None.
Proof.
  intro id. unfold find_node, ml_ac.
  cbn -[String.eqb]. destruct (String.eqb "G-sec" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "S-test" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "C-scope" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E-unit" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E-fuzz" id); reflexivity.
Qed.

Definition ml_rank (id : Id) : nat :=
  if String.eqb "G-sec" id then 2
  else if String.eqb "S-test" id then 1
  else 0.

Lemma ml_rank_decreases : forall u v,
    Reaches ml_ac u v -> ml_rank v < ml_rank u.
Proof.
  intros u v H. induction H as [u v Hstep | u w v H1 IH1 H2 IH2].
  - rewrite ml_children_equiv in Hstep. unfold ml_rank.
    destruct (String.eqb "G-sec" u) eqn:HG.
    + destruct Hstep as [<- | []]. simpl. auto.
    + destruct (String.eqb "S-test" u) eqn:HS.
      * destruct Hstep as [<- | [<- | []]]; simpl; auto.
      * destruct Hstep.
  - exact (Nat.lt_trans _ _ _ IH2 IH1).
Qed.

Lemma ml_acyclic : Acyclic ml_ac.
Proof.
  intros id H. exact (Nat.lt_irrefl _ (ml_rank_decreases id id H)).
Qed.

Lemma ml_reaches_from_S_test : forall v,
    Reaches ml_ac "S-test" v -> v = "E-unit" \/ v = "E-fuzz".
Proof.
  intros v H. remember "S-test" as src.
  induction H as [u v Hstep | u w v H1 IH1 H2 IH2]; subst.
  - rewrite ml_children_equiv in Hstep. simpl in Hstep.
    destruct Hstep as [<- | [<- | []]]; [left | right]; reflexivity.
  - destruct (IH1 eq_refl) as [-> | ->];
      exfalso; exact (Nat.nlt_0_r _ (ml_rank_decreases _ _ H2)).
Qed.

Lemma ml_reachable_ids : forall v,
    Reaches ml_ac "G-sec" v -> v = "S-test" \/ v = "E-unit" \/ v = "E-fuzz".
Proof.
  intros v H. remember "G-sec" as src.
  induction H as [u v Hstep | u w v H1 IH1 H2 IH2]; subst.
  - rewrite ml_children_equiv in Hstep. simpl in Hstep.
    destruct Hstep as [<- | []]. left; reflexivity.
  - destruct (IH1 eq_refl) as [-> | [-> | ->]].
    + right; exact (ml_reaches_from_S_test v H2).
    + exfalso; exact (Nat.nlt_0_r _ (ml_rank_decreases _ _ H2)).
    + exfalso; exact (Nat.nlt_0_r _ (ml_rank_decreases _ _ H2)).
Qed.

Lemma ml_top_is_goal : top_is_goal ml_ac.
Proof. exists ml_goal. split; reflexivity. Qed.

Lemma ml_no_dangle : no_dangling_links ml_ac.
Proof.
  intros l Hin. simpl in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    (split; [eexists | eexists]; reflexivity).
Qed.

Lemma ml_discharged : all_reachable_discharged ml_ac.
Proof.
  intros id Hreach.
  assert (Hid: id = "G-sec" \/ id = "S-test" \/ id = "E-unit" \/ id = "E-fuzz").
  { destruct Hreach as [-> | H].
    - left; reflexivity.
    - right; exact (ml_reachable_ids _ H). }
  destruct Hid as [-> | [-> | [-> | ->]]]; vm_compute.
  - discriminate.
  - discriminate.
  - eexists; split; reflexivity.
  - eexists; split; reflexivity.
Qed.

Lemma ml_entailment : forall id n,
    find_node ml_ac id = Some n ->
    (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
    (let kids := supportedby_children ml_ac id in
     let child_claims :=
       flat_map (fun kid =>
         match find_node ml_ac kid with
         | Some cn => [cn.(node_claim)]
         | None     => []
         end) kids
     in fold_right and True child_claims -> n.(node_claim)).
Proof.
  intros id n Hfind Hkind.
  rewrite ml_find_node_equiv in Hfind.
  destruct (String.eqb "G-sec" id) eqn:H1.
  - injection Hfind as <-. vm_compute. tauto.
  - destruct (String.eqb "S-test" id) eqn:H2.
    + injection Hfind as <-. vm_compute. tauto.
    + destruct (String.eqb "C-scope" id) eqn:H3.
      * injection Hfind as <-. destruct Hkind as [H|H]; discriminate.
      * destruct (String.eqb "E-unit" id) eqn:H4.
        -- injection Hfind as <-. destruct Hkind as [H|H]; discriminate.
        -- destruct (String.eqb "E-fuzz" id) eqn:H5.
           ++ injection Hfind as <-. destruct Hkind as [H|H]; discriminate.
           ++ discriminate.
Qed.

Definition ml_wf : WellFormed ml_ac :=
  {| wf_top := ml_top_is_goal;
     wf_acyclic := ml_acyclic;
     wf_discharged := ml_discharged;
     wf_no_dangle := ml_no_dangle;
     wf_entailment := ml_entailment |}.

Theorem ml_supported : SupportTree ml_ac "G-sec".
Proof. exact (assurance_case_supported ml_ac ml_wf). Qed.

(* Eval vm_compute in render_dot ml_ac.             *)
(* Eval vm_compute in render_assurance_case ml_ac.  *)

(* ------------------------------------------------------------------ *)
(* 13. Extraction                                                       *)
(* ------------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.
Extract Inlined Constant Nat.eqb => "(=)".
Extraction "rack" render_assurance_case render_dot
                   assurance_case_to_json render_json
                   signed_to_evidence signed_to_json.
