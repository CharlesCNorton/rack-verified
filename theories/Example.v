(* ------------------------------------------------------------------ *)
(* Examples: requirement -> theorem -> evidence                         *)
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

(* ================================================================== *)
(* Example 1: simple Goal -> Solution with ProofTerm                   *)
(* ================================================================== *)

Definition ex_claim : Prop := 2 + 2 = 4.
Definition ex_proof : ex_claim := eq_refl.

Definition ex_goal : Node := {|
  node_id := "G1";
  node_kind := Goal;
  node_claim := ex_claim;
  node_claim_text := "2 + 2 = 4";
  node_evidence := None;
|}.

Definition ex_solution : Node := {|
  node_id := "E1";
  node_kind := Solution;
  node_claim := ex_claim;
  node_claim_text := "2 + 2 = 4";
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

(* — Helpers — *)

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

(* — Well-formedness — *)

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
Proof. solve_entailment ex_find_node_equiv. Qed.

Definition ex_wf : WellFormed ex_ac :=
  {| wf_top := ex_top_is_goal;
     wf_acyclic := ex_acyclic;
     wf_discharged := ex_discharged;
     wf_no_dangle := ex_no_dangle;
     wf_unique_ids := ltac:(prove_nodup);
     wf_entailment := ex_entailment |}.

Theorem ex_supported : SupportTree ex_ac "G1".
Proof. exact (assurance_case_supported ex_ac ex_wf). Qed.

Example ex_check : check_well_formed ex_ac = true := eq_refl.

(* ================================================================== *)
(* Example 2: Goal -> Strategy -> 2 Solutions + Context                 *)
(* ================================================================== *)

Definition ml_security_claim : Prop := True.
Definition ml_unit_claim : Prop := 1 = 1.
Definition ml_fuzz_claim : Prop := True.

Definition ml_goal : Node := {|
  node_id := "G-sec";
  node_kind := Goal;
  node_claim := ml_security_claim;
  node_claim_text := "System meets security requirements";
  node_evidence := None;
|}.

Definition ml_strategy : Node := {|
  node_id := "S-test";
  node_kind := Strategy;
  node_claim := ml_security_claim;
  node_claim_text := "Argue via unit tests and fuzz testing";
  node_evidence := None;
|}.

Definition ml_context : Node := {|
  node_id := "C-scope";
  node_kind := Context;
  node_claim := True;
  node_claim_text := "Scope: public-facing HTTP endpoints";
  node_evidence := None;
|}.

Definition ml_sol_unit : Node := {|
  node_id := "E-unit";
  node_kind := Solution;
  node_claim := ml_unit_claim;
  node_claim_text := "Unit test suite passes (1 = 1)";
  node_evidence := Some (ProofTerm ml_unit_claim eq_refl);
|}.

Definition ml_sol_fuzz : Node := {|
  node_id := "E-fuzz";
  node_kind := Solution;
  node_claim := ml_fuzz_claim;
  node_claim_text := "Fuzz testing passed (external certificate)";
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

(* — Helpers — *)

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

(* — Well-formedness — *)

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
Proof. solve_entailment ml_find_node_equiv. Qed.

Definition ml_wf : WellFormed ml_ac :=
  {| wf_top := ml_top_is_goal;
     wf_acyclic := ml_acyclic;
     wf_discharged := ml_discharged;
     wf_no_dangle := ml_no_dangle;
     wf_unique_ids := ltac:(prove_nodup);
     wf_entailment := ml_entailment |}.

Theorem ml_supported : SupportTree ml_ac "G-sec".
Proof. exact (assurance_case_supported ml_ac ml_wf). Qed.

Example ml_check : check_well_formed ml_ac = true := eq_refl.

(* ================================================================== *)
(* Example 3: signed evidence blob (external tool result)              *)
(* ================================================================== *)

(* Simulate a SAW verification result with signature check. *)
Definition saw_payload : string := "SAW:verified:buffer_overflow_free:2026-03-18".
Definition saw_signature : string := "hmac-sha256:a1b2c3d4".

Definition saw_verify (payload sig_ : string) : bool :=
  String.eqb payload "SAW:verified:buffer_overflow_free:2026-03-18" &&
  String.eqb sig_ "hmac-sha256:a1b2c3d4".

Definition saw_blob : SignedBlob := {|
  sb_payload := saw_payload;
  sb_signature := saw_signature;
  sb_verify := saw_verify;
|}.

Lemma saw_blob_valid : signed_blob_valid saw_blob.
Proof. vm_compute. reflexivity. Qed.

(* Wire the signed blob into a small assurance case. *)
Definition sb_claim : Prop := True.

Definition sb_goal : Node := {|
  node_id := "G-safe";
  node_kind := Goal;
  node_claim := sb_claim;
  node_claim_text := "System is free of buffer overflows";
  node_evidence := None;
|}.

Definition sb_solution : Node := {|
  node_id := "E-saw";
  node_kind := Solution;
  node_claim := sb_claim;
  node_claim_text := "SAW verified: no buffer overflows";
  node_evidence := Some (signed_to_evidence saw_blob);
|}.

Definition sb_link : Link := {|
  link_kind := SupportedBy;
  link_from := "G-safe";
  link_to := "E-saw";
|}.

Definition sb_ac : AssuranceCase := {|
  ac_nodes := [sb_goal; sb_solution];
  ac_links := [sb_link];
  ac_top := "G-safe";
|}.

Lemma sb_evidence_valid : evidence_valid sb_solution (signed_to_evidence saw_blob).
Proof. exact (signed_evidence_valid saw_blob sb_solution saw_blob_valid). Qed.

(* — Helpers — *)

Lemma sb_children_equiv : forall u,
    supportedby_children sb_ac u =
    if String.eqb "G-safe" u then ["E-saw"] else [].
Proof.
  intro u. unfold supportedby_children, sb_ac, sb_link.
  cbn -[String.eqb]. destruct (String.eqb "G-safe" u); reflexivity.
Qed.

Lemma sb_find_node_equiv : forall id,
    find_node sb_ac id =
    if String.eqb "G-safe" id then Some sb_goal
    else if String.eqb "E-saw" id then Some sb_solution
    else None.
Proof.
  intro id. unfold find_node, sb_ac.
  cbn -[String.eqb]. destruct (String.eqb "G-safe" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E-saw" id); reflexivity.
Qed.

Definition sb_rank (id : Id) : nat :=
  if String.eqb "G-safe" id then 1 else 0.

Lemma sb_rank_decreases : forall u v,
    Reaches sb_ac u v -> sb_rank v < sb_rank u.
Proof.
  intros u v H. induction H as [u v Hstep | u w v H1 IH1 H2 IH2].
  - rewrite sb_children_equiv in Hstep. unfold sb_rank.
    destruct (String.eqb "G-safe" u) eqn:Heq.
    + destruct Hstep as [<- | []]. simpl. apply Nat.lt_0_succ.
    + destruct Hstep.
  - exact (Nat.lt_trans _ _ _ IH2 IH1).
Qed.

Lemma sb_acyclic : Acyclic sb_ac.
Proof.
  intros id H. exact (Nat.lt_irrefl _ (sb_rank_decreases id id H)).
Qed.

Lemma sb_reaches_from_G : forall u v,
    Reaches sb_ac u v -> u = "G-safe" -> v = "E-saw".
Proof.
  intros u v H. induction H as [u v Hstep | u w v H1 IH1 H2 IH2]; intro Heq; subst.
  - rewrite sb_children_equiv in Hstep. simpl in Hstep.
    destruct Hstep as [<- | []]. reflexivity.
  - assert (w = "E-saw") by exact (IH1 eq_refl). subst w.
    exfalso. exact (Nat.nlt_0_r _ (sb_rank_decreases _ _ H2)).
Qed.

(* — Well-formedness — *)

Lemma sb_top_is_goal : top_is_goal sb_ac.
Proof. exists sb_goal. split; reflexivity. Qed.

Lemma sb_no_dangle : no_dangling_links sb_ac.
Proof.
  intros l Hin. destruct Hin as [<- | []].
  split; [exists sb_goal | exists sb_solution]; reflexivity.
Qed.

Lemma sb_discharged : all_reachable_discharged sb_ac.
Proof.
  intros id Hreach.
  assert (Hid: id = "G-safe" \/ id = "E-saw").
  { destruct Hreach as [-> | H].
    - left; reflexivity.
    - right; exact (sb_reaches_from_G _ _ H eq_refl). }
  destruct Hid as [-> | ->]; vm_compute.
  - discriminate.
  - eexists; split; reflexivity.
Qed.

Lemma sb_entailment : forall id n,
    find_node sb_ac id = Some n ->
    (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
    (let kids := supportedby_children sb_ac id in
     let child_claims :=
       flat_map (fun kid =>
         match find_node sb_ac kid with
         | Some cn => [cn.(node_claim)]
         | None     => []
         end) kids
     in fold_right and True child_claims -> n.(node_claim)).
Proof. solve_entailment sb_find_node_equiv. Qed.

Definition sb_wf : WellFormed sb_ac :=
  {| wf_top := sb_top_is_goal;
     wf_acyclic := sb_acyclic;
     wf_discharged := sb_discharged;
     wf_no_dangle := sb_no_dangle;
     wf_unique_ids := ltac:(prove_nodup);
     wf_entailment := sb_entailment |}.

Theorem sb_supported : SupportTree sb_ac "G-safe".
Proof. exact (assurance_case_supported sb_ac sb_wf). Qed.

Example sb_check : check_well_formed sb_ac = true := eq_refl.

(* The signed blob also serializes cleanly: *)
(* Eval vm_compute in signed_to_json saw_blob. *)

(* ================================================================== *)
(* Extraction                                                           *)
(* ================================================================== *)

Require Extraction.
Extraction Language OCaml.
Extract Inlined Constant Nat.eqb => "(=)".
Extraction "rack" render_assurance_case render_assurance_case_pretty
                   render_dot
                   assurance_case_to_json render_json render_json_pretty
                   signed_to_evidence signed_to_json
                   check_well_formed.
