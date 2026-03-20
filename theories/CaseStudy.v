(* ------------------------------------------------------------------ *)
(* End-to-end case study and performance characterization              *)
(*                                                                    *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Main.
From RACK Require Import Reflect.
From RACK Require Import Export.
From RACK Require Import Notation.
From RACK Require Import EvidenceClass.
From RACK Require Import ProofIdentity.
From RACK Require Import Trace.
From RACK Require Import Delta.
From RACK Require Import Bridge.
From RACK Require Import ProductLine.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Arguments supportedby_children : simpl never.

(* ================================================================== *)
(* Case study: verified memory allocator                               *)
(*                                                                     *)
(* A miniature but non-trivial assurance case for a memory allocator  *)
(* with requirements decomposed into formal verification, bounded     *)
(* model checking, fuzz testing, and code review evidence.            *)
(* ================================================================== *)

(* -- Requirements -------------------------------------------------- *)

Definition alloc_safety_claim : Prop :=
  forall n : nat, n > 0 -> exists m : nat, m >= n.

Definition no_double_free_claim : Prop :=
  forall a b : nat, a <> b -> a <> b.  (* simplified *)

Definition bounded_alloc_claim : Prop :=
  forall n : nat, n <= 1024 -> n <= 1024.

Definition alloc_safety_proof : alloc_safety_claim :=
  fun n Hgt => ex_intro _ n (Nat.le_refl n).

Definition no_double_free_proof : no_double_free_claim :=
  fun a b H => H.

Definition bounded_alloc_proof : bounded_alloc_claim :=
  fun n H => H.

(* -- Nodes --------------------------------------------------------- *)

Definition cs_top : Node :=
  mkGoal "CS-top" "Memory allocator is safe and correct"
    [md_string "weight" "critical"]
    True.

Definition cs_strategy : Node :=
  mkStrategy "CS-strat" "Argue via formal proof, model checking, and fuzz testing"
    [] True.

Definition cs_context : Node :=
  mkContext "CS-ctx" "Scope: embedded allocator, max 1024 bytes".

Definition cs_assumption : Node :=
  mkAssumption "CS-asm" "Compiler is trusted (not verified)".

(* Formal proof evidence *)
Definition cs_sol_proof : Node :=
  mkSolution "CS-proof" "Rocq proof: allocation always succeeds for n > 0"
    (proof_evidence "alloc_safety" "Rocq proof: allocation always succeeds for n > 0" alloc_safety_claim alloc_safety_proof)
    [md_string "tool" "Rocq"]
    alloc_safety_claim.

(* CBMC model checking evidence *)
Definition cs_cbmc_blob : string :=
  "CBMC:no_double_free:unwind=10:v6.0:2026-03-18".
Definition cs_cbmc_verify (s : string) : bool :=
  String.eqb s cs_cbmc_blob.

Definition cs_sol_cbmc : Node :=
  mkSolution "CS-cbmc" "CBMC: no double-free within unwind=10"
    (cert_evidence cs_cbmc_blob "CBMC" cs_cbmc_verify)
    [md_string "tool" "CBMC";
     md_string "version" "6.0";
     md_nat "unwind" 10;
     md_timestamp "timestamp" "2026-03-18T08:00:00Z";
     md_timestamp "valid_until" "2026-06-18"]
    no_double_free_claim.

(* Kani bounded verification evidence *)
Definition cs_kani_blob : string :=
  "Kani:alloc_harness:bounded_alloc:success".
Definition cs_kani_verify (s : string) : bool :=
  String.eqb s cs_kani_blob.

Definition cs_sol_kani : Node :=
  mkSolution "CS-kani" "Kani: bounded allocation within 1024 bytes verified"
    (cert_evidence cs_kani_blob "Kani" cs_kani_verify)
    [md_string "tool" "Kani";
     md_string "harness" "alloc_harness";
     md_nat "unwind" 20;
     md_timestamp "timestamp" "2026-03-18T09:00:00Z"]
    bounded_alloc_claim.

(* AFL++ fuzz testing evidence *)
Definition cs_fuzz_blob : string :=
  "AFL++:0_crashes:5M_inputs:allocator:2026-03-18".
Definition cs_fuzz_verify (s : string) : bool :=
  String.eqb s cs_fuzz_blob.

Definition cs_sol_fuzz : Node :=
  mkSolution "CS-fuzz" "AFL++: 0 crashes in 5M inputs"
    (cert_evidence cs_fuzz_blob "AFL++" cs_fuzz_verify)
    [md_string "tool" "AFL++";
     md_timestamp "timestamp" "2026-03-18T10:00:00Z";
     md_timestamp "valid_until" "2026-04-18"]
    True.

(* -- Links --------------------------------------------------------- *)

Definition cs_links : list Link :=
  [supports "CS-top" "CS-strat";
   in_context_of "CS-top" "CS-ctx";
   in_context_of "CS-strat" "CS-asm";
   supports "CS-strat" "CS-proof";
   supports "CS-strat" "CS-cbmc";
   supports "CS-strat" "CS-kani";
   supports "CS-strat" "CS-fuzz"].

(* -- Assurance case ------------------------------------------------ *)

Definition cs_ac : AssuranceCase :=
  mkCase "CS-top"
    [cs_top; cs_strategy; cs_context; cs_assumption;
     cs_sol_proof; cs_sol_cbmc; cs_sol_kani; cs_sol_fuzz]
    cs_links.

(* -- Verification -------------------------------------------------- *)

Example cs_structural : structural_checks cs_ac = true := eq_refl.
Example cs_wf_check : check_wf_extended cs_ac = true := eq_refl.

Definition cs_wf : WellFormed cs_ac.
Proof. prove_well_formed_full. Qed.

Theorem cs_supported : SupportTree cs_ac "CS-top".
Proof. exact (assurance_case_supported cs_ac cs_wf). Qed.

Example cs_support_check :
  check_support_tree cs_ac "CS-top" = true := eq_refl.

Example cs_diagnose_empty :
  diagnose_all cs_ac = [] := eq_refl.

(* -- Evidence classification --------------------------------------- *)

Example cs_proof_class :
  classify_evidence
    (proof_evidence "alloc_safety" "alloc" alloc_safety_claim alloc_safety_proof)
  = ECTheorem := eq_refl.

Example cs_cbmc_class :
  classify_evidence (cert_evidence cs_cbmc_blob "CBMC" cs_cbmc_verify)
  = ECModelCheck := eq_refl.

Example cs_kani_class :
  classify_evidence (cert_evidence cs_kani_blob "Kani" cs_kani_verify)
  = ECSymbolic := eq_refl.

Example cs_fuzz_class :
  classify_evidence (cert_evidence cs_fuzz_blob "AFL++" cs_fuzz_verify)
  = ECTest := eq_refl.

(* -- Freshness check ----------------------------------------------- *)

(* Freshness check requires dates within the validity window.
   The check_all_fresh function validates evidence_fresh per node. *)
Example cs_admissible_check :
  check_admissible cs_ac "2026-03-18" = false.
Proof. vm_compute. reflexivity. Qed.

(* -- Traceability -------------------------------------------------- *)

Definition cs_trace_graph : TraceGraph := {|
  tg_case := cs_ac;
  tg_requirements := [{| req_id := "REQ-001" |};
                       {| req_id := "REQ-002" |};
                       {| req_id := "REQ-003" |}];
  tg_artifacts := [{| art_id := "src/alloc.rs" |}];
  tg_commits := [{| cmt_id := "abc1234" |}];
  tg_tool_runs := [{| run_id := "cbmc-run-1" |};
                    {| run_id := "kani-run-1" |};
                    {| run_id := "fuzz-run-1" |}];
  tg_owners := [{| own_id := "team-safety" |}];
  tg_trace_links :=
    [{| tl_kind := TL_Satisfies;
        tl_source := "REQ-001"; tl_target := "CS-top" |};
     {| tl_kind := TL_Satisfies;
        tl_source := "REQ-002"; tl_target := "CS-cbmc" |};
     {| tl_kind := TL_Satisfies;
        tl_source := "REQ-003"; tl_target := "CS-kani" |};
     {| tl_kind := TL_ImplementedBy;
        tl_source := "CS-top"; tl_target := "src/alloc.rs" |};
     {| tl_kind := TL_CommittedIn;
        tl_source := "src/alloc.rs"; tl_target := "abc1234" |};
     {| tl_kind := TL_ProducedBy;
        tl_source := "CS-proof"; tl_target := "rocq-build" |};
     {| tl_kind := TL_ProducedBy;
        tl_source := "CS-cbmc"; tl_target := "cbmc-run-1" |};
     {| tl_kind := TL_ProducedBy;
        tl_source := "CS-kani"; tl_target := "kani-run-1" |};
     {| tl_kind := TL_ProducedBy;
        tl_source := "CS-fuzz"; tl_target := "fuzz-run-1" |};
     {| tl_kind := TL_VerifiedBy;
        tl_source := "CS-top"; tl_target := "CS-proof" |};
     {| tl_kind := TL_OwnedBy;
        tl_source := "CS-top"; tl_target := "team-safety" |}];
|}.

Example cs_trace_total :
  check_trace_total cs_trace_graph = true := eq_refl.

Example cs_trace_provenance :
  check_trace_provenance cs_trace_graph = true := eq_refl.

(* -- Invalidation: requirement change ------------------------------ *)

Definition cs_req_change :=
  invalidate_requirement cs_trace_graph {| req_id := "REQ-001" |}.

(* The requirement change affects CS-top and its descendants *)
Example cs_req_change_nonempty :
  cs_req_change.(iw_stale_nodes) <> [].
Proof. vm_compute. discriminate. Qed.

(* -- Delta: updating evidence after a code change ------------------ *)

Definition cs_new_fuzz_blob : string :=
  "AFL++:0_crashes:10M_inputs:allocator:2026-03-19".
Definition cs_new_fuzz_verify (s : string) : bool :=
  String.eqb s cs_new_fuzz_blob.

Definition cs_delta : AssuranceDelta := {|
  ad_node_changes := [
    UpdateEvidence "CS-fuzz"
      (cert_evidence cs_new_fuzz_blob "AFL++" cs_new_fuzz_verify)
  ];
  ad_link_changes := [];
  ad_trace_changes := [];
  ad_commit := Some {| cmt_id := "def5678" |};
  ad_description := "Rerun fuzz testing with 10M inputs";
|}.

Example cs_delta_affected :
  delta_affected_nodes cs_delta = ["CS-fuzz"].
Proof. vm_compute. reflexivity. Qed.

(* -- Export sanity ------------------------------------------------- *)

Example cs_json_nonempty :
  render_assurance_case cs_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

Example cs_dot_nonempty :
  render_dot cs_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

Example cs_sacm_nonempty :
  render_sacm cs_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

(* -- Product-line variant ------------------------------------------ *)

Definition cs_fm : FeatureModel := {|
  fm_features := ["alloc"; "fuzz"; "kani"];
  fm_mandatory := ["alloc"];
  fm_constraints := [];
|}.

Definition cs_plc : ProductLineCase := {|
  plc_nodes :=
    [{| an_node := cs_top; an_feature := FETrue |};
     {| an_node := cs_strategy; an_feature := FETrue |};
     {| an_node := cs_context; an_feature := FETrue |};
     {| an_node := cs_assumption; an_feature := FETrue |};
     {| an_node := cs_sol_proof; an_feature := FETrue |};
     {| an_node := cs_sol_cbmc; an_feature := FETrue |};
     {| an_node := cs_sol_kani; an_feature := FEAtom "kani" |};
     {| an_node := cs_sol_fuzz; an_feature := FEAtom "fuzz" |}];
  plc_links :=
    [{| al_link := supports "CS-top" "CS-strat"; al_feature := FETrue |};
     {| al_link := in_context_of "CS-top" "CS-ctx"; al_feature := FETrue |};
     {| al_link := in_context_of "CS-strat" "CS-asm"; al_feature := FETrue |};
     {| al_link := supports "CS-strat" "CS-proof"; al_feature := FETrue |};
     {| al_link := supports "CS-strat" "CS-cbmc"; al_feature := FETrue |};
     {| al_link := supports "CS-strat" "CS-kani"; al_feature := FEAtom "kani" |};
     {| al_link := supports "CS-strat" "CS-fuzz"; al_feature := FEAtom "fuzz" |}];
  plc_top := "CS-top";
  plc_fm := cs_fm;
|}.

(* Full variant includes everything *)
Example cs_full_variant_wf :
  check_variant_wf cs_plc ["alloc"; "fuzz"; "kani"] = true := eq_refl.

(* Minimal variant: only the mandatory features + CBMC + proof *)
Example cs_minimal_variant_wf :
  check_variant_wf cs_plc ["alloc"] = true := eq_refl.

(* Family-wide nodes: those with FETrue *)
Example cs_reusable :
  length (reusable_nodes cs_plc) = 6.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Performance characterization types                                  *)
(* ================================================================== *)

(** Timing record for benchmarking.  Populate from OCaml-side
    timing after extraction. *)
Record BenchmarkResult : Type := {
  br_name      : string;
  br_nodes     : nat;
  br_links     : nat;
  br_check_ms  : nat;   (* structural_checks time *)
  br_support_ms : nat;  (* check_support_tree time *)
  br_json_ms   : nat;   (* render_assurance_case time *)
  br_dot_ms    : nat;   (* render_dot time *)
}.

(** Generate a linear chain assurance case of size n for benchmarking.
    Goal -> Strategy -> ... -> Solution *)
Fixpoint gen_chain (n : nat) (acc_nodes : list Node)
    (acc_links : list Link) : AssuranceCase :=
  match n with
  | 0 =>
    let sol := {|
      node_id := "N0";
      node_kind := Solution;
      node_claim_text := "leaf";
      node_evidence := Some (ProofTerm "bench" True I (Some (fun _ => true)));
      node_metadata := nil;
      node_claim := True;
    |} in
    {| ac_nodes := sol :: acc_nodes;
       ac_links := acc_links;
       ac_top := match acc_nodes with
                 | n :: _ => n.(node_id)
                 | [] => "N0"
                 end; |}
  | S m =>
    let id := append "N" (nat_to_string n) in
    let child_id := match m with
                    | 0 => "N0"
                    | S k => append "N" (nat_to_string m)
                    end in
    let kind := if Nat.eqb n (S m) then Goal else Strategy in
    let node := {|
      node_id := id;
      node_kind := kind;
      node_claim_text := id;
      node_evidence := None;
      node_metadata := nil;
      node_claim := True;
    |} in
    let link := {|
      link_kind := SupportedBy;
      link_from := id;
      link_to := child_id;
    |} in
    gen_chain m (node :: acc_nodes) (link :: acc_links)
  end.

Definition gen_benchmark_case (n : nat) : AssuranceCase :=
  gen_chain n [] [].

(** Generate a balanced binary tree assurance case of depth d.
    Each internal node is a Strategy with two children.
    Root is a Goal.  Leaves are Solutions. *)
Fixpoint gen_tree (d : nat) (prefix : string)
    : list Node * list Link * string :=
  let id := prefix in
  match d with
  | 0 =>
    let sol := {|
      node_id := id; node_kind := Solution;
      node_claim_text := id;
      node_evidence := Some (ProofTerm "bench" True I (Some (fun _ => true)));
      node_metadata := nil; node_claim := True |} in
    ([sol], [], id)
  | S d' =>
    let '(ln, ll, lid) := gen_tree d' (append prefix "L") in
    let '(rn, rl, rid) := gen_tree d' (append prefix "R") in
    let kind := match d' with 0 => Goal | _ => Strategy end in
    let node := {|
      node_id := id;
      node_kind := if String.eqb prefix "T" then Goal else kind;
      node_claim_text := id; node_evidence := None;
      node_metadata := nil; node_claim := True |} in
    let lnk_l := {| link_kind := SupportedBy;
                     link_from := id; link_to := lid |} in
    let lnk_r := {| link_kind := SupportedBy;
                     link_from := id; link_to := rid |} in
    (node :: ln ++ rn, lnk_l :: lnk_r :: ll ++ rl, id)
  end.

Definition gen_tree_case (depth : nat) : AssuranceCase :=
  let '(nodes, links, top) := gen_tree depth "T" in
  {| ac_nodes := nodes; ac_links := links; ac_top := top |}.

(* Small tree benchmark compile-time checks *)
Example bench_tree_3 :
  structural_checks (gen_tree_case 3) = true := eq_refl.

Example bench_chain_10 :
  check_wf_extended (gen_benchmark_case 10) = true := eq_refl.

(* ================================================================== *)
(* PRAdmissible for cs_delta                                          *)
(* ================================================================== *)

Example cs_delta_result_structural :
  structural_checks (apply_delta cs_ac cs_delta) = true.
Proof. vm_compute. reflexivity. Qed.

Definition cs_delta_result_wf : WellFormed (apply_delta cs_ac cs_delta).
Proof. prove_well_formed_full. Qed.

Lemma cs_delta_preserved : forall id,
    In id (delta_preserved_nodes cs_ac cs_delta) ->
    node_preserved cs_ac (apply_delta cs_ac cs_delta) id.
Proof.
  intros id Hpres.
  unfold delta_preserved_nodes in Hpres. simpl in Hpres.
  unfold node_preserved.
  repeat (destruct Hpres as [<- | Hpres];
    [vm_compute; repeat split; reflexivity |]).
  destruct Hpres.
Qed.

Definition cs_pr_admissible : PRAdmissible cs_ac cs_delta := {|
  pra_result_wf := cs_delta_result_wf;
  pra_preserved := cs_delta_preserved;
|}.

(* ================================================================== *)
(* delta_preserves_subtree for cs_delta                               *)
(* ================================================================== *)

Lemma cs_delta_preserves_subtree :
    delta_preserves_subtree cs_ac cs_delta "CS-top".
Proof.
  intros id Hpres _. exact (cs_delta_preserved id Hpres).
Qed.

(* ================================================================== *)
(* Family-wide structural checks for cs_plc                          *)
(* ================================================================== *)

(** Every valid variant of [cs_plc] passes structural checks.
    The proof case-splits on feature membership (3 features → 4 valid
    variants since "alloc" is mandatory), then computes each projection. *)
Lemma cs_family_wide_structural :
    family_wide cs_plc (fun ac => structural_checks ac = true).
Proof.
  intros v Hvalid.
  unfold project_variant, cs_plc. simpl.
  destruct (mem_string "fuzz" v) eqn:Hfuzz;
  destruct (mem_string "kani" v) eqn:Hkani;
  simpl; rewrite ?Hfuzz, ?Hkani; simpl;
  reflexivity.
Qed.
