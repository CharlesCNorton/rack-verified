(* ------------------------------------------------------------------ *)
(* Examples: requirement -> theorem -> evidence                         *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Main.
From RACK Require Import Reflect.
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
  node_claim_text := "2 + 2 = 4";
  node_evidence := None;
  node_metadata := [];
  node_claim := ex_claim;
|}.

Definition ex_solution : Node := {|
  node_id := "E1";
  node_kind := Solution;
  node_claim_text := "2 + 2 = 4";
  node_evidence := Some (ProofTerm "ex_claim" ex_claim ex_proof None);
  node_metadata := [];
  node_claim := ex_claim;
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

Definition ex_wf : WellFormed ex_ac.
Proof. prove_well_formed_auto. Qed.

Theorem ex_supported : SupportTree ex_ac "G1".
Proof. exact (assurance_case_supported ex_ac ex_wf). Qed.

Example ex_check : check_well_formed ex_ac = true := eq_refl.
Example ex_struct_check : structural_checks ex_ac = true := eq_refl.

(* ================================================================== *)
(* Example 2: Goal -> Strategy -> 2 Solutions + Context                 *)
(* ================================================================== *)

Definition ml_security_claim : Prop := True.
Definition ml_unit_claim : Prop := 1 = 1.
Definition ml_fuzz_claim : Prop := True.

Definition ml_goal : Node := {|
  node_id := "G-sec";
  node_kind := Goal;
  node_claim_text := "System meets security requirements";
  node_evidence := None;
  node_metadata := [("weight", "critical")];
  node_claim := ml_security_claim;
|}.

Definition ml_strategy : Node := {|
  node_id := "S-test";
  node_kind := Strategy;
  node_claim_text := "Argue via unit tests and fuzz testing";
  node_evidence := None;
  node_metadata := [];
  node_claim := ml_security_claim;
|}.

Definition ml_context : Node := {|
  node_id := "C-scope";
  node_kind := Context;
  node_claim_text := "Scope: public-facing HTTP endpoints";
  node_evidence := None;
  node_metadata := [];
  node_claim := True;
|}.

Definition ml_sol_unit : Node := {|
  node_id := "E-unit";
  node_kind := Solution;
  node_claim_text := "Unit test suite passes (1 = 1)";
  node_evidence := Some (ProofTerm "unit_tests_pass" ml_unit_claim eq_refl None);
  node_metadata := [("timestamp", "2026-03-18T10:00:00Z")];
  node_claim := ml_unit_claim;
|}.

Definition ml_sol_fuzz : Node := {|
  node_id := "E-fuzz";
  node_kind := Solution;
  node_claim_text := "Fuzz testing passed (external certificate)";
  node_evidence := Some (Certificate "PASS:fuzz:2026-03-18" "fuzz-tool"
                           (fun s => String.eqb s "PASS:fuzz:2026-03-18"));
  node_metadata := [("timestamp", "2026-03-18T11:00:00Z");
                     ("tool", "fuzz-tool")];
  node_claim := ml_fuzz_claim;
|}.

Definition ml_ac : AssuranceCase := {|
  ac_nodes := [ml_goal; ml_strategy; ml_context; ml_sol_unit; ml_sol_fuzz];
  ac_links := [{| link_kind := SupportedBy; link_from := "G-sec"; link_to := "S-test" |};
               {| link_kind := InContextOf; link_from := "G-sec"; link_to := "C-scope" |};
               {| link_kind := SupportedBy; link_from := "S-test"; link_to := "E-unit" |};
               {| link_kind := SupportedBy; link_from := "S-test"; link_to := "E-fuzz" |}];
  ac_top := "G-sec";
|}.

Definition ml_wf : WellFormed ml_ac.
Proof. prove_well_formed_auto. Qed.

Theorem ml_supported : SupportTree ml_ac "G-sec".
Proof. exact (assurance_case_supported ml_ac ml_wf). Qed.

Example ml_check : check_well_formed ml_ac = true := eq_refl.
Example ml_struct_check : structural_checks ml_ac = true := eq_refl.

(* ================================================================== *)
(* Example 3: signed evidence blob (external tool result)              *)
(* ================================================================== *)

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

Definition sb_claim : Prop := True.

Definition sb_goal : Node := {|
  node_id := "G-safe";
  node_kind := Goal;
  node_claim_text := "System is free of buffer overflows";
  node_evidence := None;
  node_metadata := [];
  node_claim := sb_claim;
|}.

Definition sb_solution : Node := {|
  node_id := "E-saw";
  node_kind := Solution;
  node_claim_text := "SAW verified: no buffer overflows";
  node_evidence := Some (signed_to_evidence saw_blob);
  node_metadata := [("tool", "SAW"); ("timestamp", "2026-03-18T12:00:00Z")];
  node_claim := sb_claim;
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

Definition sb_wf : WellFormed sb_ac.
Proof. prove_well_formed_auto. Qed.

Theorem sb_supported : SupportTree sb_ac "G-safe".
Proof. exact (assurance_case_supported sb_ac sb_wf). Qed.

Example sb_check : check_well_formed sb_ac = true := eq_refl.
Example sb_struct_check : structural_checks sb_ac = true := eq_refl.

(* ================================================================== *)
(* Example 4: non-trivial mathematical claim                           *)
(* ================================================================== *)

Definition arith_claim : Prop :=
  forall n : nat, n + 0 = n /\ 0 + n = n.

Definition right_zero_claim : Prop := forall n : nat, n + 0 = n.
Definition left_zero_claim  : Prop := forall n : nat, 0 + n = n.

Definition right_zero_proof : right_zero_claim := Nat.add_0_r.
Definition left_zero_proof  : left_zero_claim  := fun n => eq_refl.

Definition ar_goal : Node := {|
  node_id := "G-arith";
  node_kind := Goal;
  node_claim_text := "forall n, n+0=n /\ 0+n=n";
  node_evidence := None;
  node_metadata := [];
  node_claim := arith_claim;
|}.

Definition ar_strategy : Node := {|
  node_id := "S-split";
  node_kind := Strategy;
  node_claim_text := "Split conjunction; prove each half";
  node_evidence := None;
  node_metadata := [];
  node_claim := arith_claim;
|}.

Definition ar_sol_right : Node := {|
  node_id := "E-right";
  node_kind := Solution;
  node_claim_text := "forall n, n+0=n (by induction: Nat.add_0_r)";
  node_evidence := Some (ProofTerm "Nat.add_0_r" right_zero_claim right_zero_proof None);
  node_metadata := [];
  node_claim := right_zero_claim;
|}.

Definition ar_sol_left : Node := {|
  node_id := "E-left";
  node_kind := Solution;
  node_claim_text := "forall n, 0+n=n (by computation)";
  node_evidence := Some (ProofTerm "eq_refl" left_zero_claim left_zero_proof None);
  node_metadata := [];
  node_claim := left_zero_claim;
|}.

Definition ar_ac : AssuranceCase := {|
  ac_nodes := [ar_goal; ar_strategy; ar_sol_right; ar_sol_left];
  ac_links := [{| link_kind := SupportedBy; link_from := "G-arith";
                   link_to := "S-split" |};
               {| link_kind := SupportedBy; link_from := "S-split";
                   link_to := "E-right" |};
               {| link_kind := SupportedBy; link_from := "S-split";
                   link_to := "E-left" |}];
  ac_top := "G-arith";
|}.

Example ar_struct_check :
  structural_checks ar_ac = true := eq_refl.

Lemma ar_find_node_equiv : forall id,
    find_node ar_ac id =
    if String.eqb "G-arith" id then Some ar_goal
    else if String.eqb "S-split" id then Some ar_strategy
    else if String.eqb "E-right" id then Some ar_sol_right
    else if String.eqb "E-left" id then Some ar_sol_left
    else None.
Proof.
  intro id. unfold find_node, ar_ac.
  cbn -[String.eqb]. destruct (String.eqb "G-arith" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "S-split" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E-right" id); [reflexivity |].
  cbn -[String.eqb]. destruct (String.eqb "E-left" id); reflexivity.
Qed.

Lemma ar_entailment : forall id n,
    find_node ar_ac id = Some n ->
    (n.(node_kind) = Goal \/ n.(node_kind) = Strategy) ->
    (let kids := supportedby_children ar_ac id in
     let child_claims :=
       flat_map (fun kid =>
         match find_node ar_ac kid with
         | Some cn => [cn.(node_claim)]
         | None     => []
         end) kids
     in fold_right and True child_claims -> n.(node_claim)).
Proof. solve_entailment ar_find_node_equiv. Qed.

Lemma ar_evidence_valid : forall n e,
    In n ar_ac.(ac_nodes) ->
    n.(node_kind) = Solution ->
    n.(node_evidence) = Some e ->
    evidence_valid n e.
Proof.
  intros n e Hin Hkind He. simpl in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    try discriminate;
    injection He as <-; vm_compute; reflexivity.
Qed.

Definition ar_wf : WellFormed ar_ac :=
  build_well_formed ar_ac
    eq_refl
    ar_entailment
    ar_evidence_valid.

Theorem ar_supported : SupportTree ar_ac "G-arith".
Proof. exact (assurance_case_supported ar_ac ar_wf). Qed.

Example ar_check : check_well_formed ar_ac = true := eq_refl.

(* ================================================================== *)
(* Example 5: compositional assembly                                   *)
(* ================================================================== *)

Definition parent_claim : Prop := 2 + 2 = 4.

Definition parent_goal : Node := {|
  node_id := "G-parent";
  node_kind := Goal;
  node_claim_text := "Arithmetic subsystem is correct";
  node_evidence := None;
  node_metadata := [];
  node_claim := parent_claim;
|}.

Definition parent_ac : AssuranceCase := {|
  ac_nodes := [parent_goal];
  ac_links := [];
  ac_top := "G-parent";
|}.

Definition composed_ac : AssuranceCase :=
  compose_cases parent_ac ex_ac "G-parent".

Example composed_struct_check :
  structural_checks composed_ac = true := eq_refl.

Example composed_check :
  check_well_formed composed_ac = true := eq_refl.

(* ================================================================== *)
(* Example 6: multi-tool composition (CBMC + fuzzer + CI)              *)
(* ================================================================== *)

Definition mt_safety_claim : Prop := True.
Definition mt_cbmc_claim   : Prop := True.
Definition mt_fuzz_claim   : Prop := True.
Definition mt_ci_claim     : Prop := True.

Definition cbmc_verify (s : string) : bool :=
  String.eqb s "CBMC:all_assertions_hold:v5.95:2026-03-18".

Definition fuzz_verify (s : string) : bool :=
  String.eqb s "AFL++:0_crashes:10M_inputs:2026-03-18".

Definition ci_verify (s : string) : bool :=
  String.eqb s "GHA:run_12345:all_green:2026-03-18".

Definition mt_goal : Node := {|
  node_id := "G-mt";
  node_kind := Goal;
  node_claim_text := "Parser is safe against malformed input";
  node_evidence := None;
  node_metadata := [("confidence", "0.99"); ("weight", "critical")];
  node_claim := mt_safety_claim;
|}.

Definition mt_strategy : Node := {|
  node_id := "S-mt";
  node_kind := Strategy;
  node_claim_text := "Combine static analysis, fuzzing, and CI";
  node_evidence := None;
  node_metadata := [];
  node_claim := mt_safety_claim;
|}.

Definition mt_assumption : Node := {|
  node_id := "A-mt";
  node_kind := Assumption;
  node_claim_text := "Compiler is trusted (not verified)";
  node_evidence := None;
  node_metadata := [];
  node_claim := True;
|}.

(* Runtime re-checker for CBMC: the thunk calls the validator *)
Definition cbmc_runtime_check (_ : unit) : bool :=
  cbmc_verify "CBMC:all_assertions_hold:v5.95:2026-03-18".

Definition mt_sol_cbmc : Node := {|
  node_id := "E-cbmc";
  node_kind := Solution;
  node_claim_text := "CBMC: all assertions hold";
  node_evidence := Some (Certificate
    "CBMC:all_assertions_hold:v5.95:2026-03-18" "CBMC" cbmc_verify);
  node_metadata := [("tool", "CBMC"); ("version", "5.95");
                     ("timestamp", "2026-03-18T08:00:00Z")];
  node_claim := mt_cbmc_claim;
|}.

Definition mt_sol_fuzz : Node := {|
  node_id := "E-fuzz2";
  node_kind := Solution;
  node_claim_text := "AFL++: 0 crashes in 10M inputs";
  node_evidence := Some (Certificate
    "AFL++:0_crashes:10M_inputs:2026-03-18" "AFL++" fuzz_verify);
  node_metadata := [("tool", "AFL++"); ("timestamp", "2026-03-18T09:00:00Z");
                     ("valid_until", "2026-04-18")];
  node_claim := mt_fuzz_claim;
|}.

Definition mt_sol_ci : Node := {|
  node_id := "E-ci";
  node_kind := Solution;
  node_claim_text := "GitHub Actions: all checks green";
  node_evidence := Some (Certificate
    "GHA:run_12345:all_green:2026-03-18" "GHA" ci_verify);
  node_metadata := [("tool", "GHA"); ("run", "12345");
                     ("timestamp", "2026-03-18T10:30:00Z")];
  node_claim := mt_ci_claim;
|}.

Definition mt_ac : AssuranceCase := {|
  ac_nodes := [mt_goal; mt_strategy; mt_assumption;
               mt_sol_cbmc; mt_sol_fuzz; mt_sol_ci];
  ac_links := [{| link_kind := SupportedBy; link_from := "G-mt"; link_to := "S-mt" |};
               {| link_kind := InContextOf; link_from := "G-mt"; link_to := "A-mt" |};
               {| link_kind := SupportedBy; link_from := "S-mt"; link_to := "E-cbmc" |};
               {| link_kind := SupportedBy; link_from := "S-mt"; link_to := "E-fuzz2" |};
               {| link_kind := SupportedBy; link_from := "S-mt"; link_to := "E-ci" |}];
  ac_top := "G-mt";
|}.

Definition mt_wf : WellFormed mt_ac.
Proof. prove_well_formed_auto. Qed.

Theorem mt_supported : SupportTree mt_ac "G-mt".
Proof. exact (assurance_case_supported mt_ac mt_wf). Qed.

Example mt_check : check_well_formed mt_ac = true := eq_refl.
Example mt_struct_check : structural_checks mt_ac = true := eq_refl.

(* Runtime re-check survives extraction *)
Example mt_cbmc_runtime :
  evidence_runtime_check
    (Certificate "CBMC:all_assertions_hold:v5.95:2026-03-18" "CBMC" cbmc_verify)
  = true := eq_refl.

Example mt_tool_id :
  evidence_tool
    (Certificate "CBMC:all_assertions_hold:v5.95:2026-03-18" "CBMC" cbmc_verify)
  = "CBMC" := eq_refl.

(* ================================================================== *)
(* Example 7: ProofTerm with runtime re-checker                        *)
(* ================================================================== *)

(* A ProofTerm whose optional runtime checker can re-verify
   without the erased proof witness.                                   *)
Definition rt_claim : Prop := 3 + 3 = 6.
Definition rt_proof : rt_claim := eq_refl.
Definition rt_check (_ : unit) : bool := Nat.eqb (3 + 3) 6.

Definition rt_goal : Node := {|
  node_id := "G-rt";
  node_kind := Goal;
  node_claim_text := "3 + 3 = 6";
  node_evidence := None;
  node_metadata := [];
  node_claim := rt_claim;
|}.

Definition rt_solution : Node := {|
  node_id := "E-rt";
  node_kind := Solution;
  node_claim_text := "3 + 3 = 6 (proof + runtime check)";
  node_evidence := Some (ProofTerm "rt_claim" rt_claim rt_proof (Some rt_check));
  node_metadata := [];
  node_claim := rt_claim;
|}.

Definition rt_ac : AssuranceCase := {|
  ac_nodes := [rt_goal; rt_solution];
  ac_links := [{| link_kind := SupportedBy; link_from := "G-rt"; link_to := "E-rt" |}];
  ac_top := "G-rt";
|}.

Definition rt_wf : WellFormed rt_ac.
Proof. prove_well_formed_auto. Qed.

(* Runtime check works after extraction *)
Example rt_runtime_check :
  evidence_runtime_check
    (ProofTerm "rt_claim" rt_claim rt_proof (Some rt_check))
  = true := eq_refl.

(* Without runtime checker, evidence_runtime_check returns true
   (trusts the type system) *)
Example rt_no_runtime_check :
  evidence_runtime_check
    (ProofTerm "rt_claim" rt_claim rt_proof None)
  = true := eq_refl.

(* ================================================================== *)
(* Renderer sanity checks                                              *)
(* ================================================================== *)

Example ex_compact_nonempty :
  render_assurance_case ex_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

Example ex_pretty_nonempty :
  render_assurance_case_pretty ex_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

Example ex_dot_nonempty :
  render_dot ex_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

Lemma renderers_same_ast : forall ac,
    render_assurance_case ac =
    render_json (assurance_case_to_json ac).
Proof. reflexivity. Qed.

Lemma renderers_pretty_same_ast : forall ac,
    render_assurance_case_pretty ac =
    render_json_pretty (assurance_case_to_json ac).
Proof. reflexivity. Qed.

(* SACM export produces non-empty output *)
Example ex_sacm_nonempty :
  render_sacm ex_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

(* DOT with options produces non-empty output *)
Example ex_dot_opts_nonempty :
  render_dot_with_options default_dot_options ex_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

(* Streaming JSON produces non-empty output *)
Example ex_stream_nonempty :
  stream_json_lines ex_ac <> [].
Proof. vm_compute. discriminate. Qed.

(* Diagnostic checker produces empty list for well-formed case *)
Example ex_diagnose_empty :
  diagnose_all ex_ac = [].
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Negative examples: checker rejects malformed cases                  *)
(* ================================================================== *)

Definition bad_dangling_ac : AssuranceCase := {|
  ac_nodes := [{| node_id := "G"; node_kind := Goal;
                   node_claim_text := "G"; node_evidence := None;
                   node_metadata := []; node_claim := True |}];
  ac_links := [{| link_kind := SupportedBy;
                   link_from := "G"; link_to := "MISSING" |}];
  ac_top := "G";
|}.
Example bad_dangling : check_well_formed bad_dangling_ac = false := eq_refl.
Example bad_dangling_s : structural_checks bad_dangling_ac = false := eq_refl.

Definition bad_cycle_ac : AssuranceCase := {|
  ac_nodes := [{| node_id := "A"; node_kind := Goal;
                   node_claim_text := "A"; node_evidence := None;
                   node_metadata := []; node_claim := True |};
               {| node_id := "B"; node_kind := Strategy;
                   node_claim_text := "B"; node_evidence := None;
                   node_metadata := []; node_claim := True |}];
  ac_links := [{| link_kind := SupportedBy;
                   link_from := "A"; link_to := "B" |};
               {| link_kind := SupportedBy;
                   link_from := "B"; link_to := "A" |}];
  ac_top := "A";
|}.
Example bad_cycle : check_well_formed bad_cycle_ac = false := eq_refl.
Example bad_cycle_s : structural_checks bad_cycle_ac = false := eq_refl.

Definition bad_no_evidence_ac : AssuranceCase := {|
  ac_nodes := [{| node_id := "G"; node_kind := Goal;
                   node_claim_text := "G"; node_evidence := None;
                   node_metadata := []; node_claim := True |};
               {| node_id := "E"; node_kind := Solution;
                   node_claim_text := "E"; node_evidence := None;
                   node_metadata := []; node_claim := True |}];
  ac_links := [{| link_kind := SupportedBy;
                   link_from := "G"; link_to := "E" |}];
  ac_top := "G";
|}.
Example bad_no_evidence : check_well_formed bad_no_evidence_ac = false := eq_refl.
Example bad_no_evidence_s : structural_checks bad_no_evidence_ac = false := eq_refl.

Definition bad_dup_ids_ac : AssuranceCase := {|
  ac_nodes := [{| node_id := "X"; node_kind := Goal;
                   node_claim_text := "X1"; node_evidence := None;
                   node_metadata := []; node_claim := True |};
               {| node_id := "X"; node_kind := Solution;
                   node_claim_text := "X2";
                   node_evidence := Some (ProofTerm "t" True I None);
                   node_metadata := []; node_claim := True |}];
  ac_links := [{| link_kind := SupportedBy;
                   link_from := "X"; link_to := "X" |}];
  ac_top := "X";
|}.
Example bad_dup_ids : check_well_formed bad_dup_ids_ac = false := eq_refl.
Example bad_dup_ids_s : structural_checks bad_dup_ids_ac = false := eq_refl.

Definition bad_ctx_dir_ac : AssuranceCase := {|
  ac_nodes := [{| node_id := "G"; node_kind := Goal;
                   node_claim_text := "G"; node_evidence := None;
                   node_metadata := []; node_claim := True |};
               {| node_id := "E"; node_kind := Solution;
                   node_claim_text := "E";
                   node_evidence := Some (ProofTerm "t" True I None);
                   node_metadata := []; node_claim := True |};
               {| node_id := "C"; node_kind := Context;
                   node_claim_text := "C"; node_evidence := None;
                   node_metadata := []; node_claim := True |}];
  ac_links := [{| link_kind := SupportedBy;
                   link_from := "G"; link_to := "E" |};
               {| link_kind := InContextOf;
                   link_from := "E"; link_to := "C" |}];
  ac_top := "G";
|}.
Example bad_ctx_dir : check_well_formed bad_ctx_dir_ac = false := eq_refl.
Example bad_ctx_dir_s : structural_checks bad_ctx_dir_ac = false := eq_refl.

Definition bad_top_ac : AssuranceCase := {|
  ac_nodes := [{| node_id := "S"; node_kind := Strategy;
                   node_claim_text := "S"; node_evidence := None;
                   node_metadata := []; node_claim := True |}];
  ac_links := [];
  ac_top := "S";
|}.
Example bad_top : check_well_formed bad_top_ac = false := eq_refl.
Example bad_top_s : structural_checks bad_top_ac = false := eq_refl.

(* Diagnostic checker reports errors for negative cases *)
Example bad_dangling_diag :
  length (diagnose_all bad_dangling_ac) > 0 := eq_refl.
Example bad_cycle_diag :
  length (diagnose_all bad_cycle_ac) > 0 := eq_refl.
Example bad_no_evidence_diag :
  length (diagnose_all bad_no_evidence_ac) > 0 := eq_refl.

(* ================================================================== *)
(* Checker equivalence                                                 *)
(* ================================================================== *)

Example checkers_agree_ex :
  check_well_formed ex_ac = structural_checks ex_ac := eq_refl.
Example checkers_agree_ml :
  check_well_formed ml_ac = structural_checks ml_ac := eq_refl.
Example checkers_agree_sb :
  check_well_formed sb_ac = structural_checks sb_ac := eq_refl.
Example checkers_agree_ar :
  check_well_formed ar_ac = structural_checks ar_ac := eq_refl.
Example checkers_agree_composed :
  check_well_formed composed_ac = structural_checks composed_ac := eq_refl.
Example checkers_agree_mt :
  check_well_formed mt_ac = structural_checks mt_ac := eq_refl.

Example checkers_agree_dangling :
  check_well_formed bad_dangling_ac = structural_checks bad_dangling_ac := eq_refl.
Example checkers_agree_cycle :
  check_well_formed bad_cycle_ac = structural_checks bad_cycle_ac := eq_refl.
Example checkers_agree_no_ev :
  check_well_formed bad_no_evidence_ac = structural_checks bad_no_evidence_ac := eq_refl.

(* ================================================================== *)
(* Support tree checker and witness                                    *)
(* ================================================================== *)

Example ex_support_check :
  check_support_tree ex_ac "G1" = true := eq_refl.
Example ml_support_check :
  check_support_tree ml_ac "G-sec" = true := eq_refl.
Example sb_support_check :
  check_support_tree sb_ac "G-safe" = true := eq_refl.
Example ar_support_check :
  check_support_tree ar_ac "G-arith" = true := eq_refl.
Example mt_support_check :
  check_support_tree mt_ac "G-mt" = true := eq_refl.

Example bad_dangling_support :
  check_support_tree bad_dangling_ac "G" = false := eq_refl.
Example bad_no_evidence_support :
  check_support_tree bad_no_evidence_ac "G" = false := eq_refl.

Example ex_witness_exists :
  match compute_support_witness ex_ac "G1" with
  | Some _ => true
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example ml_witness_exists :
  match compute_support_witness ml_ac "G-sec" with
  | Some _ => true
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* JSON round-trip test                                                *)
(* ================================================================== *)

Example round_trip_top_id :
  match parse_json (render_assurance_case ex_ac) with
  | Some j =>
    match json_to_assurance_case j with
    | Some ac => String.eqb ac.(ac_top) "G1"
    | None => false
    end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Metadata helpers                                                    *)
(* ================================================================== *)

Example mt_goal_confidence :
  node_confidence mt_goal = Some "0.99" := eq_refl.

Example mt_goal_weight :
  node_weight mt_goal = Some "critical" := eq_refl.

Example mt_sol_cbmc_timestamp :
  node_timestamp mt_sol_cbmc = Some "2026-03-18T08:00:00Z" := eq_refl.

(* ================================================================== *)
(* Incremental checker                                                 *)
(* ================================================================== *)

Example mt_check_node_goal :
  check_node mt_ac "G-mt" = true := eq_refl.
Example mt_check_node_sol :
  check_node mt_ac "E-cbmc" = true := eq_refl.
Example mt_check_link :
  check_link mt_ac {| link_kind := SupportedBy;
                       link_from := "G-mt"; link_to := "S-mt" |} = true := eq_refl.

(* ================================================================== *)
(* Extraction                                                          *)
(* ================================================================== *)

Require Extraction.
Extraction Language OCaml.

(* Efficient extraction directives *)
Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.leb => "(<=)".

Extraction "rack" render_assurance_case render_assurance_case_pretty
                   render_dot render_dot_with_options default_dot_options
                   render_sacm
                   assurance_case_to_json render_json render_json_pretty
                   signed_to_evidence signed_to_json
                   check_well_formed structural_checks
                   compose_cases
                   evidence_label evidence_runtime_check evidence_tool
                   find_node_indexed build_node_index
                   check_support_tree compute_support_witness
                   parse_json json_to_assurance_case
                   hydrate_evidence auto_hydrate json_field
                   diagnose_all diagnose_node check_error_to_json
                   diagnose_to_json
                   check_node check_link
                   fold_assurance_case fold_nodes_indexed
                   stream_dot_lines stream_json_lines
                   find_metadata node_timestamp node_confidence
                   node_weight
                   registry_lookup make_certificate
                   render_json_ext json_to_ext ext_to_json
                   metadata_to_json xml_escape.
