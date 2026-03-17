(* ------------------------------------------------------------------ *)
(* End-to-end CONOPS bridge example                                    *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Main.
From RACK Require Import Reflect.
From RACK Require Import Export.
From RACK Require Import Notation.
From RACK Require Import Trace.
From RACK Require Import Conops.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* A miniature CONOPS document                                         *)
(* ================================================================== *)

Definition ex_req1 : ConopsRequirement := {|
  cr_id := "REQ-SAFE-01";
  cr_text := "The system shall not cause harm to operators";
  cr_rationale := "Operator safety is the primary design constraint";
  cr_priority := "critical";
|}.

Definition ex_req2 : ConopsRequirement := {|
  cr_id := "REQ-AVAIL-01";
  cr_text := "The system shall be available 99.9% of the time";
  cr_rationale := "Mission continuity requires high availability";
  cr_priority := "high";
|}.

Definition ex_asm1 : ConopsAssumption := {|
  ca_id := "ASM-ENV-01";
  ca_text := "Operating temperature is between -20C and 50C";
|}.

Definition ex_cst1 : ConopsConstraint := {|
  cc_id := "CST-MASS-01";
  cc_text := "Total system mass shall not exceed 25 kg";
|}.

Definition ex_section : ConopsSection := {|
  csec_title := "Safety and availability";
  csec_requirements := [ex_req1; ex_req2];
  csec_assumptions := [ex_asm1];
  csec_constraints := [ex_cst1];
|}.

Definition ex_scenario : ConopsScenario := {|
  cs_id := "SCN-01";
  cs_description := "Normal operation under standard conditions";
  cs_req_ids := ["REQ-SAFE-01"; "REQ-AVAIL-01"];
|}.

Definition ex_conops : ConopsDocument := {|
  cd_title := "Widget Controller CONOPS";
  cd_version := "1.0";
  cd_sections := [ex_section];
  cd_scenarios := [ex_scenario];
|}.

(* ================================================================== *)
(* Compile and verify                                                  *)
(* ================================================================== *)

Definition ex_compiled := compile_conops ex_conops "TOP".
Definition ex_ac := fst ex_compiled.
Definition ex_traces := snd ex_compiled.

(* The compiled case has the right top *)
Example ex_top : ex_ac.(ac_top) = "TOP" := eq_refl.

(* Requirements are Goal nodes *)
Example ex_req1_kind :
  match find_node ex_ac "REQ-SAFE-01" with
  | Some n => n.(node_kind) = Goal
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* Assumption is an Assumption node *)
Example ex_asm1_kind :
  match find_node ex_ac "ASM-ENV-01" with
  | Some n => n.(node_kind) = Assumption
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* Constraint is a Context node *)
Example ex_cst1_kind :
  match find_node ex_ac "CST-MASS-01" with
  | Some n => n.(node_kind) = Context
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* Trace links exist for each requirement *)
Example ex_trace_count :
  length ex_traces = 2.
Proof. vm_compute. reflexivity. Qed.

(* Requirements are children of TOP *)
Example ex_req1_child :
  In "REQ-SAFE-01" (supportedby_children ex_ac "TOP").
Proof. vm_compute. left. reflexivity. Qed.

(* ================================================================== *)
(* Attach evidence and prove WellFormed                                *)
(* ================================================================== *)

(* Add Solution evidence nodes for each requirement *)
Definition safety_evidence : Evidence :=
  ProofTerm "safety_analysis" True I (Some (fun _ => true)).

Definition avail_evidence : Evidence :=
  Certificate "HA:99.95%:2026-03-18" "HA-tool"
    (fun s => String.eqb s "HA:99.95%:2026-03-18").

Definition ex_sol_safe : Node :=
  mkSolution "SOL-SAFE-01" "Safety analysis: no harm scenarios identified"
    safety_evidence [md_string "tool" "safety-analysis"] True.

Definition ex_sol_avail : Node :=
  mkSolution "SOL-AVAIL-01" "HA analysis: 99.95% availability demonstrated"
    avail_evidence [md_string "tool" "HA-tool"] True.

(* Strategy node to decompose TOP into evidence *)
Definition ex_strategy : Node :=
  mkStrategy "STRAT-01" "Argue via safety analysis and HA analysis"
    [] True.

(* Build the full case with evidence *)
Definition ex_full_ac : AssuranceCase := {|
  ac_nodes := ex_ac.(ac_nodes) ++
    [ex_strategy; ex_sol_safe; ex_sol_avail];
  ac_links := ex_ac.(ac_links) ++
    [supports "REQ-SAFE-01" "STRAT-01";
     supports "REQ-AVAIL-01" "STRAT-01";
     supports "STRAT-01" "SOL-SAFE-01";
     supports "STRAT-01" "SOL-AVAIL-01"];
  ac_top := "TOP";
|}.

(* Structural checks pass *)
Example ex_full_structural :
  structural_checks ex_full_ac = true.
Proof. vm_compute. reflexivity. Qed.

(* check_wf_extended passes *)
Example ex_full_wf_check :
  check_wf_extended ex_full_ac = true.
Proof. vm_compute. reflexivity. Qed.

(* No diagnostic errors *)
Example ex_full_no_errors :
  diagnose_all ex_full_ac = [].
Proof. vm_compute. reflexivity. Qed.

(* Support tree exists *)
Example ex_full_support :
  check_support_tree ex_full_ac "TOP" = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Build WellTraced                                                    *)
(* ================================================================== *)

Definition ex_full_tg : TraceGraph := {|
  tg_case := ex_full_ac;
  tg_requirements := [{| req_id := "REQ-SAFE-01" |};
                       {| req_id := "REQ-AVAIL-01" |}];
  tg_artifacts := [];
  tg_commits := [];
  tg_tool_runs := [{| run_id := "safety-run-1" |};
                    {| run_id := "ha-run-1" |}];
  tg_owners := [];
  tg_trace_links :=
    ex_traces ++
    [{| tl_kind := TL_ProducedBy;
        tl_source := "SOL-SAFE-01";
        tl_target := "safety-run-1" |};
     {| tl_kind := TL_ProducedBy;
        tl_source := "SOL-AVAIL-01";
        tl_target := "ha-run-1" |};
     {| tl_kind := TL_VerifiedBy;
        tl_source := "REQ-SAFE-01";
        tl_target := "SOL-SAFE-01" |}];
|}.

Example ex_trace_total_check :
  check_trace_total ex_full_tg = true.
Proof. vm_compute. reflexivity. Qed.

Example ex_trace_provenance_check :
  check_trace_provenance ex_full_tg = true.
Proof. vm_compute. reflexivity. Qed.

(* JSON export produces non-empty output *)
Example ex_conops_json :
  render_assurance_case ex_full_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.

(* DOT export produces non-empty output *)
Example ex_conops_dot :
  render_dot ex_full_ac <> EmptyString.
Proof. vm_compute. discriminate. Qed.
