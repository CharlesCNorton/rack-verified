(* ------------------------------------------------------------------ *)
(* CONOPS-to-Rocq bridge: compile operational requirements to          *)
(* assurance case nodes and trace links                                *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Trace.
From RACK Require Import Notation.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* CONOPS document model                                               *)
(* ================================================================== *)

Record ConopsRequirement : Type := {
  cr_id          : string;
  cr_text        : string;
  cr_rationale   : string;
  cr_priority    : string;  (* "critical", "high", "medium", "low" *)
}.

Record ConopsAssumption : Type := {
  ca_id   : string;
  ca_text : string;
}.

Record ConopsConstraint : Type := {
  cc_id   : string;
  cc_text : string;
}.

Record ConopsScenario : Type := {
  cs_id          : string;
  cs_description : string;
  cs_req_ids     : list string;  (* requirements exercised *)
}.

Record ConopsSection : Type := {
  csec_title        : string;
  csec_requirements : list ConopsRequirement;
  csec_assumptions  : list ConopsAssumption;
  csec_constraints  : list ConopsConstraint;
}.

Record ConopsDocument : Type := {
  cd_title      : string;
  cd_version    : string;
  cd_sections   : list ConopsSection;
  cd_scenarios  : list ConopsScenario;
}.

(* ================================================================== *)
(* Compilation: CONOPS -> Assurance case nodes + trace links           *)
(* ================================================================== *)

Definition compile_requirement (cr : ConopsRequirement) : Node :=
  mkGoal cr.(cr_id) cr.(cr_text)
    [md_string "rationale" cr.(cr_rationale);
     md_string "priority" cr.(cr_priority);
     md_string "source" "CONOPS"]
    True.

Definition compile_assumption (ca : ConopsAssumption) : Node :=
  mkAssumption ca.(ca_id) ca.(ca_text).

Definition compile_constraint (cc : ConopsConstraint) : Node :=
  mkContext cc.(cc_id) cc.(cc_text).

Definition compile_section (sec : ConopsSection) : list Node :=
  map compile_requirement sec.(csec_requirements) ++
  map compile_assumption sec.(csec_assumptions) ++
  map compile_constraint sec.(csec_constraints).

Definition compile_document_nodes (doc : ConopsDocument) : list Node :=
  flat_map compile_section doc.(cd_sections).

(** Generate a Satisfies trace link for each requirement. *)
Definition compile_requirement_trace (cr : ConopsRequirement)
    : TraceLink := {|
  tl_kind   := TL_Satisfies;
  tl_source := cr.(cr_id);
  tl_target := cr.(cr_id);  (* self-referential: requirement IS the goal *)
|}.

Definition compile_document_traces (doc : ConopsDocument)
    : list TraceLink :=
  flat_map (fun sec =>
    map compile_requirement_trace sec.(csec_requirements))
    doc.(cd_sections).

(** Build an assurance case from a CONOPS document.
    The top goal is the document title.  Each requirement becomes
    a Goal node.  Sections generate SupportedBy links from the
    top to each requirement.  Assumptions and constraints become
    annotation nodes with InContextOf links. *)
Definition compile_conops (doc : ConopsDocument)
    (top_id : Id) : AssuranceCase * list TraceLink :=
  let top := mkGoal top_id doc.(cd_title) [md_string "source" "CONOPS"] True in
  let section_nodes := compile_document_nodes doc in
  let req_ids := flat_map (fun sec =>
    map cr_id sec.(csec_requirements)) doc.(cd_sections) in
  let asm_ids := flat_map (fun sec =>
    map ca_id sec.(csec_assumptions)) doc.(cd_sections) in
  let support_links := map (supports top_id) req_ids in
  let context_links := map (in_context_of top_id) asm_ids in
  let ac := mkCase top_id
    (top :: section_nodes)
    (support_links ++ context_links) in
  let traces := compile_document_traces doc in
  (ac, traces).

(* ================================================================== *)
(* Preservation: every requirement produces a reachable Goal node      *)
(* ================================================================== *)

Lemma compile_requirement_is_goal : forall cr,
    (compile_requirement cr).(node_kind) = Goal.
Proof. reflexivity. Qed.

Lemma compile_requirement_id : forall cr,
    (compile_requirement cr).(node_id) = cr.(cr_id).
Proof. reflexivity. Qed.

Lemma compiled_reqs_in_nodes : forall doc top_id cr sec,
    In sec doc.(cd_sections) ->
    In cr sec.(csec_requirements) ->
    In (compile_requirement cr)
       (fst (compile_conops doc top_id)).(ac_nodes).
Proof.
  intros doc top_id cr sec Hsec Hcr.
  unfold compile_conops. simpl.
  right. unfold compile_document_nodes.
  apply in_flat_map. exists sec. split; [exact Hsec |].
  unfold compile_section. apply in_or_app. left.
  apply in_map. exact Hcr.
Qed.

Lemma compiled_req_has_trace : forall doc cr sec,
    In sec doc.(cd_sections) ->
    In cr sec.(csec_requirements) ->
    In (compile_requirement_trace cr) (compile_document_traces doc).
Proof.
  intros doc cr sec Hsec Hcr.
  unfold compile_document_traces.
  apply in_flat_map. exists sec. split; [exact Hsec |].
  apply in_map. exact Hcr.
Qed.

Lemma compiled_req_trace_satisfies : forall cr,
    (compile_requirement_trace cr).(tl_kind) = TL_Satisfies.
Proof. reflexivity. Qed.

Lemma compiled_req_trace_source : forall cr,
    (compile_requirement_trace cr).(tl_source) = cr.(cr_id).
Proof. reflexivity. Qed.

(** Every requirement in the CONOPS document produces a Goal node
    that is a direct SupportedBy child of the top goal. *)
Lemma compiled_req_is_child : forall doc top_id cr sec,
    In sec doc.(cd_sections) ->
    In cr sec.(csec_requirements) ->
    In cr.(cr_id) (supportedby_children
      (fst (compile_conops doc top_id)) top_id).
Proof.
  intros doc top_id cr sec Hsec Hcr.
  unfold supportedby_children, compile_conops. simpl.
  apply in_map_iff.
  exists {| link_kind := SupportedBy;
            link_from := top_id;
            link_to := cr.(cr_id) |}.
  split; [reflexivity |].
  apply filter_In. split.
  - apply in_or_app. left.
    apply in_map_iff. exists cr.(cr_id). split; [reflexivity |].
    apply in_flat_map. exists sec. split; [exact Hsec |].
    apply in_map. exact Hcr.
  - simpl. rewrite String.eqb_refl. reflexivity.
Qed.
