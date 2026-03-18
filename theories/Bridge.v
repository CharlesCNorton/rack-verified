(* ------------------------------------------------------------------ *)
(* Typed bridges to external formal methods and modeling tools         *)
(*                                                                    *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Reflect.
From RACK Require Import Trace.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(* ================================================================== *)
(* SysML / AADL intermediate representation                            *)
(* ================================================================== *)

(** Semantic representation for SysML/AADL model elements.
    Preserves element identity and source location for
    trace-preserving import, not just format ingestion. *)

Inductive ModelElementKind : Type :=
  | ME_Block          (* SysML Block / AADL system *)
  | ME_Requirement    (* SysML Requirement *)
  | ME_Constraint     (* SysML Constraint Block *)
  | ME_Interface      (* AADL port / SysML FlowPort *)
  | ME_Connection     (* AADL connection / SysML connector *)
  | ME_Property.      (* AADL property / SysML value property *)

Definition ModelElementKind_eqb (a b : ModelElementKind) : bool :=
  match a, b with
  | ME_Block, ME_Block
  | ME_Requirement, ME_Requirement
  | ME_Constraint, ME_Constraint
  | ME_Interface, ME_Interface
  | ME_Connection, ME_Connection
  | ME_Property, ME_Property => true
  | _, _ => false
  end.

Record ModelElement : Type := {
  me_id       : string;
  me_kind     : ModelElementKind;
  me_name     : string;
  me_text     : string;       (* requirement text or description *)
  me_source   : string;       (* source file path *)
  me_line     : nat;          (* source line number *)
  me_parent   : option string; (* containing element ID *)
}.

Record ModelRelation : Type := {
  mr_source : string;
  mr_target : string;
  mr_kind   : string;  (* "satisfy", "derive", "refine", "trace" *)
}.

Record ModelImport : Type := {
  mi_elements  : list ModelElement;
  mi_relations : list ModelRelation;
  mi_format    : string; (* "SysML", "AADL", "ReqIF" *)
}.

(** Compile a model import into assurance case nodes and trace links.
    Requirements become Goal nodes.  Constraints become Assumption nodes.
    Blocks become Context nodes.  Relations become trace links. *)
Definition compile_model_element (me : ModelElement) : Node := {|
  node_id := me.(me_id);
  node_kind := match me.(me_kind) with
    | ME_Requirement => Goal
    | ME_Constraint  => Assumption
    | ME_Block       => Context
    | ME_Interface   => Context
    | ME_Connection  => Context
    | ME_Property    => Context
    end;
  node_claim_text := me.(me_text);
  node_evidence := None;
  node_metadata :=
    [("source", MVString me.(me_source));
     ("line", MVNat me.(me_line));
     ("model_kind", MVString (match me.(me_kind) with
       | ME_Block => "block" | ME_Requirement => "requirement"
       | ME_Constraint => "constraint" | ME_Interface => "interface"
       | ME_Connection => "connection" | ME_Property => "property"
       end));
     ("import_format", MVString "SysML/AADL")];
  node_claim := True;
|}.

Definition compile_model_relation (mr : ModelRelation) : TraceLink := {|
  tl_kind := if String.eqb mr.(mr_kind) "satisfy" then TL_Satisfies
             else if String.eqb mr.(mr_kind) "derive" then TL_Satisfies
             else TL_ImplementedBy;
  tl_source := mr.(mr_source);
  tl_target := mr.(mr_target);
|}.

Definition import_model (mi : ModelImport)
    (existing : AssuranceCase) : AssuranceCase * list TraceLink :=
  let new_nodes := map compile_model_element mi.(mi_elements) in
  let new_traces := map compile_model_relation mi.(mi_relations) in
  ({| ac_nodes := app existing.(ac_nodes) new_nodes;
      ac_links := existing.(ac_links);
      ac_top := existing.(ac_top); |},
   new_traces).

(** Import preserves existing nodes. *)
Lemma find_app_some : forall {A} (f : A -> bool) l1 l2 x,
    find f l1 = Some x -> find f (app l1 l2) = Some x.
Proof.
  intros A f l1. induction l1 as [|a l1' IH]; intros l2 x H; simpl in *.
  - discriminate.
  - destruct (f a); [exact H | exact (IH l2 x H)].
Qed.

Lemma import_preserves_nodes : forall mi ac id n,
    find_node ac id = Some n ->
    find_node (fst (import_model mi ac)) id = Some n.
Proof.
  intros mi ac id n H. unfold import_model, find_node. simpl.
  apply find_app_some. exact H.
Qed.

(* ================================================================== *)
(* Alloy bridge                                                        *)
(* ================================================================== *)

(** Structured counterexample shared across tool bridges. *)
Record Counterexample : Type := {
  cx_tool      : string;
  cx_property  : string;
  cx_witness   : string;
  cx_timestamp : string;
}.

(** Alloy analysis results: structured relations, scopes, and
    counterexamples as semantically meaningful objects. *)

Inductive AlloyOutcome : Type :=
  | AlloyNoCounterexample  (* within scope, property holds *)
  | AlloyCounterexample    (* counterexample found *)
  | AlloyTimeout.          (* analysis did not complete *)

Record AlloyResult : Type := {
  ar_property     : string;    (* Alloy assertion name *)
  ar_scope        : nat;       (* scope bound *)
  ar_outcome      : AlloyOutcome;
  ar_relations    : list (string * list (string * string));
  ar_counterexample : option Counterexample;
  ar_solver       : string;    (* SAT solver used *)
  ar_time_ms      : nat;       (* analysis time *)
}.

(** Convert an Alloy result to evidence.  A NoCounterexample within
    scope becomes valid Certificate evidence.  A Counterexample
    becomes an invalidation witness. *)
Definition alloy_to_evidence (ar : AlloyResult) : option Evidence :=
  match ar.(ar_outcome) with
  | AlloyNoCounterexample =>
    let blob := "Alloy:" ++ ar.(ar_property) ++
                ":scope=" ++ ar.(ar_solver) ++
                ":no_cex" in
    Some (Certificate blob "Alloy"
      (fun s => String.eqb s blob))
  | AlloyCounterexample => None  (* counterexample = no evidence *)
  | AlloyTimeout => None         (* timeout = no evidence *)
  end.

(** Map Alloy counterexample to invalidation. *)
Definition alloy_to_invalidation (ar : AlloyResult)
    (claim_id : Id) (tg : TraceGraph) : option (list Id) :=
  match ar.(ar_outcome) with
  | AlloyCounterexample =>
    Some (claim_id :: reachable_from tg.(tg_case) claim_id)
  | _ => None
  end.

(** Alloy trust metadata. *)
Definition alloy_trust_metadata (ar : AlloyResult)
    : list (string * MetadataValue) :=
  [("tool", MVString "Alloy");
   ("solver", MVString ar.(ar_solver));
   ("scope", MVNat ar.(ar_scope));
   ("property", MVString ar.(ar_property))].

(* ================================================================== *)
(* Verus bridge                                                        *)
(* ================================================================== *)

(** Verus verification results: preconditions, postconditions,
    invariants, and proof outcomes linked to program items. *)

Inductive VerusOutcome : Type :=
  | VerusVerified     (* all assertions proved *)
  | VerusFailed       (* some assertion failed *)
  | VerusTimeout.

Record VerusCondition : Type := {
  vc_kind : string;    (* "requires", "ensures", "invariant" *)
  vc_text : string;    (* condition text *)
  vc_file : string;
  vc_line : nat;
}.

Record VerusResult : Type := {
  vr_function     : string;
  vr_module       : string;
  vr_preconditions  : list VerusCondition;
  vr_postconditions : list VerusCondition;
  vr_invariants     : list VerusCondition;
  vr_outcome      : VerusOutcome;
  vr_time_ms      : nat;
  vr_diagnostics  : list string;
}.

Definition verus_to_evidence (vr : VerusResult) : option Evidence :=
  match vr.(vr_outcome) with
  | VerusVerified =>
    let blob := "Verus:" ++ vr.(vr_module) ++ "::" ++
                vr.(vr_function) ++ ":verified" in
    Some (Certificate blob "Verus"
      (fun s => String.eqb s blob))
  | VerusFailed => None
  | VerusTimeout => None
  end.

Definition verus_trust_metadata (vr : VerusResult)
    : list (string * MetadataValue) :=
  [("tool", MVString "Verus");
   ("function", MVString vr.(vr_function));
   ("module", MVString vr.(vr_module))].

(* ================================================================== *)
(* Kani bridge                                                         *)
(* ================================================================== *)

(** Kani bounded model checking results: bounds, assumptions,
    harness identity, unwind parameters, and counterexamples. *)

Inductive KaniOutcome : Type :=
  | KaniSuccess
  | KaniFailure
  | KaniUnwind.   (* hit unwind bound *)

Record KaniResult : Type := {
  kr_harness     : string;
  kr_function    : string;
  kr_unwind      : nat;
  kr_outcome     : KaniOutcome;
  kr_assumptions : list string;
  kr_counterexample : option Counterexample;
  kr_time_ms     : nat;
}.

Definition kani_to_evidence (kr : KaniResult) : option Evidence :=
  match kr.(kr_outcome) with
  | KaniSuccess =>
    let blob := "Kani:" ++ kr.(kr_harness) ++ ":" ++
                kr.(kr_function) ++ ":success" in
    Some (Certificate blob "Kani"
      (fun s => String.eqb s blob))
  | KaniFailure => None
  | KaniUnwind => None
  end.

Definition kani_trust_metadata (kr : KaniResult)
    : list (string * MetadataValue) :=
  [("tool", MVString "Kani");
   ("harness", MVString kr.(kr_harness));
   ("function", MVString kr.(kr_function));
   ("unwind", MVNat kr.(kr_unwind))].

(* ================================================================== *)
(* SAW bridge                                                          *)
(* ================================================================== *)

(** SAW verification results: verified functions, binary artifacts,
    proof obligations with provenance and replay conditions. *)

Inductive SAWOutcome : Type :=
  | SAWVerified
  | SAWFailed
  | SAWTimeout.

Record SAWResult : Type := {
  sr_function    : string;
  sr_spec        : string;     (* SAW spec name *)
  sr_binary      : string;     (* path to verified binary *)
  sr_outcome     : SAWOutcome;
  sr_solver      : string;     (* backend solver *)
  sr_replay_cmd  : string;     (* command to replay *)
  sr_time_ms     : nat;
}.

Definition saw_to_evidence (sr : SAWResult) : option Evidence :=
  match sr.(sr_outcome) with
  | SAWVerified =>
    let blob := "SAW:" ++ sr.(sr_function) ++ ":" ++
                sr.(sr_spec) ++ ":verified" in
    Some (Certificate blob "SAW"
      (fun s => String.eqb s blob))
  | SAWFailed => None
  | SAWTimeout => None
  end.

Definition saw_trust_metadata (sr : SAWResult)
    : list (string * MetadataValue) :=
  [("tool", MVString "SAW");
   ("function", MVString sr.(sr_function));
   ("spec", MVString sr.(sr_spec));
   ("binary", MVString sr.(sr_binary));
   ("solver", MVString sr.(sr_solver));
   ("replay", MVString sr.(sr_replay_cmd))].

(* ================================================================== *)
(* Generic bridge: convert any tool result to a Solution node          *)
(* ================================================================== *)

Definition tool_result_to_node (id claim_text : string)
    (ev : Evidence) (md : list (string * MetadataValue))
    : Node := {|
  node_id := id;
  node_kind := Solution;
  node_claim_text := claim_text;
  node_evidence := Some ev;
  node_metadata := md;
  node_claim := True;
|}.

(** Attach a tool result to an existing assurance case by adding
    a Solution node and a SupportedBy link from the parent. *)
Definition attach_tool_result (ac : AssuranceCase)
    (parent_id : Id) (result_node : Node) : AssuranceCase := {|
  ac_nodes := app ac.(ac_nodes) [result_node];
  ac_links := app ac.(ac_links)
    [{| link_kind := SupportedBy;
        link_from := parent_id;
        link_to := result_node.(node_id) |}];
  ac_top := ac.(ac_top);
|}.
