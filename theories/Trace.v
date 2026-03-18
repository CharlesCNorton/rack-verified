(* ------------------------------------------------------------------ *)
(* Typed traceability calculus and invalidation theory                 *)
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
(* Artifact identifiers                                                *)
(* ================================================================== *)

(** First-class identifier types for traceability.  Each is a
    string-wrapper with distinct semantics.  The wrapper prevents
    accidental confusion between, say, a requirement ID and a
    commit hash. *)

Record RequirementId := { req_id : string }.
Record ArtifactId    := { art_id : string }.
Record CommitId      := { cmt_id : string }.
Record ToolRunId     := { run_id : string }.
Record OwnerId       := { own_id : string }.

Definition RequirementId_eqb (a b : RequirementId) : bool :=
  String.eqb a.(req_id) b.(req_id).
Definition ArtifactId_eqb (a b : ArtifactId) : bool :=
  String.eqb a.(art_id) b.(art_id).
Definition CommitId_eqb (a b : CommitId) : bool :=
  String.eqb a.(cmt_id) b.(cmt_id).

(* ================================================================== *)
(* Trace links                                                         *)
(* ================================================================== *)

(** A [TraceLink] records a typed relationship between artifacts.
    The [tl_kind] field distinguishes the nature of the link. *)
Inductive TraceLinkKind : Type :=
  | TL_Satisfies      (* requirement -> claim *)
  | TL_ImplementedBy  (* claim -> source artifact *)
  | TL_VerifiedBy     (* claim -> evidence node *)
  | TL_ProducedBy     (* evidence -> tool run *)
  | TL_CommittedIn    (* artifact -> commit *)
  | TL_OwnedBy.       (* any -> owner *)

Definition TraceLinkKind_eqb (a b : TraceLinkKind) : bool :=
  match a, b with
  | TL_Satisfies, TL_Satisfies
  | TL_ImplementedBy, TL_ImplementedBy
  | TL_VerifiedBy, TL_VerifiedBy
  | TL_ProducedBy, TL_ProducedBy
  | TL_CommittedIn, TL_CommittedIn
  | TL_OwnedBy, TL_OwnedBy => true
  | _, _ => false
  end.

Record TraceLink : Type := {
  tl_kind   : TraceLinkKind;
  tl_source : string;   (* source artifact/requirement ID *)
  tl_target : string;   (* target artifact/claim/evidence ID *)
}.

(* ================================================================== *)
(* Trace graph                                                         *)
(* ================================================================== *)

(** A [TraceGraph] overlays an [AssuranceCase] with traceability
    information: requirements, artifacts, commits, tool runs,
    ownership, and the links between them. *)
Record TraceGraph : Type := {
  tg_case         : AssuranceCase;
  tg_requirements : list RequirementId;
  tg_artifacts    : list ArtifactId;
  tg_commits      : list CommitId;
  tg_tool_runs    : list ToolRunId;
  tg_owners       : list OwnerId;
  tg_trace_links  : list TraceLink;
}.

(* ================================================================== *)
(* Trace invariants                                                    *)
(* ================================================================== *)

(** Totality: every requirement has at least one Satisfies link. *)
Definition trace_total (tg : TraceGraph) : Prop :=
  forall r, In r tg.(tg_requirements) ->
  exists tl, In tl tg.(tg_trace_links) /\
             tl.(tl_kind) = TL_Satisfies /\
             String.eqb tl.(tl_source) r.(req_id) = true.

(** Uniqueness: no two Satisfies links share the same source and target. *)
Definition trace_unique (tg : TraceGraph) : Prop :=
  forall tl1 tl2,
    In tl1 tg.(tg_trace_links) ->
    In tl2 tg.(tg_trace_links) ->
    tl1.(tl_kind) = TL_Satisfies ->
    tl2.(tl_kind) = TL_Satisfies ->
    String.eqb tl1.(tl_source) tl2.(tl_source) = true ->
    String.eqb tl1.(tl_target) tl2.(tl_target) = true ->
    tl1 = tl2.

(** Freshness: every VerifiedBy link targets a node whose evidence
    is fresh as of [now]. *)
Definition trace_fresh (tg : TraceGraph) (now : string) : Prop :=
  forall tl, In tl tg.(tg_trace_links) ->
    tl.(tl_kind) = TL_VerifiedBy ->
    match find_node tg.(tg_case) tl.(tl_target) with
    | Some n =>
      match find_metadata "valid_until" n.(node_metadata) with
      | Some (MVTimestamp expiry) => negb (string_ltb expiry now) = true
      | Some (MVString expiry) => negb (string_ltb expiry now) = true
      | _ => True
      end
    | None => False
    end.

(** Provenance preservation: every evidence node has a ProducedBy
    link to a tool run. *)
Definition trace_provenance (tg : TraceGraph) : Prop :=
  forall n, In n tg.(tg_case).(ac_nodes) ->
    n.(node_kind) = Solution ->
    exists tl, In tl tg.(tg_trace_links) /\
               tl.(tl_kind) = TL_ProducedBy /\
               String.eqb tl.(tl_source) n.(node_id) = true.

(** A trace graph is well-traced when all invariants hold. *)
Record WellTraced (tg : TraceGraph) (now : string) : Prop := {
  wt_case_wf    : WellFormed tg.(tg_case);
  wt_total      : trace_total tg;
  wt_fresh      : trace_fresh tg now;
  wt_provenance : trace_provenance tg;
}.

(* ================================================================== *)
(* Boolean trace checks                                                *)
(* ================================================================== *)

Definition check_trace_total (tg : TraceGraph) : bool :=
  forallb (fun r =>
    existsb (fun tl =>
      TraceLinkKind_eqb tl.(tl_kind) TL_Satisfies &&
      String.eqb tl.(tl_source) r.(req_id))
    tg.(tg_trace_links))
  tg.(tg_requirements).

Definition check_trace_provenance (tg : TraceGraph) : bool :=
  forallb (fun n =>
    match n.(node_kind) with
    | Solution =>
      existsb (fun tl =>
        TraceLinkKind_eqb tl.(tl_kind) TL_ProducedBy &&
        String.eqb tl.(tl_source) n.(node_id))
      tg.(tg_trace_links)
    | _ => true
    end) tg.(tg_case).(ac_nodes).

(* ================================================================== *)
(* Invalidation theory                                                 *)
(* ================================================================== *)

(** Change kinds that can invalidate claims. *)
Inductive ChangeKind : Type :=
  | RequirementChange : RequirementId -> ChangeKind
  | ArtifactChange    : ArtifactId -> ChangeKind
  | CodeChange        : CommitId -> ChangeKind
  | ToolVersionChange : string -> string -> ChangeKind. (* tool, new ver *)

(** An invalidation witness identifies which nodes are affected
    by a change. *)
Record InvalidationWitness : Type := {
  iw_change        : ChangeKind;
  iw_stale_nodes   : list Id;  (* nodes whose evidence is stale *)
  iw_stale_links   : list TraceLink; (* trace links that are broken *)
  iw_obligations   : list Id;  (* nodes requiring re-validation *)
}.

(** Compute which nodes are affected by a requirement change:
    follow Satisfies links from the requirement to claim nodes,
    then follow SupportedBy links downward to find all evidence
    that supports those claims. *)
Definition invalidate_requirement (tg : TraceGraph)
    (rid : RequirementId) : InvalidationWitness :=
  let affected_claims :=
    map tl_target
      (filter (fun tl =>
        TraceLinkKind_eqb tl.(tl_kind) TL_Satisfies &&
        String.eqb tl.(tl_source) rid.(req_id))
      tg.(tg_trace_links)) in
  let stale_nodes :=
    flat_map (fun claim_id =>
      claim_id :: reachable_from tg.(tg_case) claim_id)
    affected_claims in
  {| iw_change := RequirementChange rid;
     iw_stale_nodes := stale_nodes;
     iw_stale_links := filter (fun tl =>
       existsb (String.eqb tl.(tl_source)) stale_nodes ||
       existsb (String.eqb tl.(tl_target)) stale_nodes)
       tg.(tg_trace_links);
     iw_obligations := filter (fun id =>
       match find_node tg.(tg_case) id with
       | Some n => match n.(node_kind) with
                   | Solution => true | _ => false end
       | None => false
       end) stale_nodes;
  |}.

(** Compute which nodes are affected by a code change:
    follow CommittedIn links from the commit to artifacts,
    then follow ImplementedBy links from artifacts to claims. *)
Definition invalidate_commit (tg : TraceGraph)
    (cid : CommitId) : InvalidationWitness :=
  let affected_artifacts :=
    map tl_source
      (filter (fun tl =>
        TraceLinkKind_eqb tl.(tl_kind) TL_CommittedIn &&
        String.eqb tl.(tl_target) cid.(cmt_id))
      tg.(tg_trace_links)) in
  let affected_claims :=
    flat_map (fun art =>
      map tl_source
        (filter (fun tl =>
          TraceLinkKind_eqb tl.(tl_kind) TL_ImplementedBy &&
          String.eqb tl.(tl_target) art)
        tg.(tg_trace_links)))
    affected_artifacts in
  let stale_nodes :=
    flat_map (fun claim_id =>
      claim_id :: reachable_from tg.(tg_case) claim_id)
    affected_claims in
  {| iw_change := CodeChange cid;
     iw_stale_nodes := stale_nodes;
     iw_stale_links := [];
     iw_obligations := filter (fun id =>
       match find_node tg.(tg_case) id with
       | Some n => match n.(node_kind) with
                   | Solution => true | _ => false end
       | None => false
       end) stale_nodes;
  |}.

(** An invalidation is sound when every stale node is actually
    reachable from a changed artifact. *)
Definition invalidation_sound (tg : TraceGraph)
    (iw : InvalidationWitness) : Prop :=
  forall id, In id iw.(iw_stale_nodes) ->
    exists n, find_node tg.(tg_case) id = Some n.

(** After re-validation: the obligations are discharged when every
    obligation node has valid, fresh evidence. *)
Definition obligations_discharged (tg : TraceGraph)
    (iw : InvalidationWitness) (now : string) : Prop :=
  forall id, In id iw.(iw_obligations) ->
    match find_node tg.(tg_case) id with
    | Some n =>
      n.(node_kind) = Solution /\
      exists e, n.(node_evidence) = Some e /\
                evidence_valid n e /\
                match find_metadata "valid_until" n.(node_metadata) with
                | Some (MVTimestamp expiry) => negb (string_ltb expiry now) = true
                | _ => True
                end
    | None => False
    end.
