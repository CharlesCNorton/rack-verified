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

Lemma TraceLinkKind_eqb_eq : forall a b,
    TraceLinkKind_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intro; try reflexivity; try discriminate.
Qed.

Definition TraceLinkKind_eq_dec : forall a b : TraceLinkKind, {a = b} + {a <> b}.
Proof. decide equality. Defined.

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
(* Reverse trace lookup                                                *)
(* ================================================================== *)

(** Given an evidence node, find which requirements it satisfies
    by following trace links backward. *)
Definition trace_reverse_lookup (tg : TraceGraph) (evidence_id : Id)
    : list Id :=
  map tl_source
    (filter (fun tl =>
      TraceLinkKind_eqb tl.(tl_kind) TL_VerifiedBy &&
      String.eqb tl.(tl_target) evidence_id)
    tg.(tg_trace_links)).

(** General backward closure: given a node ID, find all requirements
    reachable by reversing Satisfies/VerifiedBy chains. *)
Definition trace_requirements_for (tg : TraceGraph) (node_id : Id)
    : list Id :=
  let verified_claims :=
    map tl_source
      (filter (fun tl =>
        TraceLinkKind_eqb tl.(tl_kind) TL_VerifiedBy &&
        String.eqb tl.(tl_target) node_id)
      tg.(tg_trace_links)) in
  flat_map (fun claim_id =>
    map tl_source
      (filter (fun tl =>
        TraceLinkKind_eqb tl.(tl_kind) TL_Satisfies &&
        String.eqb tl.(tl_target) claim_id)
      tg.(tg_trace_links)))
  (node_id :: verified_claims).

(* ================================================================== *)
(* Trace coverage                                                      *)
(* ================================================================== *)

(** A requirement has complete evidence when there exists a chain
    Satisfies -> VerifiedBy -> ProducedBy. *)
Definition requirement_covered (tg : TraceGraph) (rid : RequirementId)
    : bool :=
  let claim_targets :=
    map tl_target
      (filter (fun tl =>
        TraceLinkKind_eqb tl.(tl_kind) TL_Satisfies &&
        String.eqb tl.(tl_source) rid.(req_id))
      tg.(tg_trace_links)) in
  let evidence_targets :=
    flat_map (fun cid =>
      map tl_target
        (filter (fun tl =>
          TraceLinkKind_eqb tl.(tl_kind) TL_VerifiedBy &&
          String.eqb tl.(tl_source) cid)
        tg.(tg_trace_links)))
    claim_targets in
  existsb (fun eid =>
    existsb (fun tl =>
      TraceLinkKind_eqb tl.(tl_kind) TL_ProducedBy &&
      String.eqb tl.(tl_source) eid)
    tg.(tg_trace_links))
  evidence_targets.

(** Check that every requirement has complete evidence chains. *)
Definition check_trace_complete (tg : TraceGraph) : bool :=
  forallb (requirement_covered tg) tg.(tg_requirements).

(** Coverage fraction: count of covered requirements / total. *)
Definition trace_coverage_count (tg : TraceGraph) : nat * nat :=
  (length (filter (requirement_covered tg) tg.(tg_requirements)),
   length tg.(tg_requirements)).

(* ================================================================== *)
(* Trace freshness checker                                             *)
(* ================================================================== *)

Definition check_trace_fresh (tg : TraceGraph) (now : string) : bool :=
  forallb (fun tl =>
    match tl.(tl_kind) with
    | TL_VerifiedBy =>
      match find_node tg.(tg_case) tl.(tl_target) with
      | Some n =>
        match find_metadata "valid_until" n.(node_metadata) with
        | Some (MVTimestamp expiry) => negb (string_ltb expiry now)
        | Some (MVString expiry) => negb (string_ltb expiry now)
        | _ => true
        end
      | None => false
      end
    | _ => true
    end) tg.(tg_trace_links).

Lemma check_trace_fresh_correct : forall tg now,
    check_trace_fresh tg now = true -> trace_fresh tg now.
Proof.
  intros tg now H tl Hin Hkind.
  unfold check_trace_fresh in H.
  apply forallb_forall with (x := tl) in H; [| exact Hin].
  rewrite Hkind in H.
  destruct (find_node tg.(tg_case) tl.(tl_target)); [| discriminate].
  destruct (find_metadata "valid_until" n.(node_metadata)) as [[| | |s]|];
    try exact I; exact H.
Qed.

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

(* ================================================================== *)
(* check_trace_total_correct                                          *)
(* ================================================================== *)

Lemma check_trace_total_correct : forall tg,
    check_trace_total tg = true -> trace_total tg.
Proof.
  intros tg H r Hin.
  unfold check_trace_total in H.
  apply forallb_forall with (x := r) in H; [| exact Hin].
  apply existsb_exists in H. destruct H as [tl [Htlin Hcond]].
  apply Bool.andb_true_iff in Hcond. destruct Hcond as [Hkind Hsrc].
  exists tl. repeat split.
  - exact Htlin.
  - destruct tl.(tl_kind); try discriminate. reflexivity.
  - exact Hsrc.
Qed.

(* ================================================================== *)
(* check_trace_provenance_correct                                     *)
(* ================================================================== *)

Lemma check_trace_provenance_correct : forall tg,
    check_trace_provenance tg = true -> trace_provenance tg.
Proof.
  intros tg H n Hin Hkind.
  unfold check_trace_provenance in H.
  apply forallb_forall with (x := n) in H; [| exact Hin].
  rewrite Hkind in H.
  apply existsb_exists in H. destruct H as [tl [Htlin Hcond]].
  apply Bool.andb_true_iff in Hcond. destruct Hcond as [Htkind Hsrc].
  exists tl. repeat split.
  - exact Htlin.
  - destruct tl.(tl_kind); try discriminate. reflexivity.
  - exact Hsrc.
Qed.

(* ================================================================== *)
(* Invalidation soundness                                              *)
(* ================================================================== *)

(** Helper: every id in [reachable_set_fuel] is either in the
    accumulator or is a link target, hence exists when
    [no_dangling_links] holds. *)
Lemma rsf_nodes_exist : forall ac fuel frontier acc,
    no_dangling_links ac ->
    (forall id, In id acc -> exists n, find_node ac id = Some n) ->
    (forall id, In id frontier -> exists n, find_node ac id = Some n) ->
    forall id, In id (reachable_set_fuel ac fuel frontier acc) ->
    exists n, find_node ac id = Some n.
Proof.
  intros ac fuel. induction fuel as [|f IH];
    intros frontier acc Hnd Hacc Hfront id Hin.
  - simpl in Hin. exact (Hacc id Hin).
  - simpl in Hin.
    remember (filter (fun id0 => negb (mem_string id0 acc))
               (flat_map (supportedby_children ac) frontier)) as fresh.
    destruct fresh as [|h t].
    + exact (Hacc id Hin).
    + apply IH in Hin; [exact Hin | exact Hnd | |].
      * intros id' Hin'. apply in_app_iff in Hin'.
        destruct Hin' as [Hin' | Hin'].
        -- exact (Hacc id' Hin').
        -- rewrite Heqfresh in Hin'.
           apply filter_In in Hin'. destruct Hin' as [Hin' _].
           apply in_flat_map in Hin'.
           destruct Hin' as [parent [_ Hchild]].
           unfold supportedby_children in Hchild.
           apply in_map_iff in Hchild.
           destruct Hchild as [l [<- Hlin']].
           apply filter_In in Hlin'. destruct Hlin' as [Hlin' _].
           destruct (Hnd l Hlin') as [_ [nt Hnt]].
           exists nt. exact Hnt.
      * intros id' Hin'. rewrite Heqfresh in Hin'.
        apply filter_In in Hin'. destruct Hin' as [Hin' _].
        apply in_flat_map in Hin'.
        destruct Hin' as [parent [_ Hchild]].
        unfold supportedby_children in Hchild.
        apply in_map_iff in Hchild.
        destruct Hchild as [l [<- Hlin']].
        apply filter_In in Hlin'. destruct Hlin' as [Hlin' _].
        destruct (Hnd l Hlin') as [_ [nt Hnt]].
        exists nt. exact Hnt.
Qed.

Lemma reachable_from_exists : forall ac start,
    no_dangling_links ac ->
    (exists n, find_node ac start = Some n) ->
    forall id, In id (reachable_from ac start) ->
    exists n, find_node ac id = Some n.
Proof.
  intros ac start Hnd [ns Hns] id Hin.
  unfold reachable_from in Hin.
  apply rsf_nodes_exist in Hin; [exact Hin | exact Hnd | |].
  - intros id' Hin'.
    unfold supportedby_children in Hin'.
    apply in_map_iff in Hin'.
    destruct Hin' as [l [<- Hlin']].
    apply filter_In in Hlin'. destruct Hlin' as [Hlin' _].
    destruct (Hnd l Hlin') as [_ [nt Hnt]].
    exists nt. exact Hnt.
  - intros id' Hin'.
    unfold supportedby_children in Hin'.
    apply in_map_iff in Hin'.
    destruct Hin' as [l [<- Hlin']].
    apply filter_In in Hlin'. destruct Hlin' as [Hlin' _].
    destruct (Hnd l Hlin') as [_ [nt Hnt]].
    exists nt. exact Hnt.
Qed.

(** Stale nodes from [invalidate_requirement] exist in the case. *)
Lemma invalidate_requirement_sound : forall tg rid,
    no_dangling_links tg.(tg_case) ->
    (forall tl, In tl tg.(tg_trace_links) ->
      tl.(tl_kind) = TL_Satisfies ->
      exists n, find_node tg.(tg_case) tl.(tl_target) = Some n) ->
    invalidation_sound tg (invalidate_requirement tg rid).
Proof.
  intros tg rid Hnd Htrace id Hin.
  unfold invalidate_requirement in Hin. simpl in Hin.
  apply in_flat_map in Hin. destruct Hin as [claim_id [Hclaim Hin_reach]].
  apply in_map_iff in Hclaim. destruct Hclaim as [tl [Htgt Htlin]].
  apply filter_In in Htlin. destruct Htlin as [Htlin Hcond].
  apply Bool.andb_true_iff in Hcond. destruct Hcond as [Hkind _].
  subst claim_id.
  assert (Hkind_eq : tl.(tl_kind) = TL_Satisfies).
  { destruct tl.(tl_kind); try discriminate. reflexivity. }
  destruct (Htrace tl Htlin Hkind_eq) as [nc Hfnc].
  destruct Hin_reach as [<- | Hreach].
  - exists nc. exact Hfnc.
  - exact (reachable_from_exists tg.(tg_case) tl.(tl_target)
             Hnd (ex_intro _ nc Hfnc) id Hreach).
Qed.

(** Soundness for [invalidate_commit]. *)
Lemma invalidate_commit_sound : forall tg cid,
    no_dangling_links tg.(tg_case) ->
    (forall tl, In tl tg.(tg_trace_links) ->
      tl.(tl_kind) = TL_ImplementedBy ->
      exists n, find_node tg.(tg_case) tl.(tl_source) = Some n) ->
    invalidation_sound tg (invalidate_commit tg cid).
Proof.
  intros tg cid Hnd Htrace id Hin.
  unfold invalidate_commit in Hin. simpl in Hin.
  apply in_flat_map in Hin. destruct Hin as [claim_id [Hclaim Hin_reach]].
  apply in_flat_map in Hclaim. destruct Hclaim as [art [Hart Hclaim']].
  apply in_map_iff in Hclaim'. destruct Hclaim' as [tl [Hsrc Htlin']].
  apply filter_In in Htlin'. destruct Htlin' as [Htlin' Hcond'].
  apply Bool.andb_true_iff in Hcond'. destruct Hcond' as [Hkind' _].
  subst claim_id.
  assert (Hkind_eq : tl.(tl_kind) = TL_ImplementedBy).
  { destruct tl.(tl_kind); try discriminate. reflexivity. }
  destruct (Htrace tl Htlin' Hkind_eq) as [nc Hfnc].
  destruct Hin_reach as [<- | Hreach].
  - exists nc. exact Hfnc.
  - exact (reachable_from_exists tg.(tg_case) tl.(tl_source)
             Hnd (ex_intro _ nc Hfnc) id Hreach).
Qed.

(* ================================================================== *)
(* Obligations discharged restores evidence coverage                    *)
(* ================================================================== *)

(** When obligations are discharged and the case structure is unchanged,
    every reachable Solution node has valid evidence. *)
Lemma obligations_cover_solutions : forall tg iw now,
    obligations_discharged tg iw now ->
    (forall id, In id iw.(iw_obligations) <->
      (match find_node tg.(tg_case) id with
       | Some n => n.(node_kind) = Solution
       | None => False
       end /\ In id iw.(iw_stale_nodes))) ->
    forall id, In id iw.(iw_stale_nodes) ->
    match find_node tg.(tg_case) id with
    | Some n =>
      match n.(node_kind) with
      | Solution => exists e, n.(node_evidence) = Some e /\ evidence_valid n e
      | _ => True
      end
    | None => True
    end.
Proof.
  intros tg iw now Hdisch Hobligs id Hstale.
  destruct (find_node tg.(tg_case) id) as [n|] eqn:Hfind.
  - destruct n.(node_kind) eqn:Hkind; try exact I.
    (* Solution *)
    assert (Hoblig : In id iw.(iw_obligations)).
    { apply Hobligs. split; [rewrite Hfind; exact Hkind | exact Hstale]. }
    pose proof (Hdisch id Hoblig) as Hd.
    rewrite Hfind in Hd. destruct Hd as [_ [e [He [Hv _]]]].
    exists e. exact (conj He Hv).
  - exact I.
Qed.
