(******************************************************************************)
(*                                                                            *)
(*          Rocq Assurance Case Kernel: Full Serialization                    *)
(*                                                                            *)
(*     JSON render/parse for TraceGraph, AssuranceDelta, ProductLineCase.    *)
(*                                                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 19, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From RACK Require Import Core.
From RACK Require Import Json.
From RACK Require Import ExportUtil.
From RACK Require Import Trace.
From RACK Require Import Delta.
From RACK Require Import ProductLine.
From RACK Require Import EvidenceClass.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* ================================================================== *)
(* Trace serialization (TODO item 4)                                   *)
(* ================================================================== *)

Definition trace_link_kind_to_json (k : TraceLinkKind) : Json :=
  JStr match k with
  | TL_Satisfies     => "Satisfies"
  | TL_ImplementedBy => "ImplementedBy"
  | TL_VerifiedBy    => "VerifiedBy"
  | TL_ProducedBy    => "ProducedBy"
  | TL_CommittedIn   => "CommittedIn"
  | TL_OwnedBy       => "OwnedBy"
  end.

Definition trace_link_to_json (tl : TraceLink) : Json :=
  JObj [("kind", trace_link_kind_to_json tl.(tl_kind));
        ("source", JStr tl.(tl_source));
        ("target", JStr tl.(tl_target))].

Definition trace_graph_to_json (tg : TraceGraph) : Json :=
  JObj [("case", assurance_case_to_json tg.(tg_case));
        ("requirements",
          JArr (map (fun r => JStr r.(req_id)) tg.(tg_requirements)));
        ("artifacts",
          JArr (map (fun a => JStr a.(art_id)) tg.(tg_artifacts)));
        ("commits",
          JArr (map (fun c => JStr c.(cmt_id)) tg.(tg_commits)));
        ("tool_runs",
          JArr (map (fun t => JStr t.(run_id)) tg.(tg_tool_runs)));
        ("owners",
          JArr (map (fun o => JStr o.(own_id)) tg.(tg_owners)));
        ("trace_links",
          JArr (map trace_link_to_json tg.(tg_trace_links)))].

Definition render_trace_graph (tg : TraceGraph) : string :=
  render_json (trace_graph_to_json tg).

Definition render_trace_graph_pretty (tg : TraceGraph) : string :=
  render_json_pretty (trace_graph_to_json tg).

(* --- Trace parse --- *)

Definition json_to_trace_link_kind (j : Json) : option TraceLinkKind :=
  match j with
  | JStr s =>
    if String.eqb s "Satisfies" then Some TL_Satisfies
    else if String.eqb s "ImplementedBy" then Some TL_ImplementedBy
    else if String.eqb s "VerifiedBy" then Some TL_VerifiedBy
    else if String.eqb s "ProducedBy" then Some TL_ProducedBy
    else if String.eqb s "CommittedIn" then Some TL_CommittedIn
    else if String.eqb s "OwnedBy" then Some TL_OwnedBy
    else None
  | _ => None
  end.

Definition json_to_trace_link (j : Json) : option TraceLink :=
  match j with
  | JObj kvs =>
    match json_field "kind" kvs,
          json_field "source" kvs,
          json_field "target" kvs with
    | Some kind_json, Some (JStr src), Some (JStr tgt) =>
      match json_to_trace_link_kind kind_json with
      | Some k => Some {| tl_kind := k;
                          tl_source := src;
                          tl_target := tgt |}
      | None => None
      end
    | _, _, _ => None
    end
  | _ => None
  end.

Fixpoint json_to_string_list (js : list Json) : option (list string) :=
  match js with
  | nil => Some nil
  | JStr s :: rest =>
    match json_to_string_list rest with
    | Some ss => Some (s :: ss)
    | None => None
    end
  | _ => None
  end.

Definition json_to_trace_graph (j : Json) : option TraceGraph :=
  match j with
  | JObj kvs =>
    match json_field "case" kvs,
          json_field "requirements" kvs,
          json_field "artifacts" kvs,
          json_field "commits" kvs,
          json_field "tool_runs" kvs,
          json_field "owners" kvs,
          json_field "trace_links" kvs with
    | Some case_json, Some (JArr req_js), Some (JArr art_js),
      Some (JArr cmt_js), Some (JArr run_js), Some (JArr own_js),
      Some (JArr tl_js) =>
      match json_to_assurance_case case_json,
            json_to_string_list req_js,
            json_to_string_list art_js,
            json_to_string_list cmt_js,
            json_to_string_list run_js,
            json_to_string_list own_js,
            json_list_map json_to_trace_link tl_js with
      | Some ac, Some reqs, Some arts, Some cmts,
        Some runs, Some owns, Some tls =>
        Some {| tg_case := ac;
                tg_requirements := map (fun s => {| req_id := s |}) reqs;
                tg_artifacts := map (fun s => {| art_id := s |}) arts;
                tg_commits := map (fun s => {| cmt_id := s |}) cmts;
                tg_tool_runs := map (fun s => {| run_id := s |}) runs;
                tg_owners := map (fun s => {| own_id := s |}) owns;
                tg_trace_links := tls |}
      | _, _, _, _, _, _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _ => None
  end.

(* ================================================================== *)
(* Delta serialization (TODO item 5)                                   *)
(* ================================================================== *)

Definition node_change_to_json (nc : NodeChange) : Json :=
  match nc with
  | AddNode n =>
    JObj [("op", JStr "AddNode"); ("node", node_to_json n)]
  | RemoveNode id =>
    JObj [("op", JStr "RemoveNode"); ("id", JStr id)]
  | UpdateEvidence id ev =>
    JObj [("op", JStr "UpdateEvidence");
          ("id", JStr id);
          ("evidence", evidence_to_json ev)]
  end.

Definition link_change_to_json (lc : LinkChange) : Json :=
  match lc with
  | AddLink l =>
    JObj [("op", JStr "AddLink"); ("link", link_to_json l)]
  | RemoveLink from to_ =>
    JObj [("op", JStr "RemoveLink");
          ("from", JStr from); ("to", JStr to_)]
  end.

Definition trace_change_to_json (tc : TraceChange) : Json :=
  match tc with
  | AddTrace tl =>
    JObj [("op", JStr "AddTrace"); ("trace_link", trace_link_to_json tl)]
  | RemoveTrace tl =>
    JObj [("op", JStr "RemoveTrace"); ("trace_link", trace_link_to_json tl)]
  end.

Definition assurance_delta_to_json (delta : AssuranceDelta) : Json :=
  JObj [("node_changes",
          JArr (map node_change_to_json delta.(ad_node_changes)));
        ("link_changes",
          JArr (map link_change_to_json delta.(ad_link_changes)));
        ("trace_changes",
          JArr (map trace_change_to_json delta.(ad_trace_changes)));
        ("commit",
          match delta.(ad_commit) with
          | Some c => JStr c.(cmt_id)
          | None => JNull
          end);
        ("description", JStr delta.(ad_description))].

Definition render_delta (delta : AssuranceDelta) : string :=
  render_json (assurance_delta_to_json delta).

Definition render_delta_pretty (delta : AssuranceDelta) : string :=
  render_json_pretty (assurance_delta_to_json delta).

(* --- Delta parse --- *)

Definition json_to_node_change (j : Json) : option NodeChange :=
  match j with
  | JObj kvs =>
    match json_field "op" kvs with
    | Some (JStr op) =>
      if String.eqb op "AddNode" then
        match json_field "node" kvs with
        | Some node_json =>
          match json_to_node node_json with
          | Some n => Some (AddNode n)
          | None => None
          end
        | None => None
        end
      else if String.eqb op "RemoveNode" then
        match json_field "id" kvs with
        | Some (JStr id) => Some (RemoveNode id)
        | _ => None
        end
      else if String.eqb op "UpdateEvidence" then
        (* UpdateEvidence requires a validator function which cannot be
           parsed from JSON. Import as RemoveNode + AddNode instead,
           or use hydrate_evidence after import. *)
        None
      else None
    | _ => None
    end
  | _ => None
  end.

Definition json_to_link_change (j : Json) : option LinkChange :=
  match j with
  | JObj kvs =>
    match json_field "op" kvs with
    | Some (JStr op) =>
      if String.eqb op "AddLink" then
        match json_field "link" kvs with
        | Some link_json =>
          match json_to_link link_json with
          | Some l => Some (AddLink l)
          | None => None
          end
        | None => None
        end
      else if String.eqb op "RemoveLink" then
        match json_field "from" kvs, json_field "to" kvs with
        | Some (JStr from), Some (JStr to_) =>
          Some (RemoveLink from to_)
        | _, _ => None
        end
      else None
    | _ => None
    end
  | _ => None
  end.

Definition json_to_trace_change (j : Json) : option TraceChange :=
  match j with
  | JObj kvs =>
    match json_field "op" kvs with
    | Some (JStr op) =>
      if String.eqb op "AddTrace" then
        match json_field "trace_link" kvs with
        | Some tl_json =>
          match json_to_trace_link tl_json with
          | Some tl => Some (AddTrace tl)
          | None => None
          end
        | None => None
        end
      else if String.eqb op "RemoveTrace" then
        match json_field "trace_link" kvs with
        | Some tl_json =>
          match json_to_trace_link tl_json with
          | Some tl => Some (RemoveTrace tl)
          | None => None
          end
        | None => None
        end
      else None
    | _ => None
    end
  | _ => None
  end.

Definition json_to_assurance_delta (j : Json) : option AssuranceDelta :=
  match j with
  | JObj kvs =>
    match json_field "node_changes" kvs,
          json_field "link_changes" kvs,
          json_field "trace_changes" kvs,
          json_field "description" kvs with
    | Some (JArr nc_js), Some (JArr lc_js),
      Some (JArr tc_js), Some (JStr desc) =>
      match json_list_map json_to_node_change nc_js,
            json_list_map json_to_link_change lc_js,
            json_list_map json_to_trace_change tc_js with
      | Some ncs, Some lcs, Some tcs =>
        let commit :=
          match json_field "commit" kvs with
          | Some (JStr cid) => Some {| cmt_id := cid |}
          | _ => None
          end in
        Some {| ad_node_changes := ncs;
                ad_link_changes := lcs;
                ad_trace_changes := tcs;
                ad_commit := commit;
                ad_description := desc |}
      | _, _, _ => None
      end
    | _, _, _, _ => None
    end
  | _ => None
  end.

(* ================================================================== *)
(* Feature / product-line serialization (TODO item 7)                  *)
(* ================================================================== *)

Fixpoint feature_expr_to_json (fe : FeatureExpr) : Json :=
  match fe with
  | FEAtom f => JObj [("type", JStr "Atom"); ("feature", JStr f)]
  | FETrue   => JObj [("type", JStr "True")]
  | FEFalse  => JObj [("type", JStr "False")]
  | FEAnd a b =>
    JObj [("type", JStr "And");
          ("left", feature_expr_to_json a);
          ("right", feature_expr_to_json b)]
  | FEOr a b =>
    JObj [("type", JStr "Or");
          ("left", feature_expr_to_json a);
          ("right", feature_expr_to_json b)]
  | FENot a =>
    JObj [("type", JStr "Not");
          ("expr", feature_expr_to_json a)]
  end.

Definition annotated_node_to_json (an : AnnotatedNode) : Json :=
  JObj [("node", node_to_json an.(an_node));
        ("feature", feature_expr_to_json an.(an_feature))].

Definition annotated_link_to_json (al : AnnotatedLink) : Json :=
  JObj [("link", link_to_json al.(al_link));
        ("feature", feature_expr_to_json al.(al_feature))].

Definition feature_model_to_json (fm : FeatureModel) : Json :=
  JObj [("features", JArr (map JStr fm.(fm_features)));
        ("mandatory", JArr (map JStr fm.(fm_mandatory)));
        ("constraints",
          JArr (map feature_expr_to_json fm.(fm_constraints)))].

Definition product_line_case_to_json (plc : ProductLineCase) : Json :=
  JObj [("top", JStr plc.(plc_top));
        ("nodes", JArr (map annotated_node_to_json plc.(plc_nodes)));
        ("links", JArr (map annotated_link_to_json plc.(plc_links)));
        ("feature_model", feature_model_to_json plc.(plc_fm))].

Definition render_product_line_case (plc : ProductLineCase) : string :=
  render_json (product_line_case_to_json plc).

Definition render_product_line_case_pretty (plc : ProductLineCase) : string :=
  render_json_pretty (product_line_case_to_json plc).

(* --- Feature parse --- *)

Fixpoint json_to_feature_expr (fuel : nat) (j : Json) : option FeatureExpr :=
  match fuel with
  | 0 => None
  | S f =>
    match j with
    | JObj kvs =>
      match json_field "type" kvs with
      | Some (JStr ty) =>
        if String.eqb ty "Atom" then
          match json_field "feature" kvs with
          | Some (JStr feat) => Some (FEAtom feat)
          | _ => None
          end
        else if String.eqb ty "True" then Some FETrue
        else if String.eqb ty "False" then Some FEFalse
        else if String.eqb ty "And" then
          match json_field "left" kvs, json_field "right" kvs with
          | Some lj, Some rj =>
            match json_to_feature_expr f lj,
                  json_to_feature_expr f rj with
            | Some l, Some r => Some (FEAnd l r)
            | _, _ => None
            end
          | _, _ => None
          end
        else if String.eqb ty "Or" then
          match json_field "left" kvs, json_field "right" kvs with
          | Some lj, Some rj =>
            match json_to_feature_expr f lj,
                  json_to_feature_expr f rj with
            | Some l, Some r => Some (FEOr l r)
            | _, _ => None
            end
          | _, _ => None
          end
        else if String.eqb ty "Not" then
          match json_field "expr" kvs with
          | Some ej =>
            match json_to_feature_expr f ej with
            | Some e => Some (FENot e)
            | None => None
            end
          | None => None
          end
        else None
      | _ => None
      end
    | _ => None
    end
  end.

Definition json_to_annotated_node (j : Json) : option AnnotatedNode :=
  match j with
  | JObj kvs =>
    match json_field "node" kvs, json_field "feature" kvs with
    | Some nj, Some fj =>
      match json_to_node nj, json_to_feature_expr 100 fj with
      | Some n, Some fe => Some {| an_node := n; an_feature := fe |}
      | _, _ => None
      end
    | _, _ => None
    end
  | _ => None
  end.

Definition json_to_annotated_link (j : Json) : option AnnotatedLink :=
  match j with
  | JObj kvs =>
    match json_field "link" kvs, json_field "feature" kvs with
    | Some lj, Some fj =>
      match json_to_link lj, json_to_feature_expr 100 fj with
      | Some l, Some fe => Some {| al_link := l; al_feature := fe |}
      | _, _ => None
      end
    | _, _ => None
    end
  | _ => None
  end.

Definition json_to_feature_model (j : Json) : option FeatureModel :=
  match j with
  | JObj kvs =>
    match json_field "features" kvs,
          json_field "mandatory" kvs,
          json_field "constraints" kvs with
    | Some (JArr feat_js), Some (JArr mand_js), Some (JArr cons_js) =>
      match json_to_string_list feat_js,
            json_to_string_list mand_js,
            json_list_map (json_to_feature_expr 100) cons_js with
      | Some feats, Some mands, Some consts =>
        Some {| fm_features := feats;
                fm_mandatory := mands;
                fm_constraints := consts |}
      | _, _, _ => None
      end
    | _, _, _ => None
    end
  | _ => None
  end.

Definition json_to_product_line_case (j : Json) : option ProductLineCase :=
  match j with
  | JObj kvs =>
    match json_field "top" kvs,
          json_field "nodes" kvs,
          json_field "links" kvs,
          json_field "feature_model" kvs with
    | Some (JStr top_id), Some (JArr node_js),
      Some (JArr link_js), Some fm_json =>
      match json_list_map json_to_annotated_node node_js,
            json_list_map json_to_annotated_link link_js,
            json_to_feature_model fm_json with
      | Some nodes, Some links, Some fm =>
        Some {| plc_nodes := nodes;
                plc_links := links;
                plc_top := top_id;
                plc_fm := fm |}
      | _, _, _ => None
      end
    | _, _, _, _ => None
    end
  | _ => None
  end.

(* ================================================================== *)
(* Trust envelope key constants (TODO item 8)                          *)
(* ================================================================== *)

(** Canonical metadata key names for trust envelope fields.
    Use these constants when constructing or querying node metadata
    to ensure consistency across the toolchain. *)

Definition te_key_tool          := "tool".
Definition te_key_version       := "version".
Definition te_key_timestamp     := "timestamp".
Definition te_key_valid_from    := "valid_from".
Definition te_key_valid_until   := "valid_until".
Definition te_key_replay        := "replay".
Definition te_key_confidence    := "confidence".
Definition te_key_blob          := "blob".
Definition te_key_undeveloped   := "undeveloped".
Definition te_key_assumption_status := "assumption_status".

(** Build a metadata list from a TrustEnvelope record using canonical keys. *)
Definition trust_envelope_to_metadata (te : TrustEnvelope)
    : list (string * MetadataValue) :=
  let base := [(te_key_tool, MVString te.(te_tool));
               (te_key_version, MVString te.(te_version))] in
  let ts := match te.(te_valid_from) with
            | EmptyString => []
            | s => [(te_key_valid_from, MVTimestamp s)]
            end in
  let vu := match te.(te_valid_until) with
            | EmptyString => []
            | s => [(te_key_valid_until, MVTimestamp s)]
            end in
  let rp := match te.(te_replay_command) with
            | Some cmd => [(te_key_replay, MVString cmd)]
            | None => []
            end in
  base ++ ts ++ vu ++ rp.
