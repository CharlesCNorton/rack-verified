(* ------------------------------------------------------------------ *)
(* DOT export                                                           *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Json.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* DOT export                                                           *)
(* ------------------------------------------------------------------ *)

Definition concat_strings (ss : list string) : string :=
  fold_right String.append EmptyString ss.

Definition node_kind_shape (nk : NodeKind) : string :=
  match nk with
  | Goal => "box" | Strategy => "parallelogram" | Solution => "ellipse"
  | Context => "note" | Assumption => "diamond" | Justification => "hexagon"
  end.

Definition node_kind_color (nk : NodeKind) : string :=
  match nk with
  | Goal => "#c6e2ff" | Strategy => "#ffffcc" | Solution => "#c6ffc6"
  | Context => "#f0f0f0" | Assumption => "#ffe0cc" | Justification => "#e0ccff"
  end.

Definition render_dot_node (n : Node) : string :=
  let label := n.(node_id) ++ ": " ++ n.(node_claim_text) in
  "  " ++ json_quote n.(node_id) ++ " [label=" ++ json_quote label
       ++ ",shape=" ++ node_kind_shape n.(node_kind)
       ++ ",style=filled,fillcolor=" ++ json_quote (node_kind_color n.(node_kind))
       ++ "];" ++ nl.

Definition render_dot_edge (l : Link) : string :=
  "  " ++ json_quote l.(link_from) ++ " -> " ++ json_quote l.(link_to)
       ++ match l.(link_kind) with
          | SupportedBy => " [style=solid];"
          | InContextOf  => " [style=dashed];"
          | Defeater     => " [style=dotted,color=red];"
          end ++ nl.

Definition render_dot (ac : AssuranceCase) : string :=
  "digraph assurance_case {" ++ nl
    ++ concat_strings (map render_dot_node ac.(ac_nodes))
    ++ concat_strings (map render_dot_edge ac.(ac_links))
    ++ "}" ++ nl.

(* ------------------------------------------------------------------ *)
(* DOT export with layout options                                       *)
(* ------------------------------------------------------------------ *)

Record DotOptions : Type := {
  dot_rankdir       : string;   (* "TB", "LR", "BT", "RL" *)
  dot_cluster       : bool;     (* group nodes by kind *)
  dot_show_metadata : bool;     (* include metadata in labels *)
  dot_show_evidence : bool;     (* include evidence labels *)
}.

Definition default_dot_options : DotOptions := {|
  dot_rankdir       := "TB";
  dot_cluster       := false;
  dot_show_metadata := false;
  dot_show_evidence := false;
|}.

Definition render_dot_node_opts (opts : DotOptions) (n : Node) : string :=
  let base_label := n.(node_id) ++ ": " ++ n.(node_claim_text) in
  let ev_label :=
    if opts.(dot_show_evidence) then
      match n.(node_evidence) with
      | Some e => "\n[" ++ evidence_label e ++ "]"
      | None => ""
      end
    else "" in
  let md_label :=
    if opts.(dot_show_metadata) then
      concat_strings (map (fun kv =>
        "\n" ++ fst kv ++ "=" ++ mv_as_string (snd kv)) n.(node_metadata))
    else "" in
  let label := base_label ++ ev_label ++ md_label in
  "  " ++ json_quote n.(node_id) ++ " [label=" ++ json_quote label
       ++ ",shape=" ++ node_kind_shape n.(node_kind)
       ++ ",style=filled,fillcolor=" ++ json_quote (node_kind_color n.(node_kind))
       ++ "];" ++ nl.

Definition node_kind_to_string (nk : NodeKind) : string :=
  match nk with
  | Goal => "Goal" | Strategy => "Strategy" | Solution => "Solution"
  | Context => "Context" | Assumption => "Assumption"
  | Justification => "Justification"
  end.

Definition render_dot_cluster_nodes (kind : NodeKind)
    (nodes : list Node) : string :=
  let filtered := filter (fun n => match n.(node_kind), kind with
    | Goal, Goal | Strategy, Strategy | Solution, Solution
    | Context, Context | Assumption, Assumption
    | Justification, Justification => true | _, _ => false end) nodes in
  match filtered with
  | [] => ""
  | _ =>
    "  subgraph cluster_" ++ node_kind_to_string kind ++ " {" ++ nl
    ++ "    label=" ++ json_quote (node_kind_to_string kind) ++ ";" ++ nl
    ++ concat_strings (map (fun n =>
         "    " ++ json_quote n.(node_id) ++ ";" ++ nl) filtered)
    ++ "  }" ++ nl
  end.

Definition render_dot_with_options (opts : DotOptions)
    (ac : AssuranceCase) : string :=
  "digraph assurance_case {" ++ nl
    ++ "  rankdir=" ++ opts.(dot_rankdir) ++ ";" ++ nl
    ++ (if opts.(dot_cluster) then
          concat_strings (map (fun k =>
            render_dot_cluster_nodes k ac.(ac_nodes))
            [Goal; Strategy; Solution; Context; Assumption; Justification])
        else "")
    ++ concat_strings (map (render_dot_node_opts opts) ac.(ac_nodes))
    ++ concat_strings (map render_dot_edge ac.(ac_links))
    ++ "}" ++ nl.
