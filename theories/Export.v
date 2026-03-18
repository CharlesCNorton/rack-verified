(* ------------------------------------------------------------------ *)
(* 8. JSON export                                                       *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* ASCII 34 = double-quote. *)
Definition dquote_char : ascii :=
  Ascii false true false false false true false false.
Definition dquote : string := String dquote_char EmptyString.

(* Minimal JSON AST. *)
Inductive Json : Type :=
  | JNull   : Json
  | JBool   : bool -> Json
  | JStr    : string -> Json
  | JNum    : nat -> Json
  | JArr    : list Json -> Json
  | JObj    : list (string * Json) -> Json.

(* — Serialization to JSON AST — *)

Definition node_kind_to_json (nk : NodeKind) : Json :=
  JStr match nk with
  | Goal => "Goal" | Strategy => "Strategy" | Solution => "Solution"
  | Context => "Context" | Assumption => "Assumption"
  | Justification => "Justification"
  end.

Definition evidence_to_json (e : Evidence) : Json :=
  match e with
  | ProofTerm _ _ =>
      JObj [("type", JStr "ProofTerm")]
  | Certificate blob _ =>
      JObj [("type", JStr "Certificate"); ("blob", JStr blob)]
  end.

Definition node_to_json (n : Node) : Json :=
  JObj [("id", JStr n.(node_id));
        ("kind", node_kind_to_json n.(node_kind));
        ("evidence",
          match n.(node_evidence) with
          | Some e => evidence_to_json e
          | None => JNull
          end)].

Definition link_kind_to_json (lk : LinkKind) : Json :=
  JStr match lk with
  | SupportedBy => "SupportedBy"
  | InContextOf => "InContextOf"
  end.

Definition link_to_json (l : Link) : Json :=
  JObj [("kind", link_kind_to_json l.(link_kind));
        ("from", JStr l.(link_from));
        ("to", JStr l.(link_to))].

Definition assurance_case_to_json (ac : AssuranceCase) : Json :=
  JObj [("top", JStr ac.(ac_top));
        ("nodes", JArr (map node_to_json ac.(ac_nodes)));
        ("links", JArr (map link_to_json ac.(ac_links)))].

(* — JSON text renderer — *)

Definition digit_to_string (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => "?"
  end.

Fixpoint nat_to_string_go (fuel n : nat) (acc : string) : string :=
  match fuel with
  | 0 => acc
  | S fuel' =>
    let acc' := String.append (digit_to_string (n mod 10)) acc in
    match n / 10 with
    | 0 => acc'
    | q => nat_to_string_go fuel' q acc'
    end
  end.

Definition nat_to_string (n : nat) : string :=
  nat_to_string_go (S n) n EmptyString.

Fixpoint join_strings (sep : string) (ss : list string) : string :=
  match ss with
  | [] => EmptyString
  | s :: rest =>
    String.append s
      (match rest with
       | [] => EmptyString
       | _ => String.append sep (join_strings sep rest)
       end)
  end.

Definition json_quote (s : string) : string :=
  String.append dquote (String.append s dquote).

Fixpoint render_json (j : Json) : string :=
  let fix render_list (js : list Json) : list string :=
    match js with
    | [] => []
    | j' :: rest => render_json j' :: render_list rest
    end
  in
  let fix render_kvs (kvs : list (string * Json)) : list string :=
    match kvs with
    | [] => []
    | (k, v) :: rest =>
        String.append (String.append (json_quote k) ":") (render_json v)
          :: render_kvs rest
    end
  in
  match j with
  | JNull => "null"
  | JBool true => "true"
  | JBool false => "false"
  | JStr s => json_quote s
  | JNum n => nat_to_string n
  | JArr elems =>
      String.append "[" (String.append (join_strings "," (render_list elems)) "]")
  | JObj kvs =>
      String.append "{" (String.append (join_strings "," (render_kvs kvs)) "}")
  end.

Definition render_assurance_case (ac : AssuranceCase) : string :=
  render_json (assurance_case_to_json ac).

(* ------------------------------------------------------------------ *)
(* 9. DOT export                                                        *)
(* ------------------------------------------------------------------ *)

(* ASCII 10 = newline. *)
Definition nl_char : ascii :=
  Ascii false true false true false false false false.
Definition nl : string := String nl_char EmptyString.

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
  "  " ++ json_quote n.(node_id) ++ " [label=" ++ json_quote n.(node_id)
       ++ ",shape=" ++ node_kind_shape n.(node_kind)
       ++ ",style=filled,fillcolor=" ++ json_quote (node_kind_color n.(node_kind))
       ++ "];" ++ nl.

Definition render_dot_edge (l : Link) : string :=
  "  " ++ json_quote l.(link_from) ++ " -> " ++ json_quote l.(link_to)
       ++ match l.(link_kind) with
          | SupportedBy => " [style=solid];"
          | InContextOf  => " [style=dashed];"
          end ++ nl.

Definition render_dot (ac : AssuranceCase) : string :=
  "digraph assurance_case {" ++ nl
    ++ concat_strings (map render_dot_node ac.(ac_nodes))
    ++ concat_strings (map render_dot_edge ac.(ac_links))
    ++ "}" ++ nl.

(* ------------------------------------------------------------------ *)
(* 10. Signed evidence blobs                                            *)
(* ------------------------------------------------------------------ *)

Record SignedBlob : Type := {
  sb_payload   : string;
  sb_signature : string;
  sb_verify    : string -> string -> bool;
}.

Definition signed_blob_valid (sb : SignedBlob) : Prop :=
  sb.(sb_verify) sb.(sb_payload) sb.(sb_signature) = true.

(* Wrap a signed blob as a Certificate evidence node.                  *)
(* The verifier closes over the stored signature so the Evidence       *)
(* validator only needs the payload.                                   *)
Definition signed_to_evidence (sb : SignedBlob) : Evidence :=
  Certificate sb.(sb_payload)
              (fun p => sb.(sb_verify) p sb.(sb_signature)).

Lemma signed_evidence_valid : forall sb n,
    signed_blob_valid sb ->
    evidence_valid n (signed_to_evidence sb).
Proof. intros sb n H. exact H. Qed.

Definition signed_to_json (sb : SignedBlob) : Json :=
  JObj [("type", JStr "SignedBlob");
        ("payload", JStr sb.(sb_payload));
        ("signature", JStr sb.(sb_signature))].
