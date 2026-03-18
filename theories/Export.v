(* ------------------------------------------------------------------ *)
(* JSON and DOT export                                                  *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Character constants                                                  *)
(* ------------------------------------------------------------------ *)

(* ASCII 34 = double-quote. *)
Definition dquote_char : ascii :=
  Ascii false true false false false true false false.
Definition dquote : string := String dquote_char EmptyString.

(* ASCII 92 = backslash. *)
Definition backslash_char : ascii :=
  Ascii false false true true true false true false.

(* ASCII 32 = space. *)
Definition space_char : ascii :=
  Ascii false false false false false true false false.

(* ASCII 10 = newline. *)
Definition nl_char : ascii :=
  Ascii false true false true false false false false.
Definition nl : string := String nl_char EmptyString.

(* ------------------------------------------------------------------ *)
(* JSON string escaping                                                 *)
(* ------------------------------------------------------------------ *)

(* Self-contained ascii equality — no stdlib Ascii.eqb dependency. *)
Definition ascii_eqb (a b : ascii) : bool :=
  match a, b with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
    Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 && Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3 &&
    Bool.eqb a4 b4 && Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7
  end.

(* Control-character constants for JSON escaping.                      *)
Definition nl_esc_char : ascii :=    (* 'n' = 0x6E *)
  Ascii false true true true false true true false.
Definition cr_char : ascii :=       (* CR = 0x0D *)
  Ascii true false true true false false false false.
Definition cr_esc_char : ascii :=   (* 'r' = 0x72 *)
  Ascii false true false false true true true false.
Definition tab_char : ascii :=      (* TAB = 0x09 *)
  Ascii true false false true false false false false.
Definition tab_esc_char : ascii :=  (* 't' = 0x74 *)
  Ascii false false true false true true true false.
Definition bs_char : ascii :=       (* BS = 0x08 *)
  Ascii false false false true false false false false.
Definition bs_esc_char : ascii :=   (* 'b' = 0x62 *)
  Ascii false true false false false true true false.
Definition ff_char : ascii :=       (* FF = 0x0C *)
  Ascii false false true true false false false false.
Definition ff_esc_char : ascii :=   (* 'f' = 0x66 *)
  Ascii false true true false false true true false.

(* Escape characters special in JSON strings: dquote, backslash,
   and control characters (newline, carriage return, tab, etc.).        *)
Fixpoint escape_json_chars (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
    if ascii_eqb c dquote_char then
      String backslash_char (String dquote_char (escape_json_chars rest))
    else if ascii_eqb c backslash_char then
      String backslash_char (String backslash_char (escape_json_chars rest))
    else if ascii_eqb c nl_char then
      String backslash_char (String nl_esc_char (escape_json_chars rest))
    else if ascii_eqb c cr_char then
      String backslash_char (String cr_esc_char (escape_json_chars rest))
    else if ascii_eqb c tab_char then
      String backslash_char (String tab_esc_char (escape_json_chars rest))
    else if ascii_eqb c bs_char then
      String backslash_char (String bs_esc_char (escape_json_chars rest))
    else if ascii_eqb c ff_char then
      String backslash_char (String ff_esc_char (escape_json_chars rest))
    else
      String c (escape_json_chars rest)
  end.

(* ------------------------------------------------------------------ *)
(* Minimal JSON AST                                                     *)
(* ------------------------------------------------------------------ *)

Inductive Json : Type :=
  | JNull   : Json
  | JBool   : bool -> Json
  | JStr    : string -> Json
  | JNum    : nat -> Json
  | JArr    : list Json -> Json
  | JObj    : list (string * Json) -> Json.

(* ------------------------------------------------------------------ *)
(* Serialization to JSON AST                                            *)
(* ------------------------------------------------------------------ *)

Definition node_kind_to_json (nk : NodeKind) : Json :=
  JStr match nk with
  | Goal => "Goal" | Strategy => "Strategy" | Solution => "Solution"
  | Context => "Context" | Assumption => "Assumption"
  | Justification => "Justification"
  end.

Definition evidence_to_json (e : Evidence) : Json :=
  match e with
  | ProofTerm lbl _ _ =>
      JObj [("type", JStr "ProofTerm"); ("label", JStr lbl)]
  | Certificate blob _ =>
      JObj [("type", JStr "Certificate"); ("blob", JStr blob)]
  end.

Definition node_to_json (n : Node) : Json :=
  JObj [("id", JStr n.(node_id));
        ("kind", node_kind_to_json n.(node_kind));
        ("claim", JStr n.(node_claim_text));
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

(* ------------------------------------------------------------------ *)
(* JSON text renderers                                                  *)
(* ------------------------------------------------------------------ *)

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

(* Fixed fuel of 20 — sufficient for any nat up to 10^20.
   Avoids O(n) fuel construction in the Peano representation.          *)
Definition nat_to_string (n : nat) : string :=
  nat_to_string_go 20 n EmptyString.

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
  String.append dquote (String.append (escape_json_chars s) dquote).

(* Compact single-line renderer. *)
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
(* Pretty-printed JSON renderer                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint indent (n : nat) : string :=
  match n with
  | 0 => EmptyString
  | S n' => String space_char (String space_char (indent n'))
  end.

Fixpoint render_json_pretty_go (depth : nat) (j : Json) : string :=
  let ind := indent depth in
  let ind1 := indent (S depth) in
  let fix render_list_pretty (js : list Json) : list string :=
    match js with
    | [] => []
    | j' :: rest =>
        String.append ind1 (render_json_pretty_go (S depth) j')
        :: render_list_pretty rest
    end
  in
  let fix render_kvs_pretty (kvs : list (string * Json)) : list string :=
    match kvs with
    | [] => []
    | (k, v) :: rest =>
        String.append ind1
          (String.append (json_quote k)
            (String.append ": " (render_json_pretty_go (S depth) v)))
        :: render_kvs_pretty rest
    end
  in
  match j with
  | JNull => "null"
  | JBool true => "true"
  | JBool false => "false"
  | JStr s => json_quote s
  | JNum n => nat_to_string n
  | JArr elems =>
    let items := render_list_pretty elems in
    match items with
    | [] => "[]"
    | _ =>
      String.append "["
        (String.append nl
          (String.append (join_strings (String.append "," nl) items)
            (String.append nl (String.append ind "]"))))
    end
  | JObj kvs =>
    let entries := render_kvs_pretty kvs in
    match entries with
    | [] => "{}"
    | _ =>
      String.append "{"
        (String.append nl
          (String.append (join_strings (String.append "," nl) entries)
            (String.append nl (String.append ind "}"))))
    end
  end.

Definition render_json_pretty (j : Json) : string :=
  render_json_pretty_go 0 j.

Definition render_assurance_case_pretty (ac : AssuranceCase) : string :=
  render_json_pretty (assurance_case_to_json ac).

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
          end ++ nl.

Definition render_dot (ac : AssuranceCase) : string :=
  "digraph assurance_case {" ++ nl
    ++ concat_strings (map render_dot_node ac.(ac_nodes))
    ++ concat_strings (map render_dot_edge ac.(ac_links))
    ++ "}" ++ nl.

(* ------------------------------------------------------------------ *)
(* Signed evidence blobs                                                *)
(* ------------------------------------------------------------------ *)

Record SignedBlob : Type := {
  sb_payload   : string;
  sb_signature : string;
  sb_verify    : string -> string -> bool;
}.

Definition signed_blob_valid (sb : SignedBlob) : Prop :=
  sb.(sb_verify) sb.(sb_payload) sb.(sb_signature) = true.

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
