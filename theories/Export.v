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

(* After extraction, ProofTerm erases its Prop and proof witness;
   only the string label survives.  The exported JSON therefore
   contains the label (identifying which theorem was proved) but
   NOT the proof itself.  Import cannot reconstruct ProofTerm
   evidence — use hydrate_evidence to re-attach it.                    *)
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

(* Fixed fuel of 20 digits — sufficient for decimal representations
   up to 10^20 (~66 bits).  Chosen to avoid O(n) fuel construction
   in the Peano representation while covering any practically
   occurring nat in assurance-case metadata.                           *)
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

(* Abstraction for externally-signed evidence blobs.
   sb_verify is a DECIDABLE VALIDATOR, not a cryptographic primitive.
   The user instantiates it with whatever verification logic is
   appropriate: HMAC check, GPG signature verify, or a simple
   string-equality stub for testing.  The Rocq proof only requires
   that sb_verify sb_payload sb_signature = true; the actual
   cryptographic strength is the user's responsibility.

   After extraction, sb_verify becomes an OCaml function
   (string -> string -> bool) that can call real crypto libraries.     *)
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

(* ------------------------------------------------------------------ *)
(* JSON parser                                                          *)
(* ------------------------------------------------------------------ *)

(* Fuel-bounded recursive-descent parser.
   Limitations: no Unicode escape sequences (\uXXXX), non-negative
   integers only (no floats, no negative numbers).  Sufficient for
   round-tripping assurance-case JSON produced by render_json.         *)

Definition nat_of_ascii_local (a : ascii) : nat :=
  match a with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    (if b0 then 1 else 0) + (if b1 then 2 else 0) +
    (if b2 then 4 else 0) + (if b3 then 8 else 0) +
    (if b4 then 16 else 0) + (if b5 then 32 else 0) +
    (if b6 then 64 else 0) + (if b7 then 128 else 0)
  end.

Definition is_whitespace_char (c : ascii) : bool :=
  let n := nat_of_ascii_local c in
  Nat.eqb n 32 || Nat.eqb n 10 || Nat.eqb n 13 || Nat.eqb n 9.

Definition is_digit_char (c : ascii) : bool :=
  let n := nat_of_ascii_local c in
  Nat.leb 48 n && Nat.leb n 57.

Definition digit_value_of (c : ascii) : nat :=
  nat_of_ascii_local c - 48.

Definition is_char_code (c : ascii) (code : nat) : bool :=
  Nat.eqb (nat_of_ascii_local c) code.

Fixpoint skip_whitespace (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
    if is_whitespace_char c then skip_whitespace rest else s
  end.

Fixpoint string_rev_append (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c rest => string_rev_append rest (String c acc)
  end.

Definition string_rev (s : string) : string :=
  string_rev_append s EmptyString.

Fixpoint string_length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ rest => S (string_length rest)
  end.

(* Parse a JSON string literal body (after opening double-quote).
   Returns (parsed_string, remaining_input).                           *)
Fixpoint parse_string_chars (fuel : nat) (s : string) (acc : string)
  : option (string * string) :=
  match fuel with
  | 0 => None
  | S f =>
    match s with
    | EmptyString => None
    | String c rest =>
      if is_char_code c 34 then
        Some (string_rev acc, rest)
      else if is_char_code c 92 then
        match rest with
        | EmptyString => None
        | String c2 rest2 =>
          if is_char_code c2 34 then
            parse_string_chars f rest2 (String dquote_char acc)
          else if is_char_code c2 92 then
            parse_string_chars f rest2 (String backslash_char acc)
          else if is_char_code c2 110 then
            parse_string_chars f rest2 (String nl_char acc)
          else if is_char_code c2 114 then
            parse_string_chars f rest2 (String cr_char acc)
          else if is_char_code c2 116 then
            parse_string_chars f rest2 (String tab_char acc)
          else if is_char_code c2 98 then
            parse_string_chars f rest2 (String bs_char acc)
          else if is_char_code c2 102 then
            parse_string_chars f rest2 (String ff_char acc)
          else
            None
        end
      else
        parse_string_chars f rest (String c acc)
    end
  end.

(* Parse a non-negative decimal integer.                               *)
Fixpoint parse_nat_chars (fuel : nat) (s : string) (acc : nat)
  : nat * string :=
  match fuel with
  | 0 => (acc, s)
  | S f =>
    match s with
    | EmptyString => (acc, s)
    | String c rest =>
      if is_digit_char c
      then parse_nat_chars f rest (acc * 10 + digit_value_of c)
      else (acc, s)
    end
  end.

(* Expect a specific literal prefix.                                   *)
Fixpoint expect_literal (lit s : string) : option string :=
  match lit with
  | EmptyString => Some s
  | String c1 rest_lit =>
    match s with
    | EmptyString => None
    | String c2 rest_s =>
      if ascii_eqb c1 c2 then expect_literal rest_lit rest_s
      else None
    end
  end.

(* Main recursive-descent parser.  All three mutually recursive
   functions decrease on the fuel parameter.                           *)
Fixpoint parse_json_go (fuel : nat) (s : string)
  : option (Json * string) :=
  match fuel with
  | 0 => None
  | S f =>
    let s := skip_whitespace s in
    match s with
    | EmptyString => None
    | String c rest =>
      if is_char_code c 34 then
        match parse_string_chars f rest EmptyString with
        | Some (str, rest') => Some (JStr str, rest')
        | None => None
        end
      else if is_char_code c 123 then
        let rest' := skip_whitespace rest in
        match rest' with
        | EmptyString => None
        | String c2 rest2 =>
          if is_char_code c2 125 then
            Some (JObj nil, rest2)
          else
            parse_object_kvs f rest' nil
        end
      else if is_char_code c 91 then
        let rest' := skip_whitespace rest in
        match rest' with
        | EmptyString => None
        | String c2 rest2 =>
          if is_char_code c2 93 then
            Some (JArr nil, rest2)
          else
            parse_array_elems f rest' nil
        end
      else if is_digit_char c then
        let '(n, rest') := parse_nat_chars f rest (digit_value_of c) in
        Some (JNum n, rest')
      else if is_char_code c 116 then
        match expect_literal "rue" rest with
        | Some rest' => Some (JBool true, rest')
        | None => None
        end
      else if is_char_code c 102 then
        match expect_literal "alse" rest with
        | Some rest' => Some (JBool false, rest')
        | None => None
        end
      else if is_char_code c 110 then
        match expect_literal "ull" rest with
        | Some rest' => Some (JNull, rest')
        | None => None
        end
      else
        None
    end
  end

with parse_array_elems (fuel : nat) (s : string) (acc : list Json)
  : option (Json * string) :=
  match fuel with
  | 0 => None
  | S f =>
    match parse_json_go f s with
    | None => None
    | Some (elem, rest) =>
      let rest := skip_whitespace rest in
      match rest with
      | EmptyString => None
      | String c rest' =>
        if is_char_code c 93 then
          Some (JArr (rev (elem :: acc)), rest')
        else if is_char_code c 44 then
          parse_array_elems f rest' (elem :: acc)
        else None
      end
    end
  end

with parse_object_kvs (fuel : nat) (s : string)
    (acc : list (string * Json))
  : option (Json * string) :=
  match fuel with
  | 0 => None
  | S f =>
    let s := skip_whitespace s in
    match s with
    | EmptyString => None
    | String c rest =>
      if is_char_code c 34 then
        match parse_string_chars f rest EmptyString with
        | None => None
        | Some (key, rest1) =>
          let rest1 := skip_whitespace rest1 in
          match rest1 with
          | EmptyString => None
          | String c2 rest2 =>
            if is_char_code c2 58 then
              match parse_json_go f rest2 with
              | None => None
              | Some (value, rest3) =>
                let rest3 := skip_whitespace rest3 in
                match rest3 with
                | EmptyString => None
                | String c3 rest4 =>
                  if is_char_code c3 125 then
                    Some (JObj (rev ((key, value) :: acc)), rest4)
                  else if is_char_code c3 44 then
                    parse_object_kvs f rest4 ((key, value) :: acc)
                  else None
                end
              end
            else None
          end
        end
      else None
    end
  end.

Definition parse_json (s : string) : option Json :=
  match parse_json_go (string_length s) s with
  | Some (j, _) => Some j
  | None => None
  end.

(* ------------------------------------------------------------------ *)
(* JSON to AssuranceCase importer                                       *)
(* ------------------------------------------------------------------ *)

(* Look up a key in a JSON object's key-value list.                    *)
Fixpoint json_field (key : string) (kvs : list (string * Json))
  : option Json :=
  match kvs with
  | nil => None
  | (k, v) :: rest =>
    if String.eqb k key then Some v else json_field key rest
  end.

Definition json_to_node_kind (j : Json) : option NodeKind :=
  match j with
  | JStr s =>
    if String.eqb s "Goal" then Some Goal
    else if String.eqb s "Strategy" then Some Strategy
    else if String.eqb s "Solution" then Some Solution
    else if String.eqb s "Context" then Some Context
    else if String.eqb s "Assumption" then Some Assumption
    else if String.eqb s "Justification" then Some Justification
    else None
  | _ => None
  end.

Definition json_to_link_kind (j : Json) : option LinkKind :=
  match j with
  | JStr s =>
    if String.eqb s "SupportedBy" then Some SupportedBy
    else if String.eqb s "InContextOf" then Some InContextOf
    else None
  | _ => None
  end.

(* Reconstruct a node from JSON.  Evidence and logical claims cannot
   be recovered (ProofTerm proofs are erased, Certificate validators
   are functions).  All parsed nodes get evidence = None and
   claim = True.  Use hydrate_evidence to re-attach evidence.          *)
Definition json_to_node (j : Json) : option Node :=
  match j with
  | JObj kvs =>
    match json_field "id" kvs, json_field "kind" kvs with
    | Some (JStr id), Some kind_json =>
      match json_to_node_kind kind_json with
      | Some nk =>
        let claim_text := match json_field "claim" kvs with
                          | Some (JStr s) => s
                          | _ => EmptyString
                          end in
        Some {| node_id := id;
                node_kind := nk;
                node_claim_text := claim_text;
                node_evidence := None;
                node_claim := True |}
      | None => None
      end
    | _, _ => None
    end
  | _ => None
  end.

Definition json_to_link (j : Json) : option Link :=
  match j with
  | JObj kvs =>
    match json_field "kind" kvs,
          json_field "from" kvs,
          json_field "to" kvs with
    | Some kind_json, Some (JStr from_id), Some (JStr to_id) =>
      match json_to_link_kind kind_json with
      | Some lk =>
        Some {| link_kind := lk;
                link_from := from_id;
                link_to := to_id |}
      | None => None
      end
    | _, _, _ => None
    end
  | _ => None
  end.

Fixpoint json_list_map {A : Type} (f : Json -> option A)
    (js : list Json) : option (list A) :=
  match js with
  | nil => Some nil
  | j :: rest =>
    match f j, json_list_map f rest with
    | Some a, Some as_ => Some (a :: as_)
    | _, _ => None
    end
  end.

Definition json_to_assurance_case (j : Json) : option AssuranceCase :=
  match j with
  | JObj kvs =>
    match json_field "top" kvs,
          json_field "nodes" kvs,
          json_field "links" kvs with
    | Some (JStr top_id), Some (JArr node_jsons), Some (JArr link_jsons) =>
      match json_list_map json_to_node node_jsons,
            json_list_map json_to_link link_jsons with
      | Some nodes, Some links =>
        Some {| ac_nodes := nodes; ac_links := links; ac_top := top_id |}
      | _, _ => None
      end
    | _, _, _ => None
    end
  | _ => None
  end.

(* Re-attach evidence to parsed nodes.  The mapping provides
   evidence for each node ID.  Nodes not in the mapping keep
   their existing evidence (typically None after parsing).             *)
Fixpoint assoc_find_evidence (id : Id) (m : list (Id * Evidence))
  : option Evidence :=
  match m with
  | nil => None
  | (k, v) :: rest =>
    if String.eqb k id then Some v
    else assoc_find_evidence id rest
  end.

Fixpoint hydrate_evidence_list (nodes : list Node)
    (evidence_map : list (Id * Evidence)) : list Node :=
  match nodes with
  | nil => nil
  | n :: rest =>
    let ev := match assoc_find_evidence n.(node_id) evidence_map with
              | Some e => Some e
              | None => n.(node_evidence)
              end in
    {| node_id := n.(node_id);
       node_kind := n.(node_kind);
       node_claim_text := n.(node_claim_text);
       node_evidence := ev;
       node_claim := n.(node_claim) |}
    :: hydrate_evidence_list rest evidence_map
  end.

Definition hydrate_evidence (ac : AssuranceCase)
    (evidence_map : list (Id * Evidence)) : AssuranceCase := {|
  ac_nodes := hydrate_evidence_list ac.(ac_nodes) evidence_map;
  ac_links := ac.(ac_links);
  ac_top := ac.(ac_top);
|}.
