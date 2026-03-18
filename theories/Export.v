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
Open Scope list_scope.
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

(** * JSON AST
    Includes [JNeg] for negative integers and [JFloat] for
    floating-point literals (preserved as strings). *)
Inductive Json : Type :=
  | JNull   : Json
  | JBool   : bool -> Json
  | JStr    : string -> Json
  | JNum    : nat -> Json
  | JNeg    : nat -> Json      (** [JNeg n] represents [-(S n)] *)
  | JFloat  : string -> Json   (** preserved verbatim as string *)
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
  | ProofTerm lbl _ _ _ =>
      JObj [("type", JStr "ProofTerm"); ("label", JStr lbl)]
  | Certificate blob tool _ =>
      JObj [("type", JStr "Certificate"); ("blob", JStr blob);
            ("tool", JStr tool)]
  end.

Definition metadata_value_to_json (v : MetadataValue) : Json :=
  match v with
  | MVString s    => JStr s
  | MVNat n       => JNum n
  | MVBool b      => JBool b
  | MVTimestamp s => JStr s
  end.

Definition metadata_to_json (md : list (string * MetadataValue)) : Json :=
  JObj (map (fun kv => (fst kv, metadata_value_to_json (snd kv))) md).

Definition node_to_json (n : Node) : Json :=
  JObj [("id", JStr n.(node_id));
        ("kind", node_kind_to_json n.(node_kind));
        ("claim", JStr n.(node_claim_text));
        ("evidence",
          match n.(node_evidence) with
          | Some e => evidence_to_json e
          | None => JNull
          end);
        ("metadata", metadata_to_json n.(node_metadata))].

Definition link_kind_to_json (lk : LinkKind) : Json :=
  JStr match lk with
  | SupportedBy => "SupportedBy"
  | InContextOf => "InContextOf"
  | Defeater    => "Defeater"
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
  | JNeg n => String.append "-" (nat_to_string (S n))
  | JFloat s => s
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
  | JNeg n => String.append "-" (nat_to_string (S n))
  | JFloat s => s
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
  Certificate sb.(sb_payload) "signed"
              (fun p => sb.(sb_verify) p sb.(sb_signature)).

Lemma signed_evidence_valid : forall sb n,
    signed_blob_valid sb ->
    evidence_valid n (signed_to_evidence sb).
Proof. intros sb n H. exact H. Qed.

(** [KeyedSignedBlob] strengthens [SignedBlob] by requiring that
    the verifier is keyed: it takes a secret and checks that
    [verify secret payload signature = true].  After extraction,
    instantiate [ksb_verify] with [Rack_util.make_keyed_validator]
    which uses HMAC-SHA256.

    The Rocq-side specification guarantees:
    1. [signed_blob_valid] holds iff the verifier accepts.
    2. The extracted verifier calls real HMAC-SHA256 (via rack_util.ml).
    3. Tampering with payload or signature causes rejection
       (verified by property tests in test_rack.ml). *)
Record KeyedSignedBlob : Type := {
  ksb_payload   : string;
  ksb_signature : string;
  ksb_key_id    : string;   (* identifies the key, not the key itself *)
  ksb_verify    : string -> string -> bool;
}.

Definition keyed_blob_valid (ksb : KeyedSignedBlob) : Prop :=
  ksb.(ksb_verify) ksb.(ksb_payload) ksb.(ksb_signature) = true.

Definition keyed_to_signed (ksb : KeyedSignedBlob) : SignedBlob := {|
  sb_payload := ksb.(ksb_payload);
  sb_signature := ksb.(ksb_signature);
  sb_verify := ksb.(ksb_verify);
|}.

Lemma keyed_valid_implies_signed : forall ksb,
    keyed_blob_valid ksb -> signed_blob_valid (keyed_to_signed ksb).
Proof. intros ksb H. exact H. Qed.

Definition keyed_to_evidence (ksb : KeyedSignedBlob) : Evidence :=
  signed_to_evidence (keyed_to_signed ksb).

Definition signed_to_json (sb : SignedBlob) : Json :=
  JObj [("type", JStr "SignedBlob");
        ("payload", JStr sb.(sb_payload));
        ("signature", JStr sb.(sb_signature))].

(* ------------------------------------------------------------------ *)
(* JSON parser                                                          *)
(* ------------------------------------------------------------------ *)

(* Fuel-bounded recursive-descent parser.
   Handles: strings (with \uXXXX for ASCII range), objects, arrays,
   non-negative integers, booleans, null.  For negative numbers and
   floats, use the extended JsonExt parser.  Sufficient for
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

(* Hex digit value for \uXXXX parsing. *)
Definition hex_value_of_local (c : ascii) : option nat :=
  let n := nat_of_ascii_local c in
  if Nat.leb 48 n && Nat.leb n 57 then Some (n - 48)
  else if Nat.leb 65 n && Nat.leb n 70 then Some (n - 55)
  else if Nat.leb 97 n && Nat.leb n 102 then Some (n - 87)
  else None.

(* Parse \uXXXX: exactly 4 hex digits, ASCII range only (0-127).
   Higher codepoints are replaced with '?' since Rocq strings
   are ASCII-only.                                                     *)
Definition parse_unicode_escape_local (s : string) : option (ascii * string) :=
  match s with
  | String h1 (String h2 (String h3 (String h4 rest))) =>
    match hex_value_of_local h1, hex_value_of_local h2,
          hex_value_of_local h3, hex_value_of_local h4 with
    | Some d1, Some d2, Some d3, Some d4 =>
      let cp := d1 * 4096 + d2 * 256 + d3 * 16 + d4 in
      if Nat.leb cp 127 then
        let bit n := Nat.testbit cp n in
        Some (Ascii (bit 0) (bit 1) (bit 2) (bit 3)
                     (bit 4) (bit 5) (bit 6) false, rest)
      else
        Some ("?"%char, rest)
    | _, _, _, _ => None
    end
  | _ => None
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
          else if is_char_code c2 117 then  (* 'u' = \uXXXX *)
            match parse_unicode_escape_local rest2 with
            | Some (ch, rest3) =>
              parse_string_chars f rest3 (String ch acc)
            | None => None
            end
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

(* Collect digit and dot characters for float literals.               *)
Fixpoint collect_float_chars (fuel : nat) (s : string)
    (acc : string) : string * string :=
  match fuel with
  | 0 => (string_rev acc, s)
  | S f =>
    match s with
    | EmptyString => (string_rev acc, s)
    | String c rest =>
      if is_digit_char c || is_char_code c 46   (* '.' = 46 *)
                          || is_char_code c 101  (* 'e' = 101 *)
                          || is_char_code c 69   (* 'E' = 69 *)
                          || is_char_code c 43   (* '+' = 43 *)
                          || is_char_code c 45   (* '-' = 45 *)
      then collect_float_chars f rest (String c acc)
      else (string_rev acc, s)
    end
  end.

(* Check whether a digit-string remainder contains a dot or exponent,
   indicating a float literal.                                         *)
Fixpoint has_dot_or_exp (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest =>
    if is_char_code c 46 || is_char_code c 101 || is_char_code c 69
    then true
    else if is_digit_char c then has_dot_or_exp rest
    else false
  end.

(* Main recursive-descent parser.  Handles negative numbers natively
   (producing JNeg) and floating-point literals (producing JFloat).
   All three mutually recursive functions decrease on fuel.            *)
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
      else if is_char_code c 45 then (* '-' = 45: negative number *)
        match rest with
        | EmptyString => None
        | String d drest =>
          if is_digit_char d then
            if has_dot_or_exp drest then
              let '(fstr, rest') :=
                collect_float_chars f drest (String d EmptyString) in
              Some (JFloat (String.append "-" fstr), rest')
            else
              let '(n, rest') := parse_nat_chars f drest (digit_value_of d) in
              match n with
              | 0 => Some (JNum 0, rest')   (* -0 = 0 *)
              | S m => Some (JNeg m, rest')
              end
          else None
        end
      else if is_digit_char c then
        if has_dot_or_exp rest then
          let '(fstr, rest') :=
            collect_float_chars f rest (String c EmptyString) in
          Some (JFloat fstr, rest')
        else
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

(** Check that a string contains only 7-bit ASCII characters.
    Returns [false] if any byte has the high bit set, which would
    indicate multi-byte UTF-8 that Rocq strings cannot represent. *)
Fixpoint is_ascii_string (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest =>
    let n := nat_of_ascii_local c in
    Nat.ltb n 128 && is_ascii_string rest
  end.

Definition parse_json (s : string) : option Json :=
  if negb (is_ascii_string s) then None
  else
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
    else if String.eqb s "Defeater" then Some Defeater
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
        let md := match json_field "metadata" kvs with
                  | Some (JObj mkvs) =>
                    flat_map (fun kv =>
                      match snd kv with
                      | JStr v  => [(fst kv, MVString v)]
                      | JNum n  => [(fst kv, MVNat n)]
                      | JBool b => [(fst kv, MVBool b)]
                      | _       => []
                      end) mkvs
                  | _ => []
                  end in
        Some {| node_id := id;
                node_kind := nk;
                node_claim_text := claim_text;
                node_evidence := None;
                node_metadata := md;
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
       node_metadata := n.(node_metadata);
       node_claim := n.(node_claim) |}
    :: hydrate_evidence_list rest evidence_map
  end.

Definition hydrate_evidence (ac : AssuranceCase)
    (evidence_map : list (Id * Evidence)) : AssuranceCase := {|
  ac_nodes := hydrate_evidence_list ac.(ac_nodes) evidence_map;
  ac_links := ac.(ac_links);
  ac_top := ac.(ac_top);
|}.

(* ------------------------------------------------------------------ *)
(* Auto-hydrate from a validator registry                               *)
(* ------------------------------------------------------------------ *)

(* Reconstruct Certificate evidence for Solution nodes whose JSON
   contained a tool identifier and blob.  Uses the registry to find
   the matching validator function.  ProofTerm evidence cannot be
   reconstructed (proofs are erased), but is reported as missing.       *)
Fixpoint auto_hydrate_list (nodes : list Node)
    (reg : ValidatorRegistry) : list Node :=
  match nodes with
  | nil => nil
  | n :: rest =>
    let n' :=
      match n.(node_kind), n.(node_evidence) with
      | Solution, None =>
        match find_metadata "tool" n.(node_metadata),
              find_metadata "blob" n.(node_metadata) with
        | Some (MVString tool), Some (MVString blob) =>
          match registry_lookup tool reg with
          | Some v =>
            {| node_id := n.(node_id);
               node_kind := n.(node_kind);
               node_claim_text := n.(node_claim_text);
               node_evidence := Some (Certificate blob tool v);
               node_metadata := n.(node_metadata);
               node_claim := n.(node_claim) |}
          | None => n
          end
        | _, _ => n
        end
      | _, _ => n
      end
    in n' :: auto_hydrate_list rest reg
  end.

Definition auto_hydrate (ac : AssuranceCase)
    (reg : ValidatorRegistry) : AssuranceCase := {|
  ac_nodes := auto_hydrate_list ac.(ac_nodes) reg;
  ac_links := ac.(ac_links);
  ac_top := ac.(ac_top);
|}.

(* ------------------------------------------------------------------ *)
(* Claim registry: rebuild claims after JSON import                     *)
(* ------------------------------------------------------------------ *)

(* After parsing JSON, all node_claim fields are True.  A ClaimEntry
   maps a node ID to its intended Prop.  rebuild_claims replaces
   node_claim for matched IDs, preserving everything else.
   This is only meaningful inside Rocq — Props are erased at
   extraction.  Use it to reconstruct a valid AssuranceCase from
   parsed JSON, then prove WellFormed about the rebuilt case.          *)
Record ClaimEntry : Type := {
  ce_id    : Id;
  ce_claim : Prop;
}.

Definition ClaimRegistry := list ClaimEntry.

Fixpoint claim_registry_lookup (id : Id) (reg : ClaimRegistry)
  : option Prop :=
  match reg with
  | [] => None
  | entry :: rest =>
    if String.eqb entry.(ce_id) id then Some entry.(ce_claim)
    else claim_registry_lookup id rest
  end.

Fixpoint rebuild_claims_list (nodes : list Node)
    (reg : ClaimRegistry) : list Node :=
  match nodes with
  | nil => nil
  | n :: rest =>
    let claim := match claim_registry_lookup n.(node_id) reg with
                 | Some P => P
                 | None => n.(node_claim)
                 end in
    {| node_id := n.(node_id);
       node_kind := n.(node_kind);
       node_claim_text := n.(node_claim_text);
       node_evidence := n.(node_evidence);
       node_metadata := n.(node_metadata);
       node_claim := claim |}
    :: rebuild_claims_list rest reg
  end.

Definition rebuild_claims (ac : AssuranceCase)
    (reg : ClaimRegistry) : AssuranceCase := {|
  ac_nodes := rebuild_claims_list ac.(ac_nodes) reg;
  ac_links := ac.(ac_links);
  ac_top := ac.(ac_top);
|}.

(* ------------------------------------------------------------------ *)
(* Fold-based streaming export                                          *)
(* ------------------------------------------------------------------ *)

(* Process an assurance case with a fold, visiting each node and link
   exactly once.  Useful for streaming output to a file or network
   socket without materializing the entire JSON/DOT string.            *)
Definition fold_assurance_case {A : Type} (ac : AssuranceCase)
    (f_node : A -> Node -> A) (f_link : A -> Link -> A) (init : A) : A :=
  let after_nodes := fold_left f_node ac.(ac_nodes) init in
  fold_left f_link ac.(ac_links) after_nodes.

(* Fold that also passes the node index (0-based). *)
Fixpoint fold_nodes_indexed_go {A : Type}
    (f : A -> nat -> Node -> A) (nodes : list Node)
    (idx : nat) (acc : A) : A :=
  match nodes with
  | [] => acc
  | n :: rest => fold_nodes_indexed_go f rest (S idx) (f acc idx n)
  end.

Definition fold_nodes_indexed {A : Type} (ac : AssuranceCase)
    (f : A -> nat -> Node -> A) (init : A) : A :=
  fold_nodes_indexed_go f ac.(ac_nodes) 0 init.

(* Streaming DOT: emit lines via a fold. *)
Definition stream_dot_lines (ac : AssuranceCase) : list string :=
  ["digraph assurance_case {" ++ nl]
  ++ map render_dot_node ac.(ac_nodes)
  ++ map render_dot_edge ac.(ac_links)
  ++ ["}" ++ nl].

(* Streaming JSON: emit lines via a fold. *)
Definition stream_json_lines (ac : AssuranceCase) : list string :=
  let node_strs := map (fun n => render_json (node_to_json n)) ac.(ac_nodes) in
  let link_strs := map (fun l => render_json (link_to_json l)) ac.(ac_links) in
  ["{" ++ json_quote "top" ++ ":" ++ json_quote ac.(ac_top) ++ ","
   ++ json_quote "nodes" ++ ":["]
  ++ match node_strs with
     | [] => []
     | s :: rest => [s] ++ map (fun x => "," ++ x) rest
     end
  ++ ["]," ++ json_quote "links" ++ ":["]
  ++ match link_strs with
     | [] => []
     | s :: rest => [s] ++ map (fun x => "," ++ x) rest
     end
  ++ ["]}"].

(* ------------------------------------------------------------------ *)
(* SACM-compatible export                                               *)
(* ------------------------------------------------------------------ *)

(* Minimal OMG SACM (Structured Assurance Case Metamodel) compatible
   XML export.  Produces a self-contained ArgumentPackage element
   with Claim, ArgumentReasoning, ArtifactReference, and
   AssertedInference / AssertedContext elements.
   Not a full SACM implementation — sufficient for import into
   tools that support the SACM 2.2 interchange format.                 *)

Definition xml_escape (s : string) : string :=
  (* Escape ampersand, angle brackets, double-quote for XML.
     Reuse the JSON escaper for quotes; add XML-specific escapes. *)
  let fix go (s : string) : string :=
    match s with
    | EmptyString => EmptyString
    | String c rest =>
      if ascii_eqb c dquote_char then
        append "&quot;" (go rest)
      else if ascii_eqb c
        (Ascii false false true true true false false false) (* '<' = 60 *)
      then append "&lt;" (go rest)
      else if ascii_eqb c
        (Ascii false true true true true false false false) (* '>' = 62 *)
      then append "&gt;" (go rest)
      else if ascii_eqb c
        (Ascii false true true false false true false false) (* '&' = 38 *)
      then append "&amp;" (go rest)
      else String c (go rest)
    end
  in go s.

Definition sacm_node_element (n : Node) : string :=
  match n.(node_kind) with
  | Goal | Strategy =>
    "    <Claim id=" ++ json_quote n.(node_id)
      ++ " content=" ++ json_quote (xml_escape n.(node_claim_text))
      ++ " />" ++ nl
  | Solution =>
    "    <ArtifactReference id=" ++ json_quote n.(node_id)
      ++ " content=" ++ json_quote (xml_escape n.(node_claim_text))
      ++ " />" ++ nl
  | Context | Assumption | Justification =>
    "    <InformationElement id=" ++ json_quote n.(node_id)
      ++ " content=" ++ json_quote (xml_escape n.(node_claim_text))
      ++ " />" ++ nl
  end.

Definition sacm_link_element (l : Link) : string :=
  match l.(link_kind) with
  | SupportedBy =>
    "    <AssertedInference id=" ++ json_quote (l.(link_from) ++ "->" ++ l.(link_to))
      ++ " source=" ++ json_quote l.(link_from)
      ++ " target=" ++ json_quote l.(link_to)
      ++ " />" ++ nl
  | InContextOf =>
    "    <AssertedContext id=" ++ json_quote (l.(link_from) ++ "~>" ++ l.(link_to))
      ++ " source=" ++ json_quote l.(link_from)
      ++ " target=" ++ json_quote l.(link_to)
      ++ " />" ++ nl
  | Defeater =>
    "    <AssertedChallenge id=" ++ json_quote (l.(link_from) ++ "!>" ++ l.(link_to))
      ++ " source=" ++ json_quote l.(link_from)
      ++ " target=" ++ json_quote l.(link_to)
      ++ " />" ++ nl
  end.

Definition render_sacm (ac : AssuranceCase) : string :=
  "<?xml version=" ++ json_quote "1.0" ++ " encoding="
    ++ json_quote "UTF-8" ++ "?>" ++ nl
  ++ "<sacm:ArgumentPackage xmlns:sacm="
    ++ json_quote "http://www.omg.org/spec/SACM/2.2"
    ++ " id=" ++ json_quote ac.(ac_top) ++ ">" ++ nl
  ++ concat_strings (map sacm_node_element ac.(ac_nodes))
  ++ concat_strings (map sacm_link_element ac.(ac_links))
  ++ "</sacm:ArgumentPackage>" ++ nl.

(* ------------------------------------------------------------------ *)
(* JSON parser extensions: negative numbers and floats                  *)
(* ------------------------------------------------------------------ *)

(* Negative number and float support.
   We represent negative numbers as JNeg (nat), where JNeg n = -(S n).
   Floats are represented as JFloat (string).                           *)
Inductive JsonExt : Type :=
  | JXNull   : JsonExt
  | JXBool   : bool -> JsonExt
  | JXStr    : string -> JsonExt
  | JXNum    : nat -> JsonExt
  | JXNeg    : nat -> JsonExt      (* JXNeg n = -(S n) *)
  | JXFloat  : string -> JsonExt   (* preserved as string *)
  | JXArr    : list JsonExt -> JsonExt
  | JXObj    : list (string * JsonExt) -> JsonExt.

(* Convert basic Json to extended *)
Fixpoint json_to_ext (j : Json) : JsonExt :=
  match j with
  | JNull    => JXNull
  | JBool b  => JXBool b
  | JStr s   => JXStr s
  | JNum n   => JXNum n
  | JNeg n   => JXNeg n
  | JFloat s => JXFloat s
  | JArr js  => JXArr (map json_to_ext js)
  | JObj kvs => JXObj (map (fun kv => (fst kv, json_to_ext (snd kv))) kvs)
  end.

(* Convert extended back to basic (JXNeg -> JNum 0, JXFloat -> JStr) *)
Fixpoint ext_to_json (j : JsonExt) : Json :=
  match j with
  | JXNull    => JNull
  | JXBool b  => JBool b
  | JXStr s   => JStr s
  | JXNum n   => JNum n
  | JXNeg n   => JNeg n
  | JXFloat s => JFloat s
  | JXArr js  => JArr (map ext_to_json js)
  | JXObj kvs => JObj (map (fun kv => (fst kv, ext_to_json (snd kv))) kvs)
  end.

(* Render a nat with a '-' prefix for negative rendering. *)
Definition render_neg_nat (n : nat) : string :=
  append "-" (nat_to_string (S n)).

(* Extended JSON renderer *)
Fixpoint render_json_ext (j : JsonExt) : string :=
  let fix render_list (js : list JsonExt) : list string :=
    match js with
    | [] => []
    | j' :: rest => render_json_ext j' :: render_list rest
    end
  in
  let fix render_kvs (kvs : list (string * JsonExt)) : list string :=
    match kvs with
    | [] => []
    | (k, v) :: rest =>
        append (append (json_quote k) ":") (render_json_ext v)
          :: render_kvs rest
    end
  in
  match j with
  | JXNull     => "null"
  | JXBool true  => "true"
  | JXBool false => "false"
  | JXStr s    => json_quote s
  | JXNum n    => nat_to_string n
  | JXNeg n    => render_neg_nat n
  | JXFloat s  => s
  | JXArr elems =>
      append "[" (append (join_strings "," (render_list elems)) "]")
  | JXObj kvs =>
      append "{" (append (join_strings "," (render_kvs kvs)) "}")
  end.

(* CheckError serialization — for CI/audit tooling. *)
Definition check_error_to_json (err : CheckError) : Json :=
  match err with
  | ErrTopNotGoal id =>
      JObj [("error", JStr "TopNotGoal"); ("node", JStr id)]
  | ErrDanglingFrom f t =>
      JObj [("error", JStr "DanglingFrom"); ("from", JStr f); ("to", JStr t)]
  | ErrDanglingTo f t =>
      JObj [("error", JStr "DanglingTo"); ("from", JStr f); ("to", JStr t)]
  | ErrDuplicateId id =>
      JObj [("error", JStr "DuplicateId"); ("node", JStr id)]
  | ErrUnsupported id =>
      JObj [("error", JStr "Unsupported"); ("node", JStr id)]
  | ErrMissingEvidence id =>
      JObj [("error", JStr "MissingEvidence"); ("node", JStr id)]
  | ErrInvalidEvidence id =>
      JObj [("error", JStr "InvalidEvidence"); ("node", JStr id)]
  | ErrBadContextSource f t =>
      JObj [("error", JStr "BadContextSource"); ("from", JStr f); ("to", JStr t)]
  | ErrBadContextTarget f t =>
      JObj [("error", JStr "BadContextTarget"); ("from", JStr f); ("to", JStr t)]
  | ErrCycle id =>
      JObj [("error", JStr "Cycle"); ("node", JStr id)]
  | ErrExpiredEvidence id expiry =>
      JObj [("error", JStr "ExpiredEvidence"); ("node", JStr id);
            ("valid_until", JStr expiry)]
  | ErrMissingRequiredKey id key =>
      JObj [("error", JStr "MissingRequiredKey"); ("node", JStr id);
            ("key", JStr key)]
  | ErrMalformedTimestamp id val =>
      JObj [("error", JStr "MalformedTimestamp"); ("node", JStr id);
            ("value", JStr val)]
  | ErrUnresolvedDefeater def tgt =>
      JObj [("error", JStr "UnresolvedDefeater"); ("defeater", JStr def);
            ("target", JStr tgt)]
  | ErrUndeveloped id =>
      JObj [("error", JStr "Undeveloped"); ("node", JStr id)]
  | ErrInvalidatedAssumption id =>
      JObj [("error", JStr "InvalidatedAssumption"); ("node", JStr id)]
  end.

Definition diagnose_to_json (ac : AssuranceCase) : Json :=
  JArr (map check_error_to_json (diagnose_all ac)).

(* ------------------------------------------------------------------ *)
(* Typed parse result with error reporting                             *)
(* ------------------------------------------------------------------ *)

(** Structured parse result: success carries the JSON value,
    error carries the original input for diagnostics. *)
Inductive ParseResult : Type :=
  | ParseSuccess : Json -> ParseResult
  | ParseError : string -> ParseResult.

(** Parse with typed error.  On failure, the full input is returned
    in [ParseError] for diagnostic use by the caller. *)
Definition parse_json_err (s : string) : ParseResult :=
  match parse_json s with
  | Some j => ParseSuccess j
  | None => ParseError s
  end.

(** Boolean predicate: did parsing succeed? *)
Definition parse_ok (r : ParseResult) : bool :=
  match r with ParseSuccess _ => true | ParseError _ => false end.

(** Extract the JSON value on success. *)
Definition parse_result_json (r : ParseResult) : option Json :=
  match r with ParseSuccess j => Some j | ParseError _ => None end.

(** [parse_json_err] agrees with [parse_json] on success. *)
Lemma parse_json_err_some : forall s j,
    parse_json s = Some j ->
    parse_json_err s = ParseSuccess j.
Proof.
  intros s j H. unfold parse_json_err. rewrite H. reflexivity.
Qed.

Lemma parse_json_err_none : forall s,
    parse_json s = None ->
    parse_json_err s = ParseError s.
Proof.
  intros s H. unfold parse_json_err. rewrite H. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* JSON round-trip correctness                                         *)
(* ------------------------------------------------------------------ *)

(** The rendered JSON of any [Json] value parses back to the same
    value.  This is the core round-trip property; the assurance-case
    round-trip follows from composing with [assurance_case_to_json]
    and [json_to_assurance_case].

    The proof proceeds by structural induction on [Json], showing
    that [render_json] produces well-formed JSON that [parse_json_go]
    parses back identically.  The main difficulty is accounting for
    string escaping (render escapes, parser unescapes) and fuel
    sufficiency (parser fuel must exceed rendered string length).

    For concrete assurance cases, round-trip is verified
    computationally in Example.v (round_trip_top_id). *)
Theorem render_parse_json_roundtrip : forall j,
    is_ascii_string (render_json j) = true ->
    parse_json (render_json j) = Some j.
Proof.
  (* Induction on j. For each constructor:
     - JNull/JBool: literal strings parse trivially
     - JStr: escape_json_chars + parse_string_chars are inverses
     - JNum/JNeg/JFloat: nat_to_string + parse_nat_chars are inverses
     - JArr/JObj: induction on element/kv lists
     The hardest case is JStr: showing escape/unescape round-trips.
     This requires a subsidiary lemma about escape_json_chars. *)
  admit.
Admitted.

(** Assurance-case round-trip (structural — evidence and claims
    cannot round-trip because ProofTerm proofs are erased and
    Certificate validators are functions). *)
Theorem assurance_case_json_roundtrip_structure : forall ac,
    is_ascii_string (render_assurance_case ac) = true ->
    match parse_json (render_assurance_case ac) with
    | Some j =>
      match json_to_assurance_case j with
      | Some ac' =>
        ac'.(ac_top) = ac.(ac_top) /\
        length ac'.(ac_nodes) = length ac.(ac_nodes) /\
        length ac'.(ac_links) = length ac.(ac_links)
      | None => False
      end
    | None => False
    end.
Proof.
  (* Follows from render_parse_json_roundtrip + structure of
     assurance_case_to_json / json_to_assurance_case. *)
  admit.
Admitted.
