(* ------------------------------------------------------------------ *)
(* JSON: AST, escaping, rendering, parsing, extensions                  *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
From Stdlib Require Import Lia.
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

(* 'u' for \uXXXX Unicode escapes.  0x75 = 117. *)
Definition u_char : ascii :=
  Ascii true false true false true true true false.

(* '0' digit.  0x30 = 48. *)
Definition zero_char : ascii :=
  Ascii false false false false true true false false.

(* A character is a JSON control character when its code is < 32,
   i.e., bits 5, 6, 7 are all zero.  JSON requires \uXXXX escaping
   for all control characters not covered by a named escape. *)
Definition is_control (c : ascii) : bool :=
  match c with
  | Ascii _ _ _ _ _ b5 b6 b7 => negb b5 && negb b6 && negb b7
  end.

(* Low nibble of a control character (bits 0-3). *)
Definition ctrl_lo (c : ascii) : nat :=
  match c with
  | Ascii b0 b1 b2 b3 _ _ _ _ =>
    (if b0 then 1 else 0) + (if b1 then 2 else 0) +
    (if b2 then 4 else 0) + (if b3 then 8 else 0)
  end.

(* High nibble of a control character (bit 4 only, since code < 32). *)
Definition ctrl_hi (c : ascii) : nat :=
  match c with
  | Ascii _ _ _ _ b4 _ _ _ => if b4 then 1 else 0
  end.

(* Hex digit character for values 0-15. *)
Definition hex_digit_char (n : nat) : ascii :=
  match n with
  | 0 => "0"%char | 1 => "1"%char | 2 => "2"%char | 3 => "3"%char
  | 4 => "4"%char | 5 => "5"%char | 6 => "6"%char | 7 => "7"%char
  | 8 => "8"%char | 9 => "9"%char | 10 => "a"%char | 11 => "b"%char
  | 12 => "c"%char | 13 => "d"%char | 14 => "e"%char | _ => "f"%char
  end.

(* Escape characters special in JSON strings: dquote, backslash,
   and all control characters U+0000 to U+001F per RFC 8259.           *)
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
    else if is_control c then
      String backslash_char
        (String u_char
          (String zero_char
            (String zero_char
              (String (hex_digit_char (ctrl_hi c))
                (String (hex_digit_char (ctrl_lo c))
                  (escape_json_chars rest))))))
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

(** Check that the remainder after parsing contains only whitespace. *)
Fixpoint all_whitespace (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest =>
    if is_whitespace_char c then all_whitespace rest else false
  end.

Definition parse_json (s : string) : option Json :=
  if negb (is_ascii_string s) then None
  else
    match parse_json_go (string_length s) s with
    | Some (j, rest) =>
      if all_whitespace rest then Some j else None
    | None => None
    end.

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
    error carries a reason tag and the original input for diagnostics. *)
Inductive ParseErrorKind : Type :=
  | PENotAscii
  | PESyntax
  | PETrailingGarbage.

Inductive ParseResult : Type :=
  | ParseSuccess : Json -> ParseResult
  | ParseError : ParseErrorKind -> string -> ParseResult.

(** Parse with typed error.  On failure, a [ParseErrorKind] tag
    and the full input are returned for diagnostic use. *)
Definition parse_json_err (s : string) : ParseResult :=
  if negb (is_ascii_string s) then ParseError PENotAscii s
  else
    match parse_json_go (string_length s) s with
    | Some (j, rest) =>
      if all_whitespace rest then ParseSuccess j
      else ParseError PETrailingGarbage s
    | None => ParseError PESyntax s
    end.

(** Boolean predicate: did parsing succeed? *)
Definition parse_ok (r : ParseResult) : bool :=
  match r with ParseSuccess _ => true | ParseError _ _ => false end.

(** Extract the JSON value on success. *)
Definition parse_result_json (r : ParseResult) : option Json :=
  match r with ParseSuccess j => Some j | ParseError _ _ => None end.

(** [parse_json_err] agrees with [parse_json] on success. *)
Lemma parse_json_err_some : forall s j,
    parse_json s = Some j ->
    parse_json_err s = ParseSuccess j.
Proof.
  intros s j H. unfold parse_json in H.
  destruct (is_ascii_string s) eqn:Easc; [| discriminate].
  destruct (parse_json_go (string_length s) s) as [[j' rest]|] eqn:Ego;
    [| discriminate].
  destruct (all_whitespace rest) eqn:Erest; [| discriminate].
  injection H as <-.
  unfold parse_json_err. rewrite Easc. rewrite Ego. rewrite Erest.
  reflexivity.
Qed.

Lemma parse_json_err_none : forall s,
    parse_json s = None ->
    exists k, parse_json_err s = ParseError k s.
Proof.
  intros s H. unfold parse_json in H.
  destruct (is_ascii_string s) eqn:Easc.
  - destruct (parse_json_go (string_length s) s) as [[j' rest]|] eqn:Ego.
    + destruct (all_whitespace rest) eqn:Erest; [discriminate |].
      exists PETrailingGarbage. unfold parse_json_err.
      rewrite Easc, Ego, Erest. reflexivity.
    + exists PESyntax. unfold parse_json_err.
      rewrite Easc, Ego. reflexivity.
  - exists PENotAscii. unfold parse_json_err.
    rewrite Easc. reflexivity.
Qed.

(* ================================================================== *)
(* Escape / parse string roundtrip                                     *)
(* ================================================================== *)

Lemma ascii_eqb_eq : forall a b : ascii,
    ascii_eqb a b = true -> a = b.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold ascii_eqb. intro H.
  repeat (apply Bool.andb_true_iff in H; destruct H as [H ?]).
  apply Bool.eqb_prop in H. apply Bool.eqb_prop in H0.
  apply Bool.eqb_prop in H1. apply Bool.eqb_prop in H2.
  apply Bool.eqb_prop in H3. apply Bool.eqb_prop in H4.
  apply Bool.eqb_prop in H5. apply Bool.eqb_prop in H6.
  subst. reflexivity.
Qed.

Lemma not_dquote_not_34 : forall c,
    ascii_eqb c dquote_char = false ->
    is_char_code c 34 = false.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7] H.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    vm_compute in H |- *; try reflexivity; try discriminate.
Qed.

Lemma not_backslash_not_92 : forall c,
    ascii_eqb c backslash_char = false ->
    is_char_code c 92 = false.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7] H.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    vm_compute in H |- *; try reflexivity; try discriminate.
Qed.

Lemma string_rev_append_assoc : forall s1 s2 s3,
    string_rev_append s1 (String.append s2 s3) =
    String.append (string_rev_append s1 s2) s3.
Proof.
  induction s1 as [|c s1' IH]; intros s2 s3; simpl.
  - reflexivity.
  - exact (IH (String c s2) s3).
Qed.

Lemma string_rev_append_app : forall s1 s2,
    string_rev_append s1 s2 =
    String.append (string_rev s1) s2.
Proof.
  intros s1 s2. unfold string_rev.
  rewrite <- string_rev_append_assoc. simpl. reflexivity.
Qed.

Lemma string_rev_append_involutive : forall s acc,
    string_rev_append (string_rev_append s acc) EmptyString =
    string_rev_append acc s.
Proof.
  induction s as [|c s' IH]; intro acc; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma string_rev_rev : forall s,
    string_rev (string_rev s) = s.
Proof.
  intro s. unfold string_rev.
  exact (string_rev_append_involutive s EmptyString).
Qed.

(** One parse step through a \u00XY control-character escape. *)
Lemma parse_escape_control_step : forall c f input acc,
    is_control c = true ->
    parse_string_chars (S f)
      (String backslash_char
        (String u_char
          (String zero_char
            (String zero_char
              (String (hex_digit_char (ctrl_hi c))
                (String (hex_digit_char (ctrl_lo c)) input))))))
      acc
    = parse_string_chars f input (String c acc).
Proof.
  intros c f input acc Hctrl.
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold is_control in Hctrl.
  destruct b5; [discriminate|]; destruct b6; [discriminate|];
    destruct b7; [discriminate|].
  destruct b0, b1, b2, b3, b4; reflexivity.
Qed.

(** Core roundtrip: parsing an escaped string followed by a closing
    double-quote reconstructs the original string. *)
Lemma escape_parse_inverse : forall s fuel acc rest,
    fuel > string_length s ->
    parse_string_chars fuel
      (String.append (escape_json_chars s) (String dquote_char rest))
      acc =
    Some (string_rev (string_rev_append s acc), rest).
Proof.
  induction s as [|c s' IH]; intros fuel acc rest Hfuel.
  - destruct fuel as [|f]; [inversion Hfuel |].
    simpl. reflexivity.
  - destruct fuel as [|f]; [inversion Hfuel |].
    simpl in Hfuel. apply Nat.succ_lt_mono in Hfuel.
    simpl escape_json_chars.
    change (string_rev_append (String c s') acc)
      with (string_rev_append s' (String c acc)).
    destruct (ascii_eqb c dquote_char) eqn:Ed.
    { apply ascii_eqb_eq in Ed. subst c. simpl.
      exact (IH f (String dquote_char acc) rest Hfuel). }
    destruct (ascii_eqb c backslash_char) eqn:Eb.
    { apply ascii_eqb_eq in Eb. subst c. simpl.
      exact (IH f (String backslash_char acc) rest Hfuel). }
    destruct (ascii_eqb c nl_char) eqn:En.
    { apply ascii_eqb_eq in En. subst c. simpl.
      exact (IH f (String nl_char acc) rest Hfuel). }
    destruct (ascii_eqb c cr_char) eqn:Er.
    { apply ascii_eqb_eq in Er. subst c. simpl.
      exact (IH f (String cr_char acc) rest Hfuel). }
    destruct (ascii_eqb c tab_char) eqn:Et.
    { apply ascii_eqb_eq in Et. subst c. simpl.
      exact (IH f (String tab_char acc) rest Hfuel). }
    destruct (ascii_eqb c bs_char) eqn:Ebs.
    { apply ascii_eqb_eq in Ebs. subst c. simpl.
      exact (IH f (String bs_char acc) rest Hfuel). }
    destruct (ascii_eqb c ff_char) eqn:Eff.
    { apply ascii_eqb_eq in Eff. subst c. simpl.
      exact (IH f (String ff_char acc) rest Hfuel). }
    destruct (is_control c) eqn:Ectrl.
    { (* Control character: \u00XY escape *)
      simpl (String.append (String _ _) _).
      rewrite parse_escape_control_step; [| exact Ectrl].
      exact (IH f (String c acc) rest Hfuel). }
    simpl.
    rewrite (not_dquote_not_34 c Ed).
    rewrite (not_backslash_not_92 c Eb).
    exact (IH f (String c acc) rest Hfuel).
Qed.

(** User-facing roundtrip: parse(render(s)) = s. *)
Theorem escape_unescape_roundtrip : forall s rest,
    parse_string_chars (S (string_length s))
      (String.append (escape_json_chars s) (String dquote_char rest))
      EmptyString =
    Some (s, rest).
Proof.
  intros s rest.
  rewrite (escape_parse_inverse s (S (string_length s)) EmptyString rest
             (Nat.lt_succ_diag_r _)).
  unfold string_rev. rewrite string_rev_append_involutive. reflexivity.
Qed.

(* ================================================================== *)
(* Render / parse JSON roundtrip (string case)                         *)
(* ================================================================== *)

(** If [parse_string_chars] succeeds at fuel [f1], it succeeds
    with the same result at any fuel [f2 >= f1]. *)
Lemma parse_string_chars_mono : forall f1 s acc result,
    parse_string_chars f1 s acc = Some result ->
    forall f2, f1 <= f2 ->
    parse_string_chars f2 s acc = Some result.
Proof.
  induction f1 as [|f1' IH]; intros s acc result H1 f2 Hle.
  - simpl in H1. discriminate.
  - destruct f2 as [|f2']; [lia |].
    apply Nat.succ_le_mono in Hle.
    simpl in H1 |- *.
    destruct s as [|c rest]; [exact H1 |].
    destruct (is_char_code c 34); [exact H1 |].
    destruct (is_char_code c 92).
    + destruct rest as [|c2 rest2]; [exact H1 |].
      destruct (is_char_code c2 34); [exact (IH _ _ _ H1 f2' Hle) |].
      destruct (is_char_code c2 92); [exact (IH _ _ _ H1 f2' Hle) |].
      destruct (is_char_code c2 110); [exact (IH _ _ _ H1 f2' Hle) |].
      destruct (is_char_code c2 114); [exact (IH _ _ _ H1 f2' Hle) |].
      destruct (is_char_code c2 116); [exact (IH _ _ _ H1 f2' Hle) |].
      destruct (is_char_code c2 98); [exact (IH _ _ _ H1 f2' Hle) |].
      destruct (is_char_code c2 102); [exact (IH _ _ _ H1 f2' Hle) |].
      destruct (is_char_code c2 117).
      * destruct (parse_unicode_escape_local rest2) as [[ch rest3]|];
          [exact (IH _ _ _ H1 f2' Hle) | exact H1].
      * exact H1.
    + exact (IH _ _ _ H1 f2' Hle).
Qed.

(* ================================================================== *)
(* Full AST render/parse roundtrip                                     *)
(* ================================================================== *)

(** Size measure for fuel computation. *)
Fixpoint json_depth (j : Json) : nat :=
  match j with
  | JNull | JBool _ | JStr _ | JNum _ | JNeg _ | JFloat _ => 1
  | JArr elems =>
    S (fold_right (fun j' acc => json_depth j' + acc) 0 elems)
  | JObj kvs =>
    S (fold_right (fun kv acc => json_depth (snd kv) + acc) 0 kvs)
  end.

(** Literal roundtrips: null, true, false parse back correctly. *)
Lemma render_parse_null : forall fuel rest,
    fuel > 0 ->
    parse_json_go fuel (String.append "null" rest) = Some (JNull, rest).
Proof. intros [|f] rest H; [lia |]. reflexivity. Qed.

Lemma render_parse_true : forall fuel rest,
    fuel > 0 ->
    parse_json_go fuel (String.append "true" rest) = Some (JBool true, rest).
Proof. intros [|f] rest H; [lia |]. reflexivity. Qed.

Lemma render_parse_false : forall fuel rest,
    fuel > 0 ->
    parse_json_go fuel (String.append "false" rest) = Some (JBool false, rest).
Proof. intros [|f] rest H; [lia |]. reflexivity. Qed.

Theorem render_parse_json_roundtrip_literals : forall fuel rest,
    fuel > 0 ->
    parse_json_go fuel (String.append "null" rest) = Some (JNull, rest) /\
    parse_json_go fuel (String.append "true" rest) = Some (JBool true, rest) /\
    parse_json_go fuel (String.append "false" rest) = Some (JBool false, rest).
Proof.
  intros [|f] rest H; [lia |]. repeat split; reflexivity.
Qed.

