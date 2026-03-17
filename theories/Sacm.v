(* ------------------------------------------------------------------ *)
(* SACM-compatible export                                               *)
(* ------------------------------------------------------------------ *)

From RACK Require Import Core.
From RACK Require Import Json.
From RACK Require Import Dot.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

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
