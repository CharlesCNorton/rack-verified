(* rack_sacm_validate.ml — Lightweight SACM 2.2 structure validation.
   Checks that render_sacm output has the expected XML structure
   without requiring a full XSD validator.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml rack_sacm_validate.ml -o rack_sacm_validate
*)

open Rack
open Rack_util

(* --- Structural validators --- *)

let has_xml_declaration s =
  try let _ = Str.search_forward (Str.regexp_string "<?xml version=") s 0 in true
  with Not_found -> false

let has_sacm_namespace s =
  try let _ = Str.search_forward
    (Str.regexp_string "xmlns:sacm=\"http://www.omg.org/spec/SACM/2.2\"") s 0 in true
  with Not_found -> false

let has_argument_package s =
  try let _ = Str.search_forward (Str.regexp_string "<sacm:ArgumentPackage") s 0 in true
  with Not_found -> false

let has_closing_tag s =
  try let _ = Str.search_forward (Str.regexp_string "</sacm:ArgumentPackage>") s 0 in true
  with Not_found -> false

(* Check that every Claim element has id and content attributes *)
let check_claim_elements s =
  let re = Str.regexp "<Claim " in
  let rec check pos =
    match (try Some (Str.search_forward re s pos) with Not_found -> None) with
    | None -> true
    | Some i ->
      let line_end = try Str.search_forward (Str.regexp "/>") s i with Not_found -> -1 in
      if line_end < 0 then false
      else
        let chunk = String.sub s i (line_end - i + 2) in
        let has_id = try let _ = Str.search_forward (Str.regexp_string "id=") chunk 0 in true
                     with Not_found -> false in
        let has_content = try let _ = Str.search_forward (Str.regexp_string "content=") chunk 0 in true
                          with Not_found -> false in
        if has_id && has_content then check (line_end + 2)
        else false
  in
  check 0

(* Check ArtifactReference elements *)
let check_artifact_elements s =
  let re = Str.regexp "<ArtifactReference " in
  let rec check pos =
    match (try Some (Str.search_forward re s pos) with Not_found -> None) with
    | None -> true
    | Some i ->
      let line_end = try Str.search_forward (Str.regexp "/>") s i with Not_found -> -1 in
      if line_end < 0 then false
      else
        let chunk = String.sub s i (line_end - i + 2) in
        let has_id = try let _ = Str.search_forward (Str.regexp_string "id=") chunk 0 in true
                     with Not_found -> false in
        if has_id then check (line_end + 2) else false
  in
  check 0

(* Check AssertedInference elements have source and target *)
let check_inference_elements s =
  let re = Str.regexp "<AssertedInference " in
  let rec check pos =
    match (try Some (Str.search_forward re s pos) with Not_found -> None) with
    | None -> true
    | Some i ->
      let line_end = try Str.search_forward (Str.regexp "/>") s i with Not_found -> -1 in
      if line_end < 0 then false
      else
        let chunk = String.sub s i (line_end - i + 2) in
        let has_src = try let _ = Str.search_forward (Str.regexp_string "source=") chunk 0 in true
                      with Not_found -> false in
        let has_tgt = try let _ = Str.search_forward (Str.regexp_string "target=") chunk 0 in true
                      with Not_found -> false in
        if has_src && has_tgt then check (line_end + 2) else false
  in
  check 0

type validation_result = {
  xml_declaration : bool;
  sacm_namespace : bool;
  argument_package : bool;
  closing_tag : bool;
  claims_valid : bool;
  artifacts_valid : bool;
  inferences_valid : bool;
}

let validate_sacm_string s = {
  xml_declaration = has_xml_declaration s;
  sacm_namespace = has_sacm_namespace s;
  argument_package = has_argument_package s;
  closing_tag = has_closing_tag s;
  claims_valid = check_claim_elements s;
  artifacts_valid = check_artifact_elements s;
  inferences_valid = check_inference_elements s;
}

let all_valid r =
  r.xml_declaration && r.sacm_namespace && r.argument_package &&
  r.closing_tag && r.claims_valid && r.artifacts_valid &&
  r.inferences_valid

let validate_sacm_ac ac =
  let sacm_str = string_of_coq (render_sacm ac) in
  let result = validate_sacm_string sacm_str in
  (all_valid result, result)
