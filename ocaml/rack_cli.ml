(* rack_cli.ml — CLI tool for validating RACK assurance cases.
   Reads JSON from stdin, runs check_wf_extended + diagnose_all,
   and exits with nonzero code on failure.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml rack_cli.ml -o rack_cli
   or:
     ocamlopt -I +str str.cmxa rack.ml rack_util.ml rack_cli.ml -o rack_cli

   Usage:
     cat case.json | ./rack_cli
     ./rack_cli < case.json
     ./rack_cli --check < case.json
     ./rack_cli --diagnose < case.json
     ./rack_cli --dot < case.json
     ./rack_cli --json-pretty < case.json
     ./rack_cli --sacm < case.json
*)

open Rack
open Rack_util

(* --- Read all of stdin --- *)

let read_stdin () =
  let buf = Buffer.create 4096 in
  (try while true do
    Buffer.add_string buf (input_line stdin);
    Buffer.add_char buf '\n'
  done with End_of_file -> ());
  Buffer.contents buf

(* --- Render check errors --- *)

let render_error err =
  string_of_coq (render_json (check_error_to_json err))

(* --- Main --- *)

let () =
  let mode = ref "check" in
  Array.iter (fun arg ->
    if arg = "--check" then mode := "check"
    else if arg = "--diagnose" then mode := "diagnose"
    else if arg = "--dot" then mode := "dot"
    else if arg = "--json-pretty" then mode := "pretty"
    else if arg = "--sacm" then mode := "sacm"
    else if arg = "--help" || arg = "-h" then begin
      Printf.printf "Usage: rack_cli [--check|--diagnose|--dot|--json-pretty|--sacm] < input.json\n";
      Printf.printf "  --check       Validate well-formedness (default)\n";
      Printf.printf "  --diagnose    Report all diagnostic errors as JSON\n";
      Printf.printf "  --dot         Convert to DOT graph\n";
      Printf.printf "  --json-pretty Pretty-print JSON\n";
      Printf.printf "  --sacm        Export as SACM XML\n";
      exit 0
    end
  ) Sys.argv;

  let input = read_stdin () in
  let coq_input = coq_of_string input in

  match parse_json coq_input with
  | None ->
    Printf.eprintf "Error: failed to parse JSON input\n";
    exit 2
  | Some j ->
    match json_to_assurance_case j with
    | None ->
      Printf.eprintf "Error: JSON is not a valid assurance case\n";
      exit 2
    | Some ac ->
      match !mode with
      | "check" ->
        if coq_bool_to_bool (check_wf_extended ac) then begin
          Printf.printf "PASS: assurance case is well-formed\n";
          exit 0
        end else begin
          Printf.eprintf "FAIL: assurance case is NOT well-formed\n";
          let errors = list_of_coq (diagnose_all ac) in
          List.iter (fun e ->
            Printf.eprintf "  %s\n" (render_error e)
          ) errors;
          exit 1
        end
      | "diagnose" ->
        let diag_json = diagnose_to_json ac in
        Printf.printf "%s\n" (string_of_coq (render_json_pretty diag_json));
        let errors = list_of_coq (diagnose_all ac) in
        if errors = [] then exit 0 else exit 1
      | "dot" ->
        Printf.printf "%s" (string_of_coq (render_dot ac));
        exit 0
      | "pretty" ->
        Printf.printf "%s\n" (string_of_coq (render_assurance_case_pretty ac));
        exit 0
      | "sacm" ->
        Printf.printf "%s" (string_of_coq (render_sacm ac));
        exit 0
      | m ->
        Printf.eprintf "Unknown mode: %s\n" m;
        exit 2
