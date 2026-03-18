(* rack_cli.ml — CLI tool for validating RACK assurance cases.
   Reads JSON from stdin, runs check_well_formed + diagnose_all,
   and exits with nonzero code on failure.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_cli.ml -o rack_cli
   or:
     ocamlopt -I +str str.cmxa rack.ml rack_cli.ml -o rack_cli

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

(* --- Coq string <-> OCaml string helpers --- *)

let string_of_coq s =
  let buf = Buffer.create 64 in
  let rec go = function
    | EmptyString -> ()
    | String (Ascii (b0,b1,b2,b3,b4,b5,b6,b7), rest) ->
      let n =
        (if b0 then 1 else 0) lor
        (if b1 then 2 else 0) lor
        (if b2 then 4 else 0) lor
        (if b3 then 8 else 0) lor
        (if b4 then 16 else 0) lor
        (if b5 then 32 else 0) lor
        (if b6 then 64 else 0) lor
        (if b7 then 128 else 0)
      in
      Buffer.add_char buf (Char.chr n);
      go rest
  in
  go s;
  Buffer.contents buf

let coq_of_string s =
  let len = String.length s in
  let rec go i =
    if i >= len then EmptyString
    else
      let c = Char.code s.[i] in
      let bit n = if c land (1 lsl n) <> 0 then True else False in
      String (Ascii (bit 0, bit 1, bit 2, bit 3,
                     bit 4, bit 5, bit 6, bit 7),
              go (i + 1))
  in
  go 0

(* --- Read all of stdin --- *)

let read_stdin () =
  let buf = Buffer.create 4096 in
  (try while true do
    Buffer.add_string buf (input_line stdin);
    Buffer.add_char buf '\n'
  done with End_of_file -> ());
  Buffer.contents buf

(* --- Coq list to OCaml list --- *)

let rec list_of_coq = function
  | Nil -> []
  | Cons (x, rest) -> x :: list_of_coq rest

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
        if check_well_formed ac then begin
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
