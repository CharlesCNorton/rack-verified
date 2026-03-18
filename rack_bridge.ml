(* rack_bridge.ml — FFI shims for external formal-methods tools.
   Each function spawns a subprocess, parses its output, and
   returns a Rack-compatible evidence value.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml rack_bridge.ml -o rack_bridge
*)

open Rack
open Rack_util

(* --- Structured error type --- *)

type bridge_error =
  | ToolNotFound of string
  | ToolFailed of string * int  (* tool, exit code *)
  | ParseFailed of string * string  (* tool, raw output *)
  | VerificationFailed of string * string  (* tool, details *)

let string_of_bridge_error = function
  | ToolNotFound tool -> Printf.sprintf "%s: tool not found on PATH" tool
  | ToolFailed (tool, code) -> Printf.sprintf "%s: exited with code %d" tool code
  | ParseFailed (tool, _) -> Printf.sprintf "%s: could not parse output" tool
  | VerificationFailed (tool, details) -> Printf.sprintf "%s: verification failed: %s" tool details

(* --- Subprocess runner --- *)

let run_command cmd =
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 1024 in
  (try while true do
    Buffer.add_string buf (input_line ic);
    Buffer.add_char buf '\n'
  done with End_of_file -> ());
  let status = Unix.close_process_in ic in
  (Buffer.contents buf, status)

let run_command_result tool cmd =
  try
    let (output, status) = run_command cmd in
    match status with
    | Unix.WEXITED 0 -> Ok output
    | Unix.WEXITED code -> Error (ToolFailed (tool, code))
    | _ -> Error (ToolFailed (tool, -1))
  with Unix.Unix_error (Unix.ENOENT, _, _) ->
    Error (ToolNotFound tool)

let has_pattern pattern output =
  try let _ = Str.search_forward (Str.regexp_string pattern) output 0 in true
  with Not_found -> false

let make_evidence tool blob =
  let validator s =
    if string_of_coq s = blob then Rack.True else Rack.False
  in
  Certificate (coq_of_string blob, coq_of_string tool, validator)

(* --- CBMC bridge --- *)

let run_cbmc ~binary ~function_name ~unwind =
  let cmd = Printf.sprintf "cbmc %s --function %s --unwind %d --json-ui 2>&1"
    binary function_name unwind in
  match run_command_result "CBMC" cmd with
  | Error e -> Error e
  | Ok output ->
    if has_pattern "VERIFICATION SUCCESSFUL" output then
      let blob = Printf.sprintf "CBMC:%s:%s:unwind=%d:pass" binary function_name unwind in
      Ok (make_evidence "CBMC" blob)
    else if has_pattern "VERIFICATION FAILED" output then
      Error (VerificationFailed ("CBMC",
        Printf.sprintf "%s:%s:unwind=%d" binary function_name unwind))
    else
      Error (ParseFailed ("CBMC", output))

(* --- Kani bridge --- *)

let run_kani ~harness ~unwind =
  let cmd = Printf.sprintf "cargo kani --harness %s --unwind %d 2>&1"
    harness unwind in
  match run_command_result "Kani" cmd with
  | Error e -> Error e
  | Ok output ->
    if has_pattern "VERIFICATION:- SUCCESSFUL" output then
      let blob = Printf.sprintf "Kani:%s:unwind=%d:success" harness unwind in
      Ok (make_evidence "Kani" blob)
    else if has_pattern "VERIFICATION:- FAILED" output then
      Error (VerificationFailed ("Kani",
        Printf.sprintf "%s:unwind=%d" harness unwind))
    else
      Error (ParseFailed ("Kani", output))

(* --- SAW bridge --- *)

let run_saw ~script =
  let cmd = Printf.sprintf "saw %s 2>&1" script in
  match run_command_result "SAW" cmd with
  | Error e -> Error e
  | Ok output ->
    if has_pattern "verified" output then
      let blob = Printf.sprintf "SAW:%s:verified" script in
      Ok (make_evidence "SAW" blob)
    else
      Error (VerificationFailed ("SAW", script))

(* --- Verus bridge --- *)

let run_verus ~file =
  let cmd = Printf.sprintf "verus %s 2>&1" file in
  match run_command_result "Verus" cmd with
  | Error e -> Error e
  | Ok output ->
    if has_pattern "verification results:: verified" output then
      let blob = Printf.sprintf "Verus:%s:verified" file in
      Ok (make_evidence "Verus" blob)
    else
      Error (VerificationFailed ("Verus", file))

(* --- Alloy bridge --- *)

let run_alloy ~model ~scope =
  let cmd = Printf.sprintf "java -jar alloy.jar -exec %s -scope %d 2>&1"
    model scope in
  match run_command_result "Alloy" cmd with
  | Error e -> Error e
  | Ok output ->
    if has_pattern "No counterexample found" output then
      let blob = Printf.sprintf "Alloy:%s:scope=%d:no_cex" model scope in
      Ok (make_evidence "Alloy" blob)
    else if has_pattern "Counterexample found" output then
      Error (VerificationFailed ("Alloy",
        Printf.sprintf "%s:scope=%d:counterexample" model scope))
    else
      Error (ParseFailed ("Alloy", output))

(* --- Generic tool runner --- *)

let run_tool ~tool ~cmd ~success_pattern =
  match run_command_result tool cmd with
  | Error e -> Error e
  | Ok output ->
    if has_pattern success_pattern output then
      let blob = Printf.sprintf "%s:%s:pass" tool cmd in
      Ok (make_evidence tool blob)
    else
      Error (VerificationFailed (tool, cmd))
