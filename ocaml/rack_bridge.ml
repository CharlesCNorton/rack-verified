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

(* Shell-quote a single argument: wrap in single quotes, escaping
   any embedded single quotes as '\'' (POSIX sh).  Prevents
   injection when arguments contain spaces, semicolons, etc. *)
let shell_quote s =
  "'" ^ Str.global_replace (Str.regexp_string "'") "'\\''" s ^ "'"

let run_command_argv argv =
  let prog = List.hd argv in
  let args = Array.of_list argv in
  let (rd, wr) = Unix.pipe () in
  let pid = Unix.create_process prog args Unix.stdin wr Unix.stderr in
  Unix.close wr;
  let ic = Unix.in_channel_of_descr rd in
  let buf = Buffer.create 1024 in
  (try while true do
    Buffer.add_string buf (input_line ic);
    Buffer.add_char buf '\n'
  done with End_of_file -> ());
  close_in ic;
  let (_, status) = Unix.waitpid [] pid in
  (Buffer.contents buf, status)

let run_command_result tool argv =
  try
    let (output, status) = run_command_argv argv in
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

(* --- Minimal JSON value extraction (no external dependency) --- *)

(* Extract a string value for a key from a flat JSON object.
   Handles {"key": "value", ...} patterns without a full parser. *)
let json_extract_string key output =
  let pat = Str.regexp (Printf.sprintf {|"%s" *: *"\([^"]*\)"|} (Str.quote key)) in
  try let _ = Str.search_forward pat output 0 in
    Some (Str.matched_group 1 output)
  with Not_found -> None

(* Extract a boolean/status for a key. *)
let json_extract_field key output =
  let pat = Str.regexp (Printf.sprintf {|"%s" *: *\([^ ,}\n]*\)|} (Str.quote key)) in
  try let _ = Str.search_forward pat output 0 in
    Some (Str.matched_group 1 output)
  with Not_found -> None

(* --- CBMC bridge --- *)

(* CBMC --json-ui output contains {"cProverStatus": "SUCCESS"} or
   {"cProverStatus": "FAILURE"}.  Fall back to text pattern if
   JSON field extraction fails. *)
let run_cbmc ~binary ~function_name ~unwind =
  let argv = ["cbmc"; binary; "--function"; function_name;
              "--unwind"; string_of_int unwind; "--json-ui"] in
  match run_command_result "CBMC" argv with
  | Error e -> Error e
  | Ok output ->
    let success =
      match json_extract_string "cProverStatus" output with
      | Some "SUCCESS" -> true
      | Some _ -> false
      | None -> has_pattern "VERIFICATION SUCCESSFUL" output
    in
    if success then
      let blob = Printf.sprintf "CBMC:%s:%s:unwind=%d:pass" binary function_name unwind in
      Ok (make_evidence "CBMC" blob)
    else if has_pattern "VERIFICATION FAILED" output ||
            json_extract_string "cProverStatus" output = Some "FAILURE" then
      Error (VerificationFailed ("CBMC",
        Printf.sprintf "%s:%s:unwind=%d" binary function_name unwind))
    else
      Error (ParseFailed ("CBMC", output))

(* --- Kani bridge --- *)

(* Kani outputs a summary line "VERIFICATION:- SUCCESSFUL" or
   "VERIFICATION:- FAILED".  With --output-format=json it produces
   structured JSON; we try JSON first, fall back to text. *)
let run_kani ~harness ~unwind =
  let argv = ["cargo"; "kani"; "--harness"; harness;
              "--unwind"; string_of_int unwind] in
  match run_command_result "Kani" argv with
  | Error e -> Error e
  | Ok output ->
    let success =
      match json_extract_field "result" output with
      | Some s -> has_pattern "SUCCESS" s
      | None -> has_pattern "VERIFICATION:- SUCCESSFUL" output
    in
    if success then
      let blob = Printf.sprintf "Kani:%s:unwind=%d:success" harness unwind in
      Ok (make_evidence "Kani" blob)
    else if has_pattern "VERIFICATION:- FAILED" output ||
            json_extract_field "result" output = Some "\"FAILURE\"" then
      Error (VerificationFailed ("Kani",
        Printf.sprintf "%s:unwind=%d" harness unwind))
    else
      Error (ParseFailed ("Kani", output))

(* --- SAW bridge --- *)

let run_saw ~script =
  let argv = ["saw"; script] in
  match run_command_result "SAW" argv with
  | Error e -> Error e
  | Ok output ->
    if has_pattern "verified" output then
      let blob = Printf.sprintf "SAW:%s:verified" script in
      Ok (make_evidence "SAW" blob)
    else
      Error (VerificationFailed ("SAW", script))

(* --- Verus bridge --- *)

let run_verus ~file =
  let argv = ["verus"; file] in
  match run_command_result "Verus" argv with
  | Error e -> Error e
  | Ok output ->
    if has_pattern "verification results:: verified" output then
      let blob = Printf.sprintf "Verus:%s:verified" file in
      Ok (make_evidence "Verus" blob)
    else
      Error (VerificationFailed ("Verus", file))

(* --- Alloy bridge --- *)

let run_alloy ~model ~scope =
  let argv = ["java"; "-jar"; "alloy.jar"; "-exec"; model;
              "-scope"; string_of_int scope] in
  match run_command_result "Alloy" argv with
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

let run_tool ~tool ~argv ~success_pattern =
  match run_command_result tool argv with
  | Error e -> Error e
  | Ok output ->
    if has_pattern success_pattern output then
      let blob = Printf.sprintf "%s:%s:pass" tool (String.concat " " argv) in
      Ok (make_evidence tool blob)
    else
      Error (VerificationFailed (tool, String.concat " " argv))
