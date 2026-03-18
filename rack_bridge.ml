(* rack_bridge.ml — FFI shims for external formal-methods tools.
   Each function spawns a subprocess, parses its output, and
   returns a Rack-compatible evidence value.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml rack_bridge.ml -o rack_bridge
*)

open Rack
open Rack_util

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

let run_command_ok cmd =
  let (output, status) = run_command cmd in
  match status with
  | Unix.WEXITED 0 -> Some output
  | _ -> None

(* --- CBMC bridge --- *)

let run_cbmc ~binary ~function_name ~unwind =
  let cmd = Printf.sprintf "cbmc %s --function %s --unwind %d --json-ui 2>&1"
    binary function_name unwind in
  match run_command_ok cmd with
  | None -> None
  | Some output ->
    let blob = Printf.sprintf "CBMC:%s:%s:unwind=%d:pass" binary function_name unwind in
    let validator = fun s ->
      if string_of_coq s = blob then Rack.True else Rack.False
    in
    Some (Certificate (coq_of_string blob, coq_of_string "CBMC", validator))

(* --- Kani bridge --- *)

let run_kani ~harness ~unwind =
  let cmd = Printf.sprintf "cargo kani --harness %s --unwind %d 2>&1"
    harness unwind in
  match run_command_ok cmd with
  | None -> None
  | Some output ->
    if String.length output > 0 &&
       (try let _ = Str.search_forward (Str.regexp_string "VERIFICATION:- SUCCESSFUL") output 0 in true
        with Not_found -> false) then
      let blob = Printf.sprintf "Kani:%s:unwind=%d:success" harness unwind in
      let validator = fun s ->
        if string_of_coq s = blob then Rack.True else Rack.False
      in
      Some (Certificate (coq_of_string blob, coq_of_string "Kani", validator))
    else None

(* --- SAW bridge --- *)

let run_saw ~script =
  let cmd = Printf.sprintf "saw %s 2>&1" script in
  match run_command_ok cmd with
  | None -> None
  | Some output ->
    let blob = Printf.sprintf "SAW:%s:verified" script in
    let validator = fun s ->
      if string_of_coq s = blob then Rack.True else Rack.False
    in
    Some (Certificate (coq_of_string blob, coq_of_string "SAW", validator))

(* --- Verus bridge --- *)

let run_verus ~file =
  let cmd = Printf.sprintf "verus %s 2>&1" file in
  match run_command_ok cmd with
  | None -> None
  | Some output ->
    if try let _ = Str.search_forward (Str.regexp_string "verification results:: verified") output 0 in true
       with Not_found -> false then
      let blob = Printf.sprintf "Verus:%s:verified" file in
      let validator = fun s ->
        if string_of_coq s = blob then Rack.True else Rack.False
      in
      Some (Certificate (coq_of_string blob, coq_of_string "Verus", validator))
    else None

(* --- Alloy bridge --- *)

let run_alloy ~model ~scope =
  let cmd = Printf.sprintf "java -jar alloy.jar -exec %s -scope %d 2>&1"
    model scope in
  match run_command_ok cmd with
  | None -> None
  | Some output ->
    if try let _ = Str.search_forward (Str.regexp_string "No counterexample found") output 0 in true
       with Not_found -> false then
      let blob = Printf.sprintf "Alloy:%s:scope=%d:no_cex" model scope in
      let validator = fun s ->
        if string_of_coq s = blob then Rack.True else Rack.False
      in
      Some (Certificate (coq_of_string blob, coq_of_string "Alloy", validator))
    else None

(* --- Generic tool runner --- *)

let run_tool ~tool ~cmd ~success_pattern =
  match run_command_ok cmd with
  | None -> None
  | Some output ->
    if try let _ = Str.search_forward (Str.regexp_string success_pattern) output 0 in true
       with Not_found -> false then
      let blob = Printf.sprintf "%s:%s:pass" tool cmd in
      let validator = fun s ->
        if string_of_coq s = blob then Rack.True else Rack.False
      in
      Some (Certificate (coq_of_string blob, coq_of_string tool, validator))
    else None
