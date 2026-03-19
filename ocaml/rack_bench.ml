(* rack_bench.ml — Benchmark harness for extracted RACK operations.
   Measures wall-clock time for structural_checks, check_support_tree,
   render_assurance_case, and render_dot at multiple graph sizes.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml rack_bench.ml -o rack_bench
*)

open Rack
open Rack_util

let time_ms f =
  let t0 = Sys.time () in
  let result = f () in
  let dt = (Sys.time () -. t0) *. 1000.0 in
  (result, int_of_float dt)

let gen_chain n =
  let rec go i nodes links =
    if i = 0 then
      let sol = { node_id = coq_of_string "N0"; node_kind = Solution;
        node_claim_text = coq_of_string "leaf";
        node_evidence = Some (ProofTerm (coq_of_string "bench", None));
        node_metadata = Nil } in
      let top = match nodes with
        | n :: _ -> string_of_coq n.node_id
        | [] -> "N0" in
      { ac_nodes = coq_list_of (sol :: nodes);
        ac_links = coq_list_of links;
        ac_top = coq_of_string top }
    else
      let id = Printf.sprintf "N%d" i in
      let child_id = if i = 1 then "N0" else Printf.sprintf "N%d" (i - 1) in
      let kind = if i = n then Goal else Strategy in
      let node = { node_id = coq_of_string id; node_kind = kind;
        node_claim_text = coq_of_string id;
        node_evidence = None; node_metadata = Nil } in
      let link = { link_kind = SupportedBy;
        link_from = coq_of_string id;
        link_to = coq_of_string child_id } in
      go (i - 1) (node :: nodes) (link :: links)
  in
  go n [] []

let bench_size n =
  let ac = gen_chain n in
  let n_nodes = List.length (list_of_coq ac.ac_nodes) in
  let n_links = List.length (list_of_coq ac.ac_links) in
  let (_, check_ms) = time_ms (fun () -> structural_checks ac) in
  let (_, support_ms) = time_ms (fun () ->
    check_support_tree ac ac.ac_top) in
  let (_, json_ms) = time_ms (fun () -> render_assurance_case ac) in
  let (_, dot_ms) = time_ms (fun () -> render_dot ac) in
  Printf.printf "| %4d | %4d | %4d | %6d ms | %6d ms | %6d ms | %6d ms |\n"
    n n_nodes n_links check_ms support_ms json_ms dot_ms

let () =
  Printf.printf "| Size | Nodes | Links | Check    | Support  | JSON     | DOT      |\n";
  Printf.printf "|------|-------|-------|----------|----------|----------|----------|\n";
  List.iter bench_size [10; 25; 50; 100; 250; 500; 1000]
