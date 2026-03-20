(* rack_bench.ml — Benchmark harness for extracted RACK operations.
   Measures wall-clock time for structural_checks, structural_checks_fast,
   topo_sort, check_support_tree, render_assurance_case, parse_json,
   and render_dot at multiple graph sizes.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml rack_bench.ml -o rack_bench
*)

open Rack
open Rack_util

let time_us f =
  let t0 = Sys.time () in
  let result = f () in
  let dt = (Sys.time () -. t0) *. 1_000_000.0 in
  (result, int_of_float dt)

(* Generate a balanced binary tree of depth d.
   Nodes: 2^(d+1) - 1.  Every internal node has 2 children. *)
let gen_tree n =
  let counter = ref 0 in
  let nodes = ref [] in
  let links = ref [] in
  let fresh () = let i = !counter in incr counter; Printf.sprintf "N%d" i in
  let rec go depth =
    let id = fresh () in
    if depth <= 0 then begin
      nodes := { node_id = coq_of_string id; node_kind = Solution;
        node_claim_text = coq_of_string id;
        node_evidence = Some (ProofTerm (coq_of_string "b", Some (fun _ -> True)));
        node_metadata = Nil } :: !nodes; id
    end else begin
      let kind = if !counter <= 1 then Goal else Strategy in
      let c1 = go (depth - 1) in
      let c2 = go (depth - 1) in
      nodes := { node_id = coq_of_string id; node_kind = kind;
        node_claim_text = coq_of_string id;
        node_evidence = None; node_metadata = Nil } :: !nodes;
      links := { link_kind = SupportedBy; link_from = coq_of_string id;
        link_to = coq_of_string c1 } :: !links;
      links := { link_kind = SupportedBy; link_from = coq_of_string id;
        link_to = coq_of_string c2 } :: !links;
      id
    end
  in
  (* pick depth to get at least n nodes *)
  let depth = ref 0 in
  while (1 lsl (!depth + 1)) - 1 < n do incr depth done;
  let top = go !depth in
  { ac_nodes = coq_list_of (List.rev !nodes);
    ac_links = coq_list_of (List.rev !links);
    ac_top = coq_of_string top }

let bench_size target =
  let ac = gen_tree target in
  let n_nodes = List.length (list_of_coq ac.ac_nodes) in
  let n_links = List.length (list_of_coq ac.ac_links) in
  let (_, check_us) = time_us (fun () -> structural_checks ac) in
  let (_, fast_us) = time_us (fun () -> structural_checks_fast ac) in
  let (_, topo_us) = time_us (fun () -> topo_sort ac) in
  let (_, support_us) = time_us (fun () ->
    check_support_tree ac ac.ac_top) in
  let json_str = render_assurance_case ac in
  let (_, json_us) = time_us (fun () -> render_assurance_case ac) in
  let (_, parse_us) = time_us (fun () -> parse_json json_str) in
  let (_, dot_us) = time_us (fun () -> render_dot ac) in
  Printf.printf "| %5d | %5d | %5d | %8d | %8d | %8d | %8d | %8d | %8d | %8d |\n"
    target n_nodes n_links check_us fast_us topo_us support_us json_us parse_us dot_us

let () =
  Printf.printf "| Target| Nodes | Links | Check us | Fast  us | Topo  us | Supp  us | JSON  us | Parse us | DOT   us |\n";
  Printf.printf "|-------|-------|-------|----------|----------|----------|----------|----------|----------|----------|\n";
  List.iter bench_size [10; 50; 100; 500; 1000]
