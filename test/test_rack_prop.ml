(* test_rack_prop.ml — property-based tests for the extracted RACK library.
   Self-contained random graph generator; no external dependencies.

   Strategy:
   - Generate well-formed tree-shaped assurance cases (depth 1-4,
     1-3 children per internal node, Solution leaves with valid
     ProofTerm evidence).
   - Test 8 properties, 100 trials each (800 total test executions):
     1. Well-formed trees pass check_wf_extended.
     2. Well-formed trees pass structural_checks.
     3. check_wf_extended and structural_checks agree.
     4. Well-formed trees have support trees (check_support_tree).
     5. diagnose_all returns [] for well-formed trees.
     6. Random mutations (5 kinds) break well-formedness.
     7. JSON render/parse round-trips preserve the top ID.
     8. Composition of disjoint well-formed trees is well-formed.
   - Mutation kinds: RemoveEvidence, AddCycle, DanglingLink,
     DuplicateId, WrongTop.
   - ID disjointness for composition uses trial-specific numeric
     prefixes (P0_, P1_, ...) to avoid collisions.
   - Coverage: exercises structural_checks, check_wf_extended,
     check_support_tree, diagnose_all, compose_cases,
     render_assurance_case, parse_json, json_to_assurance_case,
     and all five mutation detection paths.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml test_rack_prop.ml -o test_rack_prop
   or:
     ocamlopt -I +str str.cmxa rack.ml rack_util.ml test_rack_prop.ml -o test_rack_prop
*)

open Rack
open Rack_util

(* --- Random graph generator --- *)

let rng = Random.State.make_self_init ()

let rand_int n = Random.State.int rng n

let rand_node_id i = Printf.sprintf "N%d" i

let rand_kind () =
  match rand_int 6 with
  | 0 -> Goal | 1 -> Strategy | 2 -> Solution
  | 3 -> Context | 4 -> Assumption | _ -> Justification

(* Generate a well-formed tree-shaped assurance case:
   - Single Goal at root
   - Each Goal/Strategy has 1-3 children
   - Leaves are Solutions with valid evidence
   - Depth bounded *)
let gen_well_formed_tree max_depth =
  let counter = ref 0 in
  let nodes = ref [] in
  let links = ref [] in
  let fresh () =
    let i = !counter in
    incr counter;
    rand_node_id i
  in
  let rec gen depth =
    let id = fresh () in
    if depth <= 0 then begin
      (* Solution leaf *)
      let n = {
        node_id = coq_of_string id;
        node_kind = Solution;
        node_claim_text = coq_of_string (Printf.sprintf "claim_%s" id);
        node_evidence = Some (ProofTerm (coq_of_string "proof", Some (fun _ -> True)));
        node_metadata = Nil;
      } in
      nodes := n :: !nodes;
      id
    end else begin
      let kind = if depth = max_depth then Goal
                 else if rand_int 3 = 0 then Goal
                 else Strategy in
      let n_children = 1 + rand_int 3 in
      let children = List.init n_children (fun _ -> gen (depth - 1)) in
      let n = {
        node_id = coq_of_string id;
        node_kind = kind;
        node_claim_text = coq_of_string (Printf.sprintf "claim_%s" id);
        node_evidence = None;
        node_metadata = Nil;
      } in
      nodes := n :: !nodes;
      List.iter (fun child_id ->
        links := {
          link_kind = SupportedBy;
          link_from = coq_of_string id;
          link_to = coq_of_string child_id;
        } :: !links
      ) children;
      id
    end
  in
  let top_id = gen max_depth in
  {
    ac_nodes = coq_list_of (List.rev !nodes);
    ac_links = coq_list_of (List.rev !links);
    ac_top = coq_of_string top_id;
  }

(* Mutate an assurance case to make it invalid *)
type mutation =
  | RemoveEvidence    (* strip evidence from a random Solution *)
  | AddCycle          (* add a back-edge creating a cycle *)
  | DanglingLink      (* add a link to a nonexistent node *)
  | DuplicateId       (* duplicate a node ID *)
  | WrongTop          (* set top to a non-Goal node *)

let mutate ac mut =
  let nodes = list_of_coq ac.ac_nodes in
  let links = list_of_coq ac.ac_links in
  match mut with
  | RemoveEvidence ->
    let solutions = List.filter (fun n ->
      match n.node_kind with Solution -> true | _ -> false) nodes in
    (match solutions with
     | [] -> ac
     | _ ->
       let target = List.nth solutions (rand_int (List.length solutions)) in
       let nodes' = List.map (fun n ->
         if string_of_coq n.node_id = string_of_coq target.node_id then
           { n with node_evidence = None }
         else n) nodes in
       { ac with ac_nodes = coq_list_of nodes' })
  | AddCycle ->
    (match nodes with
     | [] | [_] -> ac
     | _ ->
       (* first_n is a leaf, last_n is the root after List.rev.
          Back-edge must go FROM a leaf TO the root to create a cycle. *)
       let leaf = List.nth nodes 0 in
       let root = List.nth nodes (List.length nodes - 1) in
       let back_link = {
         link_kind = SupportedBy;
         link_from = leaf.node_id;
         link_to = root.node_id;
       } in
       { ac with ac_links = coq_list_of (links @ [back_link]) })
  | DanglingLink ->
    let dangle = {
      link_kind = SupportedBy;
      link_from = (List.hd nodes).node_id;
      link_to = coq_of_string "NONEXISTENT";
    } in
    { ac with ac_links = coq_list_of (links @ [dangle]) }
  | DuplicateId ->
    (match nodes with
     | [] -> ac
     | n :: _ ->
       let dup = { n with
         node_kind = Solution;
         node_claim_text = coq_of_string "duplicate";
         node_evidence = Some (ProofTerm (coq_of_string "dup", Some (fun _ -> True)));
       } in
       { ac with ac_nodes = coq_list_of (nodes @ [dup]) })
  | WrongTop ->
    let non_goals = List.filter (fun n ->
      match n.node_kind with Goal -> false | _ -> true) nodes in
    (match non_goals with
     | [] -> ac
     | _ ->
       let target = List.nth non_goals (rand_int (List.length non_goals)) in
       { ac with ac_top = target.node_id })

(* --- Test runner --- *)

let passed = ref 0
let failed = ref 0
let total = ref 0

let check label condition =
  incr total;
  if condition then
    incr passed
  else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" label
  end

let () =
  Printf.printf "=== RACK property-based tests ===\n";
  let n_trials = 100 in

  (* Property 1: well-formed trees pass check_wf_extended *)
  Printf.printf "\n[Property: well-formed trees pass]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    check (Printf.sprintf "wf_tree_%d" i) (coq_bool_to_bool (check_wf_extended ac))
  done;

  (* Property 2: well-formed trees pass structural_checks *)
  Printf.printf "[Property: well-formed trees pass structural_checks]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    check (Printf.sprintf "struct_tree_%d" i) (coq_bool_to_bool (structural_checks ac))
  done;

  (* Property 3: check_wf_extended = structural_checks *)
  Printf.printf "[Property: checkers agree]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    let cwf = coq_bool_to_bool (check_wf_extended ac) in
    let sc = coq_bool_to_bool (structural_checks ac) in
    check (Printf.sprintf "agree_%d" i) (cwf = sc)
  done;

  (* Property 4: well-formed trees have support trees *)
  Printf.printf "[Property: well-formed trees have support trees]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    check (Printf.sprintf "support_%d" i)
      (coq_bool_to_bool (check_support_tree ac ac.ac_top))
  done;

  (* Property 5: diagnose_all returns [] for well-formed cases *)
  Printf.printf "[Property: no diagnostics for well-formed cases]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    check (Printf.sprintf "diag_%d" i)
      (list_of_coq (diagnose_all ac) = [])
  done;

  (* Property 6: mutations break well-formedness *)
  Printf.printf "[Property: mutations break well-formedness]\n";
  let mutations = [| RemoveEvidence; AddCycle; DanglingLink;
                     DuplicateId; WrongTop |] in
  for i = 0 to n_trials - 1 do
    let depth = 2 + rand_int 3 in
    let ac = gen_well_formed_tree depth in
    let mut = mutations.(rand_int (Array.length mutations)) in
    let bad = mutate ac mut in
    let wf_bad = coq_bool_to_bool (check_wf_extended bad) in
    check (Printf.sprintf "mutant_%d" i) (not wf_bad)
  done;

  (* Property 7: JSON round-trip preserves top ID *)
  Printf.printf "[Property: JSON round-trip preserves top]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 3 in
    let ac = gen_well_formed_tree depth in
    let json_str = render_assurance_case ac in
    let ok = match parse_json json_str with
      | Some j ->
        (match json_to_assurance_case j with
         | Some ac2 ->
           string_of_coq ac2.ac_top = string_of_coq ac.ac_top
         | None -> false)
      | None -> false
    in
    check (Printf.sprintf "roundtrip_%d" i) ok
  done;

  (* Property 8: compose preserves well-formedness *)
  Printf.printf "[Property: composition preserves well-formedness]\n";
  for i = 0 to n_trials - 1 do
    let ac1 = gen_well_formed_tree (1 + rand_int 3) in
    let ac2 = gen_well_formed_tree (1 + rand_int 3) in
    (* Ensure disjoint IDs using trial-specific prefixes *)
    let pfx1 = Printf.sprintf "P%d_" (i * 2) in
    let pfx2 = Printf.sprintf "P%d_" (i * 2 + 1) in
    let rename_nodes prefix ns =
      list_of_coq ns |> List.map (fun n ->
        { n with node_id = coq_of_string (prefix ^ string_of_coq n.node_id) })
      |> coq_list_of
    in
    let rename_links prefix ls =
      list_of_coq ls |> List.map (fun l ->
        { l with
          link_from = coq_of_string (prefix ^ string_of_coq l.link_from);
          link_to = coq_of_string (prefix ^ string_of_coq l.link_to) })
      |> coq_list_of
    in
    let ac1' = { ac_nodes = rename_nodes pfx1 ac1.ac_nodes;
                 ac_links = rename_links pfx1 ac1.ac_links;
                 ac_top = coq_of_string (pfx1 ^ string_of_coq ac1.ac_top) } in
    let ac2' = { ac_nodes = rename_nodes pfx2 ac2.ac_nodes;
                 ac_links = rename_links pfx2 ac2.ac_links;
                 ac_top = coq_of_string (pfx2 ^ string_of_coq ac2.ac_top) } in
    let composed = compose_cases ac1' ac2' ac1'.ac_top in
    check (Printf.sprintf "compose_%d" i) (coq_bool_to_bool (check_wf_extended composed))
  done;

  (* Summary *)
  Printf.printf "\n=== Results: %d/%d passed ===" !passed !total;
  if !failed > 0 then begin
    Printf.printf " (%d FAILED)\n" !failed;
    exit 1
  end else begin
    Printf.printf "\n";
    exit 0
  end
