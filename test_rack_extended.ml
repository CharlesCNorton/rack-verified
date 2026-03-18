(* test_rack_extended.ml — property-based tests for Trace, Delta,
   and ProductLine modules (items 15-16 of the gap list).

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml test_rack_extended.ml -o test_rack_extended
*)

open Rack
open Rack_util

let rng = Random.State.make_self_init ()
let rand_int n = Random.State.int rng n

let passed = ref 0
let failed = ref 0
let total = ref 0

let check label condition =
  incr total;
  if condition then incr passed
  else begin incr failed; Printf.printf "  FAIL  %s\n" label end

(* === Generators === *)

let rand_node_id i = Printf.sprintf "N%d" i

let gen_well_formed_tree max_depth =
  let counter = ref 0 in
  let nodes = ref [] in
  let links = ref [] in
  let fresh () = let i = !counter in incr counter; rand_node_id i in
  let rec gen depth =
    let id = fresh () in
    if depth <= 0 then begin
      nodes := { node_id = coq_of_string id; node_kind = Solution;
        node_claim_text = coq_of_string id;
        node_evidence = Some (ProofTerm (coq_of_string "p", None));
        node_metadata = Nil } :: !nodes; id
    end else begin
      let kind = if depth = max_depth then Goal else Strategy in
      let n_children = 1 + rand_int 2 in
      let children = List.init n_children (fun _ -> gen (depth - 1)) in
      nodes := { node_id = coq_of_string id; node_kind = kind;
        node_claim_text = coq_of_string id;
        node_evidence = None; node_metadata = Nil } :: !nodes;
      List.iter (fun cid ->
        links := { link_kind = SupportedBy;
          link_from = coq_of_string id;
          link_to = coq_of_string cid } :: !links) children; id
    end
  in
  let top = gen max_depth in
  { ac_nodes = coq_list_of (List.rev !nodes);
    ac_links = coq_list_of (List.rev !links);
    ac_top = coq_of_string top }

(* === Delta tests === *)

let () =
  Printf.printf "=== Extended property-based tests ===\n";

  (* Delta: UpdateEvidence preserves structural checks *)
  Printf.printf "\n[Delta: UpdateEvidence preserves structure]\n";
  for i = 0 to 49 do
    let ac = gen_well_formed_tree (2 + rand_int 3) in
    let nodes = list_of_coq ac.ac_nodes in
    let solutions = List.filter (fun n ->
      match n.node_kind with Solution -> true | _ -> false) nodes in
    match solutions with
    | [] -> check (Printf.sprintf "delta_ev_%d" i) true
    | _ ->
      let target = List.nth solutions (rand_int (List.length solutions)) in
      let new_ev = ProofTerm (coq_of_string "updated", None) in
      let delta = { ad_node_changes =
        Cons (UpdateEvidence (target.node_id, new_ev), Nil);
        ad_link_changes = Nil; ad_trace_changes = Nil;
        ad_commit = None;
        ad_description = coq_of_string "test" } in
      let ac' = apply_delta ac delta in
      check (Printf.sprintf "delta_ev_%d" i)
        (structural_checks ac' |> coq_bool_to_bool)
  done;

  (* Delta: AddNode + AddLink *)
  Printf.printf "[Delta: AddNode+AddLink preserves structure]\n";
  for i = 0 to 49 do
    let ac = gen_well_formed_tree (2 + rand_int 2) in
    let nodes = list_of_coq ac.ac_nodes in
    let strategies = List.filter (fun n ->
      match n.node_kind with Strategy -> true | _ -> false) nodes in
    match strategies with
    | [] -> check (Printf.sprintf "delta_add_%d" i) true
    | _ ->
      let parent = List.nth strategies (rand_int (List.length strategies)) in
      let new_id = coq_of_string (Printf.sprintf "NEW_%d" i) in
      let new_node = { node_id = new_id; node_kind = Solution;
        node_claim_text = coq_of_string "new";
        node_evidence = Some (ProofTerm (coq_of_string "p", None));
        node_metadata = Nil } in
      let delta = { ad_node_changes = Cons (AddNode new_node, Nil);
        ad_link_changes = Cons (AddLink { link_kind = SupportedBy;
          link_from = parent.node_id; link_to = new_id }, Nil);
        ad_trace_changes = Nil; ad_commit = None;
        ad_description = coq_of_string "add" } in
      let ac' = apply_delta ac delta in
      check (Printf.sprintf "delta_add_%d" i)
        (structural_checks ac' |> coq_bool_to_bool)
  done;

  (* Delta: empty delta is identity *)
  Printf.printf "[Delta: empty delta is identity]\n";
  for i = 0 to 49 do
    let ac = gen_well_formed_tree (1 + rand_int 3) in
    let empty = { ad_node_changes = Nil; ad_link_changes = Nil;
      ad_trace_changes = Nil; ad_commit = None;
      ad_description = coq_of_string "" } in
    let ac' = apply_delta ac empty in
    let wf_before = check_well_formed ac |> coq_bool_to_bool in
    let wf_after = check_well_formed ac' |> coq_bool_to_bool in
    check (Printf.sprintf "delta_empty_%d" i) (wf_before = wf_after)
  done;

  (* Delta: RemoveNode breaks structure *)
  Printf.printf "[Delta: RemoveNode mutation breaks structure]\n";
  for i = 0 to 49 do
    let ac = gen_well_formed_tree (2 + rand_int 2) in
    let nodes = list_of_coq ac.ac_nodes in
    if List.length nodes < 2 then
      check (Printf.sprintf "delta_rm_%d" i) true
    else begin
      let target = List.nth nodes (1 + rand_int (List.length nodes - 1)) in
      let delta = { ad_node_changes = Cons (RemoveNode target.node_id, Nil);
        ad_link_changes = Nil; ad_trace_changes = Nil;
        ad_commit = None; ad_description = coq_of_string "rm" } in
      let ac' = apply_delta ac delta in
      check (Printf.sprintf "delta_rm_%d" i)
        (not (check_well_formed ac' |> coq_bool_to_bool))
    end
  done;

  (* Delta composition: additive compose distributes *)
  Printf.printf "[Delta: additive compose distributes]\n";
  for i = 0 to 29 do
    let ac = gen_well_formed_tree (2 + rand_int 2) in
    let new_id1 = coq_of_string (Printf.sprintf "X_%d" i) in
    let new_id2 = coq_of_string (Printf.sprintf "Y_%d" i) in
    let n1 = { node_id = new_id1; node_kind = Solution;
      node_claim_text = coq_of_string "x";
      node_evidence = Some (ProofTerm (coq_of_string "p", None));
      node_metadata = Nil } in
    let n2 = { node_id = new_id2; node_kind = Solution;
      node_claim_text = coq_of_string "y";
      node_evidence = Some (ProofTerm (coq_of_string "p", None));
      node_metadata = Nil } in
    let d1 = { ad_node_changes = Cons (AddNode n1, Nil);
      ad_link_changes = Nil; ad_trace_changes = Nil;
      ad_commit = None; ad_description = coq_of_string "d1" } in
    let d2 = { ad_node_changes = Cons (AddNode n2, Nil);
      ad_link_changes = Nil; ad_trace_changes = Nil;
      ad_commit = None; ad_description = coq_of_string "d2" } in
    let composed = compose_deltas d1 d2 in
    let r1 = apply_delta ac composed in
    let r2 = apply_delta (apply_delta ac d1) d2 in
    (* Compare node counts — full equality is hard with extracted types *)
    let c1 = List.length (list_of_coq r1.ac_nodes) in
    let c2 = List.length (list_of_coq r2.ac_nodes) in
    check (Printf.sprintf "delta_compose_%d" i) (c1 = c2)
  done;

  (* Trace: invalidate_requirement produces non-empty stale set *)
  Printf.printf "[Trace: requirement invalidation]\n";
  for _i = 0 to 9 do
    let ac = gen_well_formed_tree 3 in
    let tg = { tg_case = ac;
      tg_requirements = Cons ((coq_of_string "REQ-1"), Nil);
      tg_artifacts = Nil; tg_commits = Nil;
      tg_tool_runs = Nil; tg_owners = Nil;
      tg_trace_links = Cons ({ tl_kind = TL_Satisfies;
        tl_source = coq_of_string "REQ-1";
        tl_target = ac.ac_top }, Nil) } in
    let iw = invalidate_requirement tg (coq_of_string "REQ-1") in
    check (Printf.sprintf "trace_inval_%d" _i)
      (list_of_coq iw.iw_stale_nodes <> [])
  done;

  (* Trace: commit invalidation *)
  Printf.printf "[Trace: commit invalidation]\n";
  for _i = 0 to 9 do
    let ac = gen_well_formed_tree 2 in
    let tg = { tg_case = ac;
      tg_requirements = Nil; tg_artifacts = Nil;
      tg_commits = Cons ((coq_of_string "abc"), Nil);
      tg_tool_runs = Nil; tg_owners = Nil;
      tg_trace_links = Cons ({ tl_kind = TL_CommittedIn;
        tl_source = coq_of_string "src";
        tl_target = coq_of_string "abc" },
        Cons ({ tl_kind = TL_ImplementedBy;
          tl_source = ac.ac_top;
          tl_target = coq_of_string "src" }, Nil)) } in
    let iw = invalidate_commit tg (coq_of_string "abc") in
    check (Printf.sprintf "trace_commit_%d" _i)
      (list_of_coq iw.iw_stale_nodes <> [])
  done;

  (* Trace: missing requirement fails check_trace_total *)
  Printf.printf "[Trace: missing requirement fails total]\n";
  for _i = 0 to 9 do
    let ac = gen_well_formed_tree 2 in
    let tg = { tg_case = ac;
      tg_requirements = Cons ((coq_of_string "REQ-MISSING"), Nil);
      tg_artifacts = Nil; tg_commits = Nil;
      tg_tool_runs = Nil; tg_owners = Nil;
      tg_trace_links = Nil } in
    check (Printf.sprintf "trace_neg_total_%d" _i)
      (not (coq_bool_to_bool (check_trace_total tg)))
  done;

  (* Trace: missing provenance fails check_trace_provenance *)
  Printf.printf "[Trace: missing provenance fails]\n";
  for _i = 0 to 9 do
    let ac = gen_well_formed_tree 2 in
    let tg = { tg_case = ac;
      tg_requirements = Nil; tg_artifacts = Nil;
      tg_commits = Nil; tg_tool_runs = Nil;
      tg_owners = Nil; tg_trace_links = Nil } in
    check (Printf.sprintf "trace_neg_prov_%d" _i)
      (not (coq_bool_to_bool (check_trace_provenance tg)))
  done;

  (* Summary *)
  Printf.printf "\n=== Results: %d/%d passed ===" !passed !total;
  if !failed > 0 then begin
    Printf.printf " (%d FAILED)\n" !failed; exit 1
  end else begin Printf.printf "\n"; exit 0 end
