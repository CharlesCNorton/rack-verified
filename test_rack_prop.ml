(* test_rack_prop.ml — property-based tests for the extracted RACK library.
   Self-contained random graph generator; no external dependencies.

   Build:
     ocamlfind ocamlopt -package str -linkpkg rack.ml test_rack_prop.ml -o test_rack_prop
   or:
     ocamlopt -I +str str.cmxa rack.ml test_rack_prop.ml -o test_rack_prop
*)

open Rack

(* --- Coq string helpers --- *)

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

(* --- Coq list helpers --- *)

let rec coq_list_of = function
  | [] -> Nil
  | x :: xs -> Cons (x, coq_list_of xs)

let rec list_of_coq = function
  | Nil -> []
  | Cons (x, rest) -> x :: list_of_coq rest

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
        node_evidence = Some (ProofTerm (coq_of_string "proof", None));
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
       let last_n = List.nth nodes (List.length nodes - 1) in
       let first_n = List.nth nodes 0 in
       let back_link = {
         link_kind = SupportedBy;
         link_from = last_n.node_id;
         link_to = first_n.node_id;
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
         node_evidence = Some (ProofTerm (coq_of_string "dup", None));
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

  (* Property 1: well-formed trees pass check_well_formed *)
  Printf.printf "\n[Property: well-formed trees pass]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    check (Printf.sprintf "wf_tree_%d" i) (check_well_formed ac)
  done;

  (* Property 2: well-formed trees pass structural_checks *)
  Printf.printf "[Property: well-formed trees pass structural_checks]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    check (Printf.sprintf "struct_tree_%d" i) (structural_checks ac)
  done;

  (* Property 3: check_well_formed = structural_checks *)
  Printf.printf "[Property: checkers agree]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    let cwf = check_well_formed ac in
    let sc = structural_checks ac in
    check (Printf.sprintf "agree_%d" i) (cwf = sc)
  done;

  (* Property 4: well-formed trees have support trees *)
  Printf.printf "[Property: well-formed trees have support trees]\n";
  for i = 0 to n_trials - 1 do
    let depth = 1 + rand_int 4 in
    let ac = gen_well_formed_tree depth in
    check (Printf.sprintf "support_%d" i)
      (check_support_tree ac ac.ac_top)
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
    check (Printf.sprintf "mutant_%d" i)
      (not (check_well_formed bad))
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
  for i = 0 to 49 do
    let ac1 = gen_well_formed_tree (1 + rand_int 3) in
    let ac2 = gen_well_formed_tree (1 + rand_int 3) in
    (* Ensure disjoint IDs by prefixing *)
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
    let ac1' = { ac_nodes = rename_nodes "A_" ac1.ac_nodes;
                 ac_links = rename_links "A_" ac1.ac_links;
                 ac_top = coq_of_string ("A_" ^ string_of_coq ac1.ac_top) } in
    let ac2' = { ac_nodes = rename_nodes "B_" ac2.ac_nodes;
                 ac_links = rename_links "B_" ac2.ac_links;
                 ac_top = coq_of_string ("B_" ^ string_of_coq ac2.ac_top) } in
    let composed = compose_cases ac1' ac2' ac1'.ac_top in
    check (Printf.sprintf "compose_%d" i) (check_well_formed composed)
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
