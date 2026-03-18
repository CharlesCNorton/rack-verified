(* test_rack.ml — exercise the extracted RACK library *)

open Rack

(* --- helpers --- *)

let string_of_coq_string s =
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

let coq_string_of_string s =
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

let assert_true label b =
  if b then Printf.printf "  PASS  %s\n" label
  else (Printf.printf "  FAIL  %s\n" label; exit 1)

let assert_false label b =
  if not b then Printf.printf "  PASS  %s\n" label
  else (Printf.printf "  FAIL  %s\n" label; exit 1)

(* --- build a small assurance case --- *)

let goal_node = {
  node_id = coq_string_of_string "G1";
  node_kind = Goal;
  node_claim_text = coq_string_of_string "2+2=4";
  node_evidence = None;
  node_metadata = Nil;
}

let solution_node = {
  node_id = coq_string_of_string "E1";
  node_kind = Solution;
  node_claim_text = coq_string_of_string "2+2=4";
  node_evidence = Some (ProofTerm (coq_string_of_string "proof", None));
  node_metadata = Nil;
}

let link1 = {
  link_kind = SupportedBy;
  link_from = coq_string_of_string "G1";
  link_to = coq_string_of_string "E1";
}

let ac = {
  ac_nodes = Cons (goal_node, Cons (solution_node, Nil));
  ac_links = Cons (link1, Nil);
  ac_top = coq_string_of_string "G1";
}

(* --- tests --- *)

let () =
  Printf.printf "=== RACK extracted OCaml tests ===\n";

  (* check_well_formed *)
  Printf.printf "\n[check_well_formed]\n";
  assert_true "well-formed simple case" (check_well_formed ac);

  (* structural_checks *)
  Printf.printf "\n[structural_checks]\n";
  assert_true "structural simple case" (structural_checks ac);

  (* check_support_tree *)
  Printf.printf "\n[check_support_tree]\n";
  assert_true "support tree simple case"
    (check_support_tree ac (coq_string_of_string "G1"));

  (* compute_support_witness *)
  Printf.printf "\n[compute_support_witness]\n";
  assert_true "witness exists"
    (match compute_support_witness ac (coq_string_of_string "G1") with
     | Some _ -> true | None -> false);

  (* find_node *)
  Printf.printf "\n[find_node / find_node_indexed]\n";
  let idx = build_node_index ac in
  assert_true "find_node G1"
    (match find_node ac (coq_string_of_string "G1") with
     | Some _ -> true | None -> false);
  assert_true "find_node_indexed G1"
    (match find_node_indexed idx (coq_string_of_string "G1") with
     | Some _ -> true | None -> false);

  (* evidence_label *)
  Printf.printf "\n[evidence_label]\n";
  let lbl = evidence_label (ProofTerm (coq_string_of_string "my_thm", None)) in
  assert_true "label is my_thm"
    (string_of_coq_string lbl = "my_thm");

  (* evidence_runtime_check *)
  Printf.printf "\n[evidence_runtime_check]\n";
  assert_true "ProofTerm None -> true"
    (evidence_runtime_check (ProofTerm (coq_string_of_string "x", None)));
  assert_true "ProofTerm Some -> calls thunk"
    (evidence_runtime_check (ProofTerm (coq_string_of_string "x",
      Some (fun () -> true))));
  let v = fun s -> s = coq_string_of_string "ok" in
  assert_true "Certificate valid"
    (evidence_runtime_check (Certificate (coq_string_of_string "ok",
      coq_string_of_string "test-tool", v)));

  (* evidence_tool *)
  Printf.printf "\n[evidence_tool]\n";
  let tool = evidence_tool (Certificate (coq_string_of_string "blob",
    coq_string_of_string "CBMC", fun _ -> true)) in
  assert_true "tool is CBMC"
    (string_of_coq_string tool = "CBMC");

  (* JSON export *)
  Printf.printf "\n[render_json]\n";
  let json_str = render_assurance_case ac in
  let s = string_of_coq_string json_str in
  assert_true "JSON non-empty" (String.length s > 0);
  assert_true "JSON has G1"
    (try let _ = Str.search_forward (Str.regexp_string "G1") s 0 in true
     with Not_found -> false);

  (* JSON round-trip *)
  Printf.printf "\n[parse_json round-trip]\n";
  (match parse_json json_str with
   | Some j ->
     assert_true "parse_json succeeds" true;
     (match json_to_assurance_case j with
      | Some ac2 ->
        assert_true "json_to_assurance_case succeeds" true;
        let top = string_of_coq_string ac2.ac_top in
        assert_true ("round-trip top = G1, got " ^ top) (top = "G1")
      | None ->
        assert_true "json_to_assurance_case succeeds" false)
   | None ->
     assert_true "parse_json succeeds" false);

  (* DOT export *)
  Printf.printf "\n[render_dot]\n";
  let dot_str = render_dot ac in
  let dot_s = string_of_coq_string dot_str in
  assert_true "DOT non-empty" (String.length dot_s > 0);

  (* DOT with options *)
  Printf.printf "\n[render_dot_with_options]\n";
  let dot_opts = render_dot_with_options default_dot_options ac in
  assert_true "DOT opts non-empty" (String.length (string_of_coq_string dot_opts) > 0);

  (* SACM export *)
  Printf.printf "\n[render_sacm]\n";
  let sacm_str = render_sacm ac in
  let sacm_s = string_of_coq_string sacm_str in
  assert_true "SACM non-empty" (String.length sacm_s > 0);
  assert_true "SACM has xml"
    (try let _ = Str.search_forward (Str.regexp_string "xml") sacm_s 0 in true
     with Not_found -> false);

  (* compose_cases *)
  Printf.printf "\n[compose_cases]\n";
  let parent_goal_node = {
    node_id = coq_string_of_string "G-parent";
    node_kind = Goal;
    node_claim_text = coq_string_of_string "parent";
    node_evidence = None;
    node_metadata = Nil;
  } in
  let parent = {
    ac_nodes = Cons (parent_goal_node, Nil);
    ac_links = Nil;
    ac_top = coq_string_of_string "G-parent";
  } in
  let composed = compose_cases parent ac (coq_string_of_string "G-parent") in
  assert_true "composed well-formed" (check_well_formed composed);
  assert_true "composed structural" (structural_checks composed);

  (* diagnose_all *)
  Printf.printf "\n[diagnose_all]\n";
  (match diagnose_all ac with
   | Nil -> assert_true "no errors for valid case" true
   | _ -> assert_true "no errors for valid case" false);

  (* check_node / check_link *)
  Printf.printf "\n[check_node / check_link]\n";
  assert_true "check_node G1"
    (check_node ac (coq_string_of_string "G1"));
  assert_true "check_link"
    (check_link ac link1);

  (* streaming export *)
  Printf.printf "\n[streaming]\n";
  (match stream_json_lines ac with
   | Nil -> assert_true "stream non-empty" false
   | _ -> assert_true "stream non-empty" true);
  (match stream_dot_lines ac with
   | Nil -> assert_true "dot stream non-empty" false
   | _ -> assert_true "dot stream non-empty" true);

  (* metadata *)
  Printf.printf "\n[metadata]\n";
  let md_node = {
    node_id = coq_string_of_string "test";
    node_kind = Solution;
    node_claim_text = coq_string_of_string "test";
    node_evidence = None;
    node_metadata = Cons (Pair (coq_string_of_string "key",
                                coq_string_of_string "val"), Nil);
  } in
  (match find_metadata (coq_string_of_string "key") md_node.node_metadata with
   | Some v -> assert_true "find_metadata"
     (string_of_coq_string v = "val")
   | None -> assert_true "find_metadata" false);

  (* negative: bad case *)
  Printf.printf "\n[negative cases]\n";
  let bad = {
    ac_nodes = Cons (goal_node, Nil);
    ac_links = Cons (link1, Nil);
    ac_top = coq_string_of_string "G1";
  } in
  assert_false "dangling link rejected" (check_well_formed bad);
  (match diagnose_all bad with
   | Nil -> assert_true "diagnose finds errors" false
   | _ -> assert_true "diagnose finds errors" true);

  Printf.printf "\n=== All tests passed ===\n"
