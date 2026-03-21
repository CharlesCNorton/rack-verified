# RACK TODO

1. Fix `alloy_to_evidence` in `Bridge.v`: the blob string uses `ar_solver` in the scope position (`":scope=" ++ ar.(ar_solver)`) instead of the numeric `ar_scope`
2. Fix `rack_bench.ml`: the header claims "wall-clock time" but `Sys.time()` measures CPU time; replace with `Unix.gettimeofday` for wall-clock measurement
3. Fix `check_date_format` in `Diagnostics.v`: add leap year validation for February (currently permits day 29 unconditionally) and add year-range validation
4. Provide a `ProofTerm` evidence variant that passes `check_all_discharged` without requiring a `Some f` runtime checker, so that evidence whose correctness is guaranteed by the type system pre-extraction is not structurally rejected post-extraction
5. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needs well-founded induction on n/10 through `nat_to_string_go`)
6. Prove `parse_json_go` fuel sufficiency (needs mutual induction scheme for `parse_json_go`/`parse_array_elems`/`parse_object_kvs`)
7. Prove `render_parse_json_roundtrip` for `JNum` and `JNeg` (blocked on item 5)
8. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (blocked on item 6)
9. Prove `diagnose_structural ac = []` implies `structural_checks ac = true` (claimed in `Diagnostics.v:568` comment but not proved)
10. Prove BFS `check_acyclic` soundness: `check_acyclic ac = true -> Acyclic ac` (currently only `verify_topo_order` has a complete soundness proof)
11. Prove `check_annotations_compatible_sound` to completion in `ProductLine.v`
12. Prove `project_variant` preserves `WellFormed` when the family-wide `ProductLineCase` is well-formed and the variant is valid under the feature model (needs item 11)
13. Prove `compose_well_formed` and related theorems for `compose_cases_guarded`, not just `compose_cases`
14. Prove delta composition for the general case where both deltas contain `RemoveNode` and overlapping link changes
15. Prove `avl_insert` preserves `AVL_balanced`
16. Prove `avl_elements_sorted`: in-order traversal of an `AVL_ordered` tree is sorted (needs item 15)
17. Replace `find_node`'s O(n) linear scan with a balanced-map-backed O(log n) implementation (needs items 15–16)
18. Replace the unbalanced BST in `Incremental.v` with a balanced tree (AVL or red-black) with proved O(log n) lookup (needs items 15–16)
19. Prove `TraceGraph` JSON render/parse roundtrip (needs items 7–8)
20. Prove `AssuranceDelta` JSON render/parse roundtrip (needs items 7–8)
21. Prove `ProductLineCase` JSON render/parse roundtrip (needs items 7–8)
22. Prove that `hydrate_evidence` followed by `rebuild_claims` on a JSON-imported case produces an `AssuranceCase` whose `structural_checks` agree with the original pre-export case (needs items 7–8 and item 4)
23. Add an automated end-to-end pipeline (or tactic) that composes `parse_json`, `json_to_assurance_case`, `hydrate_evidence`, and `rebuild_claims` with a correctness certificate (needs item 22)
24. Add claim-level round-trip tests in the OCaml test suite (currently extracted tests never exercise `node_claim` because Prop fields are erased; needs item 4)
25. Add property-based tests for `compose_cases_guarded` (currently only `compose_cases` is tested; needs item 13)
26. Connect a real VST `semax_body` proof through the DeepSpec bridge as `ProofTerm` evidence with a complete `WellFormed` + `SupportTree` witness
27. Add `WellFormed` + `SupportTree` witnesses to deepspec/ files (VSTBridge, ITreeBridge, DeepSpecVST, DeepSpecITree, ConopsITree; requires `make deepspec` with VST/CompCert/ITree Docker image; needs item 26)
28. Prove that the extraction directives (`Extract Inductive nat => "int"`, etc.) preserve Rocq-side semantics for all values within OCaml's native integer range
29. Prove or validate that `sb_verify` instantiations used in production satisfy a cryptographic security specification (the Rocq proof only requires `sb_verify payload sig = true`)
30. Prove that Certificate validators used in Rocq-side proofs agree with their OCaml HMAC-SHA256 implementations post-extraction (currently tested against NIST vectors but not formally verified; needs items 28–29)
31. Update the README comparison table to note where RACK's own implementation is incomplete (product-line preservation, general delta composition) rather than marking competitors as "Not addressed" for features RACK has not fully proved
