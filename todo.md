# RACK TODO

1. Remove or deprecate `check_discharged`; keep only `check_all_discharged` and route all call sites to it
2. Remove or gate `check_identity_entailment` behind a deprecation; make `check_identity_entailment_fp` the only public API for identity entailment
3. Document in the README that `prove_well_formed_auto` only handles cases where `vm_compute; tauto` solves the entailment obligation, and that non-trivial entailments require manual proof
4. Prove `parse_json_go` fuel sufficiency: `string_length s` always provides enough fuel for any valid JSON string `s`
5. Prove `nat_to_string`/`parse_nat_chars` roundtrip
6. Prove `parse_string_chars` fuel monotonicity
7. Prove `render_parse_json_roundtrip` for `JStr` by integrating `escape_unescape_roundtrip` with the `parse_json_go` wrapper using fuel monotonicity
8. Prove `render_parse_json_roundtrip` for `JNum` and `JNeg` using the nat roundtrip
9. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` by mutual induction over the sub-value roundtrips
10. Prove `TraceGraph` JSON render/parse roundtrip
11. Prove `AssuranceDelta` JSON render/parse roundtrip
12. Prove `ProductLineCase` JSON render/parse roundtrip
13. Prove `avl_insert_find`: inserting then finding with the same key returns the inserted value
14. Prove `avl_insert_find_other`: inserting does not disturb lookups for other keys
15. Prove `avl_insert` preserves `AVL_balanced`
16. Prove `avl_elements_sorted`: in-order traversal of an `AVL_ordered` tree is sorted
17. Prove `avl_insert_find_via_elements`: connect `avl_find` to the element list for the full refinement chain
18. Wire BST or AVL index into `structural_checks` so the proved path uses O(log n) lookups instead of linear `find_node`
19. Add performance benchmarks for 100, 1000, and 10000 node cases covering `structural_checks`, `topo_sort`, `check_support_tree`, and JSON render/parse
20. Prove `compose_well_formed` and related theorems for `compose_cases_guarded`, not just `compose_cases`
21. Prove `project_variant` preserves `WellFormed` when the family-wide `ProductLineCase` is well-formed and the variant is valid under the feature model
22. Prove `compile_document` produces a structurally valid assurance case for any well-formed `ConopsDocument`
23. Prove delta composition for the general case where both deltas may contain `RemoveNode` and overlapping link changes, or prove a tight characterization of when composition fails
24. Add a typed wrapper or pre-extraction static check that prevents constructing a `ProofTerm` whose `Prop` argument differs from the `node_claim` of the node it is attached to
25. Connect a real VST `semax_body` proof through the DeepSpec bridge to a complete `WellFormed` + `SupportTree` witness in a single end-to-end example
26. Add nonce or sequence number fields to `SignedBlob` and `KeyedSignedBlob` for replay protection
27. Add key rotation and revocation support to `KeyedSignedBlob`
28. Formally verify the OCaml SHA-256 and HMAC-SHA256 implementation against FIPS 180-4, or replace it with a binding to a verified library
29. Prove that the extraction directives (`Extract Inductive nat => "int"`, etc.) preserve Rocq-side semantics for all values within OCaml's native integer range
