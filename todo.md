# RACK TODO

1. Replace the `Some (fun _ => true)` re-checker convention on `ProofTerm` evidence with a mechanism that preserves validity after extraction (the Rocq-side `P = node_claim` guarantee is erased; the current thunk is a trust assumption, not a verified check)
2. Prove `avl_insert_find`: inserting then finding with the same key returns the inserted value
3. Prove `avl_insert_find_other`: inserting does not disturb lookups for other keys
4. Prove `avl_insert` preserves `AVL_balanced`
5. Prove `avl_elements_sorted`: in-order traversal of an `AVL_ordered` tree is sorted
6. Prove `avl_insert_find_via_elements`: connect `avl_find` to the element list for the full refinement chain
7. Provide O(log n) node lookup and acyclicity checking by replacing `find_node`'s linear scan and BFS acyclicity's quadratic traversal with balanced-map-backed implementations
8. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needs well-founded induction on n/10 through nat_to_string_go)
9. Prove `parse_json_go` fuel sufficiency (needs mutual induction scheme for parse_json_go/parse_array_elems/parse_object_kvs)
10. Prove `render_parse_json_roundtrip` for `JNum` and `JNeg` (blocked on item 8)
11. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (blocked on item 9)
12. Prove `TraceGraph` JSON render/parse roundtrip
13. Prove `AssuranceDelta` JSON render/parse roundtrip
14. Prove `ProductLineCase` JSON render/parse roundtrip
15. Prove `compose_well_formed` and related theorems for `compose_cases_guarded`, not just `compose_cases`
16. Prove delta composition for the general case where both deltas may contain `RemoveNode` and overlapping link changes, or prove a tight characterization of when composition fails
17. Prove `project_variant` preserves `WellFormed` when the family-wide `ProductLineCase` is well-formed and the variant is valid under the feature model
18. Prove `compile_document` produces a structurally valid assurance case for any well-formed `ConopsDocument`
19. Connect a real VST `semax_body` proof through the DeepSpec bridge as `ProofTerm` evidence with a complete `WellFormed` + `SupportTree` witness
20. Promote `VSTBridge.v` and `ITreeBridge.v` from thin stubs to full modules that carry end-to-end `WellFormed` + `SupportTree` witnesses, eliminating the split between the main build and the `deepspec/` directory
21. Formally verify the OCaml SHA-256 and HMAC-SHA256 implementation against FIPS 180-4, or replace it with a binding to a verified library
22. Prove that the extraction directives (`Extract Inductive nat => "int"`, etc.) preserve Rocq-side semantics for all values within OCaml's native integer range
