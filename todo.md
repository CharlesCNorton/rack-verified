# RACK TODO

1. Prove `avl_insert_find_other`: inserting does not disturb lookups for other keys
2. Prove `avl_insert` preserves `AVL_balanced`
3. Prove `avl_elements_sorted`: in-order traversal of an `AVL_ordered` tree is sorted
4. Prove `avl_insert_find_via_elements`: connect `avl_find` to the element list for the full refinement chain
5. Provide O(log n) node lookup and acyclicity checking by replacing `find_node`'s linear scan and BFS acyclicity's quadratic traversal with balanced-map-backed implementations
6. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needs well-founded induction on n/10 through nat_to_string_go)
7. Prove `parse_json_go` fuel sufficiency (needs mutual induction scheme for parse_json_go/parse_array_elems/parse_object_kvs)
8. Prove `render_parse_json_roundtrip` for `JNum` and `JNeg` (blocked on item 6)
9. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (blocked on item 7)
10. Prove `TraceGraph` JSON render/parse roundtrip
11. Prove `AssuranceDelta` JSON render/parse roundtrip
12. Prove `ProductLineCase` JSON render/parse roundtrip
13. Prove `compose_well_formed` and related theorems for `compose_cases_guarded`, not just `compose_cases`
14. Prove delta composition for the general case where both deltas may contain `RemoveNode` and overlapping link changes, or prove a tight characterization of when composition fails
15. Prove `project_variant` preserves `WellFormed` when the family-wide `ProductLineCase` is well-formed and the variant is valid under the feature model
16. Prove `compile_document` produces a structurally valid assurance case for any well-formed `ConopsDocument`
17. Connect a real VST `semax_body` proof through the DeepSpec bridge as `ProofTerm` evidence with a complete `WellFormed` + `SupportTree` witness
18. Promote `VSTBridge.v` and `ITreeBridge.v` from thin stubs to full modules that carry end-to-end `WellFormed` + `SupportTree` witnesses, eliminating the split between the main build and the `deepspec/` directory
19. Formally verify the OCaml SHA-256 and HMAC-SHA256 implementation against FIPS 180-4, or replace it with a binding to a verified library
20. Prove that the extraction directives (`Extract Inductive nat => "int"`, etc.) preserve Rocq-side semantics for all values within OCaml's native integer range
