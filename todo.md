# RACK TODO

1. Prove `avl_insert` preserves `AVL_balanced`
2. Prove `avl_elements_sorted`: in-order traversal of an `AVL_ordered` tree is sorted
3. Provide O(log n) node lookup and acyclicity checking by replacing `find_node`'s linear scan and BFS acyclicity's quadratic traversal with balanced-map-backed implementations
4. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needs well-founded induction on n/10 through nat_to_string_go)
5. Prove `parse_json_go` fuel sufficiency (needs mutual induction scheme for parse_json_go/parse_array_elems/parse_object_kvs)
6. Prove `render_parse_json_roundtrip` for `JNum` and `JNeg` (blocked on item 4)
7. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (blocked on item 5)
8. Prove `TraceGraph` JSON render/parse roundtrip
9. Prove `AssuranceDelta` JSON render/parse roundtrip
10. Prove `ProductLineCase` JSON render/parse roundtrip
11. Prove `compose_well_formed` and related theorems for `compose_cases_guarded`, not just `compose_cases`
12. Prove delta composition for the general case where both deltas may contain `RemoveNode` and overlapping link changes, or prove a tight characterization of when composition fails
13. Prove `project_variant` preserves `WellFormed` when the family-wide `ProductLineCase` is well-formed and the variant is valid under the feature model
14. Prove `compile_document` produces a structurally valid assurance case for any well-formed `ConopsDocument`
15. Connect a real VST `semax_body` proof through the DeepSpec bridge as `ProofTerm` evidence with a complete `WellFormed` + `SupportTree` witness
16. Promote `VSTBridge.v` and `ITreeBridge.v` from thin stubs to full modules that carry end-to-end `WellFormed` + `SupportTree` witnesses, eliminating the split between the main build and the `deepspec/` directory
17. Formally verify the OCaml SHA-256 and HMAC-SHA256 implementation against FIPS 180-4, or replace it with a binding to a verified library
18. Prove that the extraction directives (`Extract Inductive nat => "int"`, etc.) preserve Rocq-side semantics for all values within OCaml's native integer range
