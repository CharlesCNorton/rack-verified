# RACK TODO

## Sub-system assurance

1. Prove `project_variant` preserves `WellFormed` when the family-wide `ProductLineCase` is well-formed and the variant is valid under the feature model
2. Connect a real VST `semax_body` proof through the DeepSpec bridge as `ProofTerm` evidence with a complete `WellFormed` + `SupportTree` witness
3. Add `WellFormed` + `SupportTree` witnesses to deepspec/ files (VSTBridge cases use `prove_well_formed_auto`; requires `make deepspec` with VST/CompCert/ITree Docker image)

## Nice to have

4. Prove `avl_insert` preserves `AVL_balanced`
5. Prove `avl_elements_sorted`: in-order traversal of an `AVL_ordered` tree is sorted
6. Provide O(log n) node lookup and acyclicity checking by replacing `find_node`'s linear scan and BFS acyclicity's quadratic traversal with balanced-map-backed implementations
7. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needs well-founded induction on n/10 through nat_to_string_go)
8. Prove `parse_json_go` fuel sufficiency (needs mutual induction scheme for parse_json_go/parse_array_elems/parse_object_kvs)
9. Prove `render_parse_json_roundtrip` for `JNum` and `JNeg` (blocked on item 7)
10. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (blocked on item 8)
11. Prove `TraceGraph` JSON render/parse roundtrip
12. Prove `AssuranceDelta` JSON render/parse roundtrip
13. Prove `ProductLineCase` JSON render/parse roundtrip
14. Prove `compose_well_formed` and related theorems for `compose_cases_guarded`, not just `compose_cases`
15. Prove delta composition for the general case where both deltas may contain `RemoveNode` and overlapping link changes, or prove a tight characterization of when composition fails
16. Prove that the extraction directives (`Extract Inductive nat => "int"`, etc.) preserve Rocq-side semantics for all values within OCaml's native integer range
