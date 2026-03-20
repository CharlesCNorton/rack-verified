# RACK TODO

1. Prove `parse_json_go` fuel sufficiency: `string_length s` always provides enough fuel for any valid JSON string `s`
2. Prove `nat_to_string`/`parse_nat_chars` roundtrip
3. Prove `parse_string_chars` fuel monotonicity
4. Prove `render_parse_json_roundtrip` for `JStr` by integrating `escape_unescape_roundtrip` with the `parse_json_go` wrapper using fuel monotonicity
5. Prove `render_parse_json_roundtrip` for `JNum` and `JNeg` using the nat roundtrip
6. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` by mutual induction over the sub-value roundtrips
7. Prove `TraceGraph` JSON render/parse roundtrip
8. Prove `AssuranceDelta` JSON render/parse roundtrip
9. Prove `ProductLineCase` JSON render/parse roundtrip
10. Prove `avl_insert_find`: inserting then finding with the same key returns the inserted value
11. Prove `avl_insert_find_other`: inserting does not disturb lookups for other keys
12. Prove `avl_insert` preserves `AVL_balanced`
13. Prove `avl_elements_sorted`: in-order traversal of an `AVL_ordered` tree is sorted
14. Prove `avl_insert_find_via_elements`: connect `avl_find` to the element list for the full refinement chain
15. Prove `compose_well_formed` and related theorems for `compose_cases_guarded`, not just `compose_cases`
16. Prove `project_variant` preserves `WellFormed` when the family-wide `ProductLineCase` is well-formed and the variant is valid under the feature model
17. Prove `compile_document` produces a structurally valid assurance case for any well-formed `ConopsDocument`
18. Prove delta composition for the general case where both deltas may contain `RemoveNode` and overlapping link changes, or prove a tight characterization of when composition fails
19. Connect a real VST `semax_body` proof through the DeepSpec bridge as `ProofTerm` evidence with a complete `WellFormed` + `SupportTree` witness
20. Formally verify the OCaml SHA-256 and HMAC-SHA256 implementation against FIPS 180-4, or replace it with a binding to a verified library
21. Prove that the extraction directives (`Extract Inductive nat => "int"`, etc.) preserve Rocq-side semantics for all values within OCaml's native integer range
