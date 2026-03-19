# RACK TODO

1. Prove `render_parse_json_string` (needs parse_string_chars fuel monotonicity)
2. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (mutual induction)
3. Prove `avl_insert_find`/`avl_insert_find_other` structurally (~300 lines rotation cases)
4. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needed for full JSON roundtrip)
5. ExportUtil.v: `rebuild_claims` preservation proofs (`rebuild_claims_structural_checks` etc.)
6. Incremental.v: AVL structural correctness (`avl_elements_sorted`, `avl_insert_find_via_elements`, rotation proofs)
7. Example.v + CaseStudy.v: replace verbose WF proofs with `prove_well_formed_full`
