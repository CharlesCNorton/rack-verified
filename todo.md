# RACK Rebuild TODO

Re-add features from the broken HEAD onto the known-good base (9168543).
Each item is applied, compiled, and committed individually.

1. `.github/workflows/rack-review.yml` — CI: build + zero-Abort gate + review bot
2. `.github/workflows/build.yml` — add GitHub Pages deployment for coqdoc
3. `todo.md` — update with remaining open problems
4. Prove `render_parse_json_string` (needs parse_string_chars fuel monotonicity)
5. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (mutual induction)
6. Prove `avl_insert_find`/`avl_insert_find_other` structurally (~300 lines rotation cases)
7. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needed for full JSON roundtrip)
8. ExportUtil.v: `rebuild_claims` preservation proofs (`rebuild_claims_structural_checks` etc.)
9. Incremental.v: AVL structural correctness (`avl_elements_sorted`, `avl_insert_find_via_elements`, rotation proofs)
10. Example.v + CaseStudy.v: replace verbose WF proofs with `prove_well_formed_full`
