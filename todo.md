# RACK Rebuild TODO

Re-add features from the broken HEAD onto the known-good base (9168543).
Each item is applied, compiled, and committed individually.

1. `agent/rack_agent.py` — Claude CLI wrapper with output sanitizer
2. `agent/rack_driver.py` — CBMC/Kani/SAW/Alloy evidence driver
3. `agent/rack_review.py` — PR review bot
4. `agent/rack_prompt.txt` — RACK domain system prompt
5. `agent/schema.md` — JSON schema documentation
6. `.github/workflows/rack-review.yml` — CI: build + zero-Abort gate + review bot
7. `.github/workflows/build.yml` — add GitHub Pages deployment for coqdoc
8. `todo.md` — update with remaining open problems
9. Prove `render_parse_json_string` (needs parse_string_chars fuel monotonicity)
10. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (mutual induction)
11. Prove `avl_insert_find`/`avl_insert_find_other` structurally (~300 lines rotation cases)
12. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needed for full JSON roundtrip)
13. ExportUtil.v: `rebuild_claims` preservation proofs (`rebuild_claims_structural_checks` etc.)
14. Incremental.v: AVL structural correctness (`avl_elements_sorted`, `avl_insert_find_via_elements`, rotation proofs)
15. Example.v + CaseStudy.v: replace verbose WF proofs with `prove_well_formed_full`
