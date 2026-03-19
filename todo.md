# RACK Rebuild TODO

Re-add features from the broken HEAD onto the known-good base (9168543).
Each item is applied, compiled, and committed individually.

1. Example.v + CaseStudy.v: replace verbose WF proofs with `prove_well_formed_full`
2. `agent/rack_agent.py` — Claude CLI wrapper with output sanitizer
3. `agent/rack_driver.py` — CBMC/Kani/SAW/Alloy evidence driver
4. `agent/rack_review.py` — PR review bot
5. `agent/rack_prompt.txt` — RACK domain system prompt
6. `agent/schema.md` — JSON schema documentation
7. `.github/workflows/rack-review.yml` — CI: build + zero-Abort gate + review bot
8. `.github/workflows/build.yml` — add GitHub Pages deployment for coqdoc
9. `todo.md` — update with remaining open problems
10. Prove `render_parse_json_string` (needs parse_string_chars fuel monotonicity)
11. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (mutual induction)
12. Prove `avl_insert_find`/`avl_insert_find_other` structurally (~300 lines rotation cases)
13. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needed for full JSON roundtrip)
14. ExportUtil.v: `rebuild_claims` preservation proofs (`rebuild_claims_structural_checks` etc.)
15. Incremental.v: AVL structural correctness (`avl_elements_sorted`, `avl_insert_find_via_elements`, rotation proofs)
