# RACK Rebuild TODO

Re-add features from the broken HEAD onto the known-good base (9168543).
Each item is applied, compiled, and committed individually.

1. Reflect.v: `prove_well_formed_full` tactic, `prove_evidence_valid_robust` tactic (fix `index_of_Some_In` dependency)
2. Example.v + CaseStudy.v: replace verbose WF proofs with `prove_well_formed_full`
3. `agent/rack_agent.py` — Claude CLI wrapper with output sanitizer
4. `agent/rack_driver.py` — CBMC/Kani/SAW/Alloy evidence driver
5. `agent/rack_review.py` — PR review bot
6. `agent/rack_prompt.txt` — RACK domain system prompt
7. `agent/schema.md` — JSON schema documentation
8. `.github/workflows/rack-review.yml` — CI: build + zero-Abort gate + review bot
9. `.github/workflows/build.yml` — add GitHub Pages deployment for coqdoc
10. `todo.md` — update with remaining open problems
11. Prove `render_parse_json_string` (needs parse_string_chars fuel monotonicity)
12. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (mutual induction)
13. Prove `avl_insert_find`/`avl_insert_find_other` structurally (~300 lines rotation cases)
14. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needed for full JSON roundtrip)
15. ExportUtil.v: `rebuild_claims` preservation proofs (`rebuild_claims_structural_checks` etc.)
16. Incremental.v: AVL structural correctness (`avl_elements_sorted`, `avl_insert_find_via_elements`, rotation proofs)
