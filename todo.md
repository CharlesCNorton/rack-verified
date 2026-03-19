# RACK Rebuild TODO

Re-add features from the broken HEAD onto the known-good base (9168543).
Each item is applied, compiled, and committed individually.

1. Serialize.v: new file — JSON serialization for traces, deltas, product-line cases, metadata key constants
2. TopoSort.v: `topo_sort_valid` — Kahn's produces valid topo order (includes `index_of` helpers, `topo_sort_go_ordered`)
3. Reflect.v: `prove_well_formed_full` tactic, `prove_evidence_valid_robust` tactic (fix `index_of_Some_In` dependency)
4. Example.v + CaseStudy.v: replace verbose WF proofs with `prove_well_formed_full`
5. `agent/rack_agent.py` — Claude CLI wrapper with output sanitizer
6. `agent/rack_driver.py` — CBMC/Kani/SAW/Alloy evidence driver
7. `agent/rack_review.py` — PR review bot
8. `agent/rack_prompt.txt` — RACK domain system prompt
9. `agent/schema.md` — JSON schema documentation
10. `.github/workflows/rack-review.yml` — CI: build + zero-Abort gate + review bot
11. `.github/workflows/build.yml` — add GitHub Pages deployment for coqdoc
12. `todo.md` — update with remaining open problems
13. Prove `render_parse_json_string` (needs parse_string_chars fuel monotonicity)
14. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (mutual induction)
15. Prove `avl_insert_find`/`avl_insert_find_other` structurally (~300 lines rotation cases)
16. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needed for full JSON roundtrip)
17. ExportUtil.v: `rebuild_claims` preservation proofs (`rebuild_claims_structural_checks` etc.)
18. Incremental.v: AVL structural correctness (`avl_elements_sorted`, `avl_insert_find_via_elements`, rotation proofs)
