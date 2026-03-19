# RACK Rebuild TODO

Re-add features from the broken HEAD onto the known-good base (9168543).
Each item is applied, compiled, and committed individually.

1. ExportUtil.v: `rebuild_claims` preservation proofs (`rebuild_claims_structural_checks` etc.)
2. Incremental.v: AVL structural correctness (`avl_elements_sorted`, `avl_insert_find_via_elements`, rotation proofs)
3. Serialize.v: new file — JSON serialization for traces, deltas, product-line cases, metadata key constants
4. TopoSort.v: `topo_sort_valid` — Kahn's produces valid topo order (includes `index_of` helpers, `topo_sort_go_ordered`)
5. Reflect.v: `prove_well_formed_full` tactic, `prove_evidence_valid_robust` tactic (fix `index_of_Some_In` dependency)
6. Example.v + CaseStudy.v: replace verbose WF proofs with `prove_well_formed_full`
7. `agent/rack_agent.py` — Claude CLI wrapper with output sanitizer
8. `agent/rack_driver.py` — CBMC/Kani/SAW/Alloy evidence driver
9. `agent/rack_review.py` — PR review bot
10. `agent/rack_prompt.txt` — RACK domain system prompt
11. `agent/schema.md` — JSON schema documentation
12. `.github/workflows/rack-review.yml` — CI: build + zero-Abort gate + review bot
13. `.github/workflows/build.yml` — add GitHub Pages deployment for coqdoc
14. `todo.md` — update with remaining open problems
15. Prove `render_parse_json_string` (needs parse_string_chars fuel monotonicity)
16. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (mutual induction)
17. Prove `avl_insert_find`/`avl_insert_find_other` structurally (~300 lines rotation cases)
18. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needed for full JSON roundtrip)
