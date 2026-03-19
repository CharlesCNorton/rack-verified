# RACK Rebuild TODO

Re-add features from the broken HEAD onto the known-good base (9168543).
Each item is applied, compiled, and committed individually.

1. Delta.v: `apply_delta_compose_from_hyps`, `apply_delta_compose_add_only`
2. ProductLine.v: `family_wide_wf_from_structural`, `family_wide_wf_check`
3. Bridge.v: `import_preserves_top/links/no_dangling`, `import_preserves_wf`, `import_no_dangling`
4. Json.v: `json_depth`, literal roundtrips, `render_parse_json_str_roundtrip`
5. ExportUtil.v: `rebuild_claims` preservation proofs (`rebuild_claims_structural_checks` etc.)
6. Incremental.v: AVL structural correctness (`avl_elements_sorted`, `avl_insert_find_via_elements`, rotation proofs)
7. Serialize.v: new file — JSON serialization for traces, deltas, product-line cases, metadata key constants
8. TopoSort.v: `topo_sort_valid` — Kahn's produces valid topo order (includes `index_of` helpers, `topo_sort_go_ordered`)
9. Reflect.v: `prove_well_formed_full` tactic, `prove_evidence_valid_robust` tactic (fix `index_of_Some_In` dependency)
10. Example.v + CaseStudy.v: replace verbose WF proofs with `prove_well_formed_full`
11. `agent/rack_agent.py` — Claude CLI wrapper with output sanitizer
12. `agent/rack_driver.py` — CBMC/Kani/SAW/Alloy evidence driver
13. `agent/rack_review.py` — PR review bot
14. `agent/rack_prompt.txt` — RACK domain system prompt
15. `agent/schema.md` — JSON schema documentation
16. `.github/workflows/rack-review.yml` — CI: build + zero-Abort gate + review bot
17. `.github/workflows/build.yml` — add GitHub Pages deployment for coqdoc
18. `todo.md` — update with remaining open problems
19. Prove `nat_to_string`/`parse_nat_chars` roundtrip (needed for full JSON roundtrip)
20. Prove `render_parse_json_roundtrip` for `JArr`/`JObj` (mutual induction)
21. Prove `avl_insert_find`/`avl_insert_find_other` structurally (~300 lines rotation cases)
