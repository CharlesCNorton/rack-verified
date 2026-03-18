# RACK TODO

Items ordered by logical dependency (earlier items unblock later ones).

1. Prove `check_acyclic` (BFS) is complete, not just sound — currently only `check_acyclic_sound` exists
2. Prove `diagnose_structural` completeness without the topo-order premise — `diagnose_structural_complete` currently requires `verify_topo_order ac (topo_sort ac) = true` as a hypothesis
3. Prove the escape/unescape inverse lemma for JSON string escaping (`escape_json_chars` / `parse_string_chars` roundtrip)
4. Prove `render_parse_json_roundtrip` using the escape inverse lemma plus fuel sufficiency for the parser
5. Prove `compose_well_formed` without requiring user-supplied acyclicity/discharged/entailment — derive them from component well-formedness plus disjointness
6. Prove `delta_preserves_subtree` generically — currently only proved for the concrete `cs_delta` by enumeration
7. Prove `PRAdmissible` soundness: `check_pr_admissible = true` plus entailment/evidence obligations implies `PRAdmissible`
8. Prove `project_preserves_no_dangling` from `annotations_compatible` — currently only a boolean checker exists with no link to the propositional predicate
9. Prove `family_wide` for `WellFormed` under monotone annotations — `lift_preserves_wf` only covers the trivial `FETrue` case
10. Prove `check_trace_complete` soundness (boolean trace completeness implies the propositional coverage property)
11. Add `WellTraced` builder from boolean checks analogous to `build_well_formed`
12. Add negative property tests for traceability (mutated trace graphs fail `check_trace_total`)
13. Replace `rack_bridge.ml` shell-out stubs with actual output parsing and error handling; add at least one integration test per tool
14. Add CONOPS-to-Rocq bridge: define a `ConopsDocument` record (sections, requirements, rationale, assumptions, constraints, operational scenarios), a compiler from CONOPS elements to RACK Goal/Strategy/Assumption/Context nodes + `TL_Satisfies` trace links, and a preservation proof that every CONOPS requirement produces a reachable Goal node with a matching trace link
15. Add an end-to-end example exercising the CONOPS bridge: a miniature CONOPS document compiled to an `AssuranceCase`, evidence attached via `hydrate_evidence`, `WellFormed` proved, and `WellTraced` established through the generated trace links
16. Add the `rack_sacm_validate.ml` checks to CI (currently built but not run)
17. Split `Core.v` — at ~1700 lines it mixes type definitions, graph operations, well-formedness, topo-sort, diagnostics, and validator registries
18. Split `Export.v` into separate files: JSON AST/renderer, DOT renderer, SACM renderer, signed blobs, streaming; section boundaries are marked
19. Prove `avl_insert_preserves_balanced` (AVL balance invariant preservation) — rotation lemmas (`avl_balance_balanced`, `avl_balance_height`) are proved; remaining gap is `Nat.max` monotonicity under insert, blocked by `lia` not handling `Nat.max`
