# RACK TODO

Items ordered by logical dependency (earlier items unblock later ones).

1. Add `Decidable` instance for `NodeKind` and `LinkKind` using the existing `_eqb` lemmas so `decide equality` works
2. Prove `MetadataValue_eqb_eq` correctness lemma analogous to `NodeKind_eqb_eq`
3. Prove `TraceLinkKind_eqb` correctness lemma
4. Replace Peano `nat` with `Z` or `N` for all arithmetic in hot paths (`nat_to_string`, `index_of`, `sb_in_degree`, `reachable_set_fuel`) so extracted OCaml uses native integers
5. Add `rack.mli` filtering to hide internal Peano/positive/N types behind an opaque `int`-based API
6. Prove `String.compare` transitivity so AVL proofs can be completed
7. Prove `avl_insert_preserves_balanced` (AVL balance invariant preservation) using the transitivity result
8. Complete `topo_sort_complete`: assemble `acyclic_has_zero_indeg`, `topo_sort_go_remaining`, `topo_sort_go_nodup` into `length (topo_sort ac) = length ac.(ac_nodes)`
9. Prove `check_acyclic` (BFS) is complete, not just sound — currently only `check_acyclic_sound` exists
10. Prove `diagnose_structural` completeness without the topo-order premise — `diagnose_structural_complete` currently requires `verify_topo_order ac (topo_sort ac) = true` as a hypothesis
11. Prove the escape/unescape inverse lemma for JSON string escaping (`escape_json_chars` / `parse_string_chars` roundtrip)
12. Prove `render_parse_json_roundtrip` using the escape inverse lemma plus fuel sufficiency for the parser
13. Prove `check_well_formed` and `structural_checks` agree for all inputs, not just the concrete `Example` computations
14. Add `well_typed_defeater_links` to the `WellFormed` record or prove it follows from `check_context_links`
15. Prove `check_defeaters` soundness (implies all defeaters are resolved propositionally)
16. Prove `hydrate_evidence` preserves node count, IDs, kinds, and graph structure
17. Prove `auto_hydrate` preserves node IDs and graph structure (nodes, links, top unchanged)
18. Prove `rebuild_claims` preserves node IDs, kinds, evidence, and metadata
19. Prove `check_all_fresh` completeness (the reverse of `check_all_fresh_correct`)
20. Prove `check_class_trust` soundness (implies the propositional `Admissible` class-trust conjunct)
21. Prove `registries_consistent` is reflexive
22. Prove `compose_well_formed` without requiring user-supplied acyclicity/discharged/entailment — derive them from component well-formedness plus disjointness
23. Prove `delta_preserves_subtree` generically — currently only proved for the concrete `cs_delta` by enumeration
24. Prove `PRAdmissible` soundness: `check_pr_admissible = true` plus entailment/evidence obligations implies `PRAdmissible`
25. Prove `project_preserves_no_dangling` from `annotations_compatible` — currently only a boolean checker exists with no link to the propositional predicate
26. Prove `family_wide` for `WellFormed` under monotone annotations — `lift_preserves_wf` only covers the trivial `FETrue` case
27. Prove `check_trace_complete` soundness (boolean trace completeness implies the propositional coverage property)
28. Add `WellTraced` builder from boolean checks analogous to `build_well_formed`
29. Add negative property tests for traceability (mutated trace graphs fail `check_trace_total`)
30. Replace `rack_bridge.ml` shell-out stubs with actual output parsing and error handling; add at least one integration test per tool
31. Add CONOPS-to-Rocq bridge: define a `ConopsDocument` record (sections, requirements, rationale, assumptions, constraints, operational scenarios), a compiler from CONOPS elements to RACK Goal/Strategy/Assumption/Context nodes + `TL_Satisfies` trace links, and a preservation proof that every CONOPS requirement produces a reachable Goal node with a matching trace link
32. Add an end-to-end example exercising the CONOPS bridge: a miniature CONOPS document compiled to an `AssuranceCase`, evidence attached via `hydrate_evidence`, `WellFormed` proved, and `WellTraced` established through the generated trace links
33. Add the `rack_sacm_validate.ml` checks to CI (currently built but not run)
34. Split `Core.v` — at ~1700 lines it mixes type definitions, graph operations, well-formedness, topo-sort, diagnostics, and validator registries
35. Split `Export.v` into separate files: JSON AST/renderer, DOT renderer, SACM renderer, signed blobs, streaming; section boundaries are marked
