# RACK TODO

1. Add `.lia.cache` to `.gitignore`
2. Add a `LICENSE` file (headers say MIT but no license file exists)
3. Stop tracking extraction artifacts (`rack.ml`, `rack.mli`) — they're in `.gitignore` but present in the tree
4. Split `Export.v` into separate files: JSON AST/renderer, DOT renderer, SACM renderer, signed blobs, BST index, streaming
5. Add Makefile targets for `test_rack_prop` and ensure `rack_cli` build uses `rack_util.ml`
6. Add `.vos`/`.vok` incremental build targets to the Makefile
7. Add a `Defeater` link kind to `Core.v` with formal semantics: a defeater on a Goal blocks `SupportTree` derivation unless the defeater is itself rebutted, and the checker flags unresolved defeaters via `ErrUnresolvedDefeater`
8. Add an explicit `Undeveloped` marker on nodes with a predicate `all_developed ac`, a diagnostic `ErrUndeveloped`, and make `check_discharged` skip undeveloped branches so partial cases can be checked without false positives
9. Add a lifecycle status field to Assumption nodes (`AssumedValid | Challenged | Invalidated`) with checker rules that block the support tree on reachable `Invalidated` assumptions and emit `ErrInvalidatedAssumption`
10. Add a shared structured `Counterexample` type (tool, property, witness, timestamp) to replace the `option string` counterexample fields in the Alloy, Kani, and SAW bridges
11. Replace the unbalanced `NodeBST` with an AVL or red-black tree, prove `BST_ordered` holds for `build_bst_index` using `String.compare` transitivity, and carry the balancing invariant
12. Generalize `variants_affected_by_feature` to recurse into `FEAnd`/`FEOr`/`FENot`, computing the full set of features mentioned in any `FeatureExpr`
13. Wire `ad_trace_changes` into `apply_delta` to produce an updated `TraceGraph`
14. Add `trace_reverse_lookup` computing the backward closure from an evidence node to requirements and prove it consistent with the forward `invalidate_requirement` computation
15. Add `trace_coverage` computing the fraction of requirements with complete evidence chains (Satisfies -> VerifiedBy -> ProducedBy) and a `check_trace_complete` that verifies full-chain coverage
16. Replace `String.eqb s blob` certificate validators with HMAC-SHA256 via OCaml FFI after extraction
17. Replace `FNV-1a` in `rack_util.ml` with a real cryptographic MAC
18. Ground `pi_type_hash` to the actual `Prop` at construction time via an `Ltac` that computes a canonical hash from the type and refuses mismatches, so `mk_proof_identity` cannot be called with a stale hash
19. Address `node_claim : Prop` scalability — consider an indexed or defunctionalized claim representation to avoid proof-term bloat in large cases
20. Extend entailment automation beyond `vm_compute; tauto` — add hint databases, custom `Ltac2`, or a reflection-based partial decision procedure for common entailment shapes
21. Add a `family_entailment` predicate to `ProductLine.v` and prove that `project_variant` preserves entailment when annotated nodes share compatible feature expressions
22. Prove `check_acyclic` (BFS) soundness formally
23. Prove general delta composition under an explicit conflict-freedom precondition covering the `RemoveNode` case that `apply_delta_compose` currently excludes
24. Prove JSON parser round-trip correctness formally (`parse_json (render_json (assurance_case_to_json ac)) = Some ...`)
25. Prove `diagnose_structural ac = [] <-> structural_checks ac = true` (completeness direction — soundness is in `Reflect.v` but completeness is only a comment)
26. Prove `check_support_tree` soundness directly: `check_support_tree ac id = true -> SupportTree ac id`
27. Add a `check_trace_fresh` boolean checker for `trace_fresh` and prove its soundness lemma
28. Prove `topo_sort` completeness: when the graph is acyclic, `verify_topo_order ac (topo_sort ac) = true`
29. Prove `check_annotations_compatible` soundness: boolean checker implies `annotations_compatible`
30. Prove `signed_blob_valid` connects to the real MAC
31. Add property-based OCaml tests for `Trace`, `Delta`, and `ProductLine` modules
32. Add mutation tests for trace invalidation (requirement change, commit change) and delta application
33. Wire `BenchmarkResult` to actual OCaml-side timing and emit results for `gen_benchmark_case` at multiple sizes
34. Implement real FFI call-outs in `Bridge.v` tool converters (Alloy, Verus, Kani, SAW) — at minimum a subprocess-calling OCaml shim
35. Validate `render_sacm` output against the OMG SACM 2.2 XSD schema
36. Generate and publish `coqdoc` (the Makefile target exists but isn't wired into CI artifacts)
