# RACK TODO

1. Split `Export.v` into separate files: JSON AST/renderer, DOT renderer, SACM renderer, signed blobs, BST index, streaming
2. Replace the unbalanced `NodeBST` with an AVL or red-black tree, prove `BST_ordered` holds for `build_bst_index` using `String.compare` transitivity, and carry the balancing invariant
3. Ground `pi_type_hash` to the actual `Prop` at construction time via an `Ltac` that computes a canonical hash from the type and refuses mismatches, so `mk_proof_identity` cannot be called with a stale hash
4. Address `node_claim : Prop` scalability — consider an indexed or defunctionalized claim representation to avoid proof-term bloat in large cases
5. Extend entailment automation beyond `vm_compute; tauto` — add hint databases, custom `Ltac2`, or a reflection-based partial decision procedure for common entailment shapes
6. Prove general delta composition under an explicit conflict-freedom precondition covering the `RemoveNode` case that `apply_delta_compose` currently excludes
7. Prove JSON parser round-trip correctness formally (`parse_json (render_json (assurance_case_to_json ac)) = Some ...`)
8. Prove `check_support_tree` soundness directly: `check_support_tree ac id = true -> SupportTree ac id`
9. Prove `topo_sort` completeness: when the graph is acyclic, `verify_topo_order ac (topo_sort ac) = true`
10. Prove `signed_blob_valid` connects to the real MAC
11. Add property-based OCaml tests for `Trace`, `Delta`, and `ProductLine` modules
12. Add mutation tests for trace invalidation (requirement change, commit change) and delta application
13. Wire `BenchmarkResult` to actual OCaml-side timing and emit results for `gen_benchmark_case` at multiple sizes
14. Implement real FFI call-outs in `Bridge.v` tool converters (Alloy, Verus, Kani, SAW) — at minimum a subprocess-calling OCaml shim
15. Validate `render_sacm` output against the OMG SACM 2.2 XSD schema
16. Generate and publish `coqdoc` (the Makefile target exists but isn't wired into CI artifacts)
