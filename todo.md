# RACK TODO

1. Prove `topo_sort` completeness: `acyclic_has_zero_indeg` in `Core.v` needs the predecessor-chain → cycle argument; `topo_sort_complete` follows
2. Prove JSON parser round-trip correctness: `render_parse_json_roundtrip` in `Export.v` needs escape/unescape inverse lemma + fuel sufficiency
3. Prove AVL ordering + balance invariant preservation: `avl_balance_elements` is proved; full `avl_insert_preserves_ordered` and `avl_insert_preserves_balanced` require `String.compare` transitivity proof
4. Split `Export.v` into separate files: JSON AST/renderer, DOT renderer, SACM renderer, signed blobs, streaming; section boundaries are marked
