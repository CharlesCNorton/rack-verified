# RACK TODO

Ordered from least to most difficult.

1. Prove the escape/unescape inverse lemma for JSON string escaping (`escape_json_chars` / `parse_string_chars` roundtrip)
2. Prove `render_parse_json_roundtrip` using the escape inverse lemma plus fuel sufficiency for the parser
3. Prove `check_acyclic` (BFS) is complete, not just sound — currently only `check_acyclic_sound` exists
4. Prove `diagnose_structural` completeness without the topo-order premise — `diagnose_structural_complete` currently requires `verify_topo_order ac (topo_sort ac) = true` as a hypothesis
5. Prove `compose_well_formed` without requiring user-supplied acyclicity/discharged/entailment — derive them from component well-formedness plus disjointness
6. Prove `family_wide` for `WellFormed` under monotone annotations — `lift_preserves_wf` only covers the trivial `FETrue` case
7. Prove `avl_insert_preserves_balanced` (AVL balance invariant preservation) — rotation lemmas (`avl_balance_balanced`, `avl_balance_height`) are proved; remaining gap is `Nat.max` monotonicity under insert, blocked by `lia` not handling `Nat.max`
